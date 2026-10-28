#!/usr/bin/env python3
"""Controleur automatique de la variable de depot `CI_OVERFLOW_LOCAL`.

Volet 1 / **phase B** du debordement CI (#22937) : la phase A (#22921) a
pose la *forme hybride* des workflows -- une variable de depot unique decide
si un job part sur le parc local ou sur l'offre GitHub-hosted. La phase A est
**manuelle** (un operateur pose la variable) ; cette phase B la pilote.

Regle de decision (celle de l'arbitrage, pas une invention de l'organe) :

- offre hebergee **saturee** (jobs `ubuntu-latest` en file au-dela du seuil
  d'age) **et** parc local libre -> variable a `true` (le local absorbe le
  debordement) ;
- **charge rendue predite et bornee** -> variable a `false` : l'offre
  hebergee n'attend pas **et** le parc local ne porte presque rien (le
  nombre de slots occupes borne la charge qui revient avec la cohorte),
  confirmation sur une **seconde** lecture ;
- sinon -> **HOLD** (on ne touche a rien : une variable qui oscille est pire
  qu'une variable stable).

Garde de securite : si le **parc local est lui-meme affame** (des jobs
`coursia-linux` attendent), on ne bascule **pas** vers `true` -- on rend la
main a l'offre hebergee.

Le controleur est **fail-CLOSED** : une mesure illisible (API en erreur,
listing incomplet, inventaire des runners non lisible) ne produit **aucune**
ecriture -- un organe qui ne sait pas ne bascule pas.

PREREQUISIT (a installer par l'operateur, jamais suppose) : **deux jetons,
deux canaux, jamais le meme** :

- le jeton de **MESURE** (`GH_TOKEN`, ou `github.token` dans le workflow)
  sert a lire les files de jobs et l'inventaire des runners ;
- le jeton d'**ECRITURE** (`ACTIONS_VARIABLES_PAT`) sert **uniquement** a
  lire et a ecrire la variable de depot. Il porte le droit fin
  `Variables: read-write` sur `jsboige/CoursIA` seul (secret pose dans
  Actions le 2026-10-27T17:05:48Z, expiration 2027-01-25).

**Aucun repli.** Sans jeton d'ecriture, le controleur **rend son verdict et
n'ecrit rien** -- il ne se rabat jamais sur le jeton de mesure, qui n'a pas
le droit. Secret absent ou vide : le verdict est rendu, l'ecriture est
refusee, et le resume du job **nomme la cause**. C'est l'option (a) de
l'arbitrage user du 2026-10-27 (c.6441695482) : le chemin d'ecriture est
cable, un secret manquant degrade le mode, il ne le rend pas muet.

En local, l'operateur pose le jeton d'ecriture par commande :

    ACTIONS_VARIABLES_PAT=$(gh auth token --user jsboige) \
      python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply

Sans jeton de mesure, l'organe rend `REFUSED` et **n'ecrit rien**.

Jeton d'inventaire du parc : `github.token` ne porte PAS le droit de lire
`/actions/runners` (aucune portee de `permissions:` ne le donne). L'organe lit
donc l'inventaire avec le jeton dedie `RUNNERS_READ_PAT` (secret read-only
`Administration:read`, deja consomme par six workflows du depot -- cf
[`linux-runner-starvation-advisory.yml`]), et retombe sur le jeton courant
quand il est absent (operateur en local). Sans l'un ni l'autre, la mesure
locale est illisible, le verdict vaut `UNREADABLE` et la raison NOMME le jeton
manquant : jamais un `OK` par defaut. Option : `--runners-token-env`.

Usage :

    # lecture seule, verdict seul (defaut : dry-run)
    python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA

    # application effective (le jeton d'ecriture est obligatoire)
    ACTIONS_VARIABLES_PAT=... python scripts/ci/ci_overflow_controller.py \
        --repo jsboige/CoursIA --apply

**Lecture tronquee.** Un budget de lecture atteint rend les comptes de file
une **borne inferieure**. Une borne inferieure etablit une affirmation
POSITIVE (« au moins N jobs ages ») mais **n'etablit pas** une affirmation
NEGATIVE (« aucun job en file », « le parc n'est pas affame »). Le
controleur applique cette regle aux deux branches : la troncature de la
lecture **hebergee** interdit de conclure « file videe » (bascule vers
`false`), la troncature de la lecture **locale** interdit de conclure
« parc local non affame » (bascule vers `true`). Elle n'interdit jamais de
constater une saturation (affirmation positive) ni une affamescence locale
constatee. Mesure du 2026-10-27 sur la file reelle : lecture hebergee
complete (`budget_unread = 0`), lecture locale tronquee a 15 runs ages de
15 a 20 min -- donc au-dessus du seuil de 15 min, donc desertes par une
lecture complete : le « parc local non affame » n'etait PAS etabli.

Le cout de l'organe est borne : deux lectures de file, plafonnees par
`--job-budget` (defaut 120) et `--local-job-budget` (defaut 120) lectures de
jobs -- le volume d'appels API est justement l'objet du volet 5 de #22937, un
organe de controle ne doit pas en devenir la cause. Mesure du 2026-10-27 (file
reelle, compteur sur les deux points d'appel) : **313 appels `gh` par
passage**, dont 160 lectures de jobs et 143 requetes de re-verification du
residuel (chaque entree vue au seul listing `queued` coute une requete
`runs/{id}`). C'est ce chiffre qui fixe la cadence horaire du workflow, pas une
preference. Le budget local a ete aligne sur le budget hebergee (40 -> 120)
pour que la lecture locale soit **complete** dans le regime nominal : un
budget trop bas produit une troncature systematique, donc une lecture
locale toujours « non etablie », donc une bascule vers `true` impossible.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_runner_starvation as crs  # noqa: E402  (organe voisin, meme dossier)

EXIT_OK = 0
EXIT_UNREADABLE = 1
EXIT_REFUSED = 2

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_VARIABLE = "CI_OVERFLOW_LOCAL"
HOSTED_LABEL = "ubuntu-latest"
LOCAL_LABEL = "coursia-linux"

# Seuil de saturation : au-dela de ce nombre de jobs hebergees en file
# depuis plus de `--saturation-minutes`, l'offre hebergee est saturee.
DEFAULT_SATURATION_JOBS = 3
DEFAULT_SATURATION_MINUTES = 15.0
# Nombre de slots locaux libres minimum pour accepter le debordement.
DEFAULT_MIN_FREE_SLOTS = 2
# Dwell : minimum entre deux bascules (anti-oscillation).
# COHERENCE AVEC LA CADENCE (point Hermes du 2026-10-27, 12:53Z) : le dwell
# n'est opposable que s'il depasse l'ecart entre deux passages. Le cron est
# horaire ('31 * * * *') : deux passages consecutifs sont a 60 min. Un dwell de
# 30 min ne peut donc JAMAIS bloquer une bascule -- l'anti-oscillation etait
# inerte, un decor et non une protection. Regle appliquee : le dwell depasse
# la cadence (90 > 60).
DEFAULT_DWELL_MINUTES = 90.0
# Charge rendue maximum toleree a la liberation. La liberation rend la
# COHORTE a l'offre hebergee : le nombre de jobs que le parc local porte au
# moment de la liberation borne la charge qui revient. On ne libere donc que
# si le parc local ne porte presque rien (au plus ce nombre de slots
# occupes) -- la charge rendue est alors PREDITE et BORNEE, pas subie.
DEFAULT_MAX_RETURNED_JOBS = 2
# Pause entre les deux lectures de l'inventaire local qui confirment
# l'inaction du parc (une seule lecture peut tomber sur un instant vide).
DEFAULT_CONFIRM_SECONDS = 30.0
# Backlog DUR : au-dela de cet age, le plus ancien job heberge n'attend plus
# « un peu » -- il etouffe la file. La RE-ABSORPTION (offre -> local) n'est
# alors plus bloquee par le dwell : c'est la starvation qu'on a vecue, et
# attendre 90 min la prolonge. La LIBERATION n'echappe jamais au dwell.
DEFAULT_PANIC_MINUTES = 30.0


@dataclass
class HostedSample:
    """Etat de l'offre GitHub-hosted, mesure."""

    queued: int = 0
    old: int = 0
    oldest_age_min: float = 0.0
    complete: bool = True
    # True = la lecture a ete TRONQUEE (budget de lecture atteint) : les
    # comptes de file sont des bornes INFERIEURES.
    truncated: bool = False
    # Nombre de runs en cours non lus : la classe « en cours » n'entre dans
    # AUCUNE premisse du controleur (qui ne raisonne que sur la file), elle
    # est rapportee pour que le rapport dise ce qu'il ignore.
    in_progress_unread: int = 0
    reason: str = ""


@dataclass
class LocalSample:
    """Etat du parc local, mesure."""

    online: int = 0
    free: int = 0
    starved: int = 0
    complete: bool = True
    # True = la lecture d'affamescence a ete TRONQUEE : « le parc n'est pas
    # affame » n'est alors PAS etablie (borne inferieure).
    truncated: bool = False
    in_progress_unread: int = 0
    reason: str = ""
    # Occupation reelle du parc : slots en ligne et OCCUPES. C'est la borne
    # de la charge rendue a la liberation (le parc local porte ces jobs ;
    # ils reviennent a l'offre hebergee si on libere la cohorte).
    busy: int = 0
    # Slots en ligne dont l'occupation est INCONNUE (champ `busy` absent de
    # la reponse) : ils sont comptes comme occupes (fail-CLOSED), jamais
    # comme libres.
    unknown: int = 0

    @property
    def charge(self) -> int:
        """Charge que le parc local porte, borne superieure de la rendue."""
        return self.busy + self.unknown


@dataclass
class LoadConfirm:
    """Confirmation d'inaction du parc local (seconde lecture).

    La liberation exige que le parc local ne porte **presque rien** : le
    nombre de slots occupes borne la charge qui revient a l'offre hebergee.
    Une seule lecture peut tomber sur un instant vide (le parc vient de
    finir un lot) : la lecture est donc **confirmee** par une seconde
    lecture de l'inventaire, espacee de `--confirm-seconds`.
    """

    busy: int = 0
    unknown: int = 0
    complete: bool = True
    reason: str = ""

    @property
    def charge(self) -> int:
        return self.busy + self.unknown


@dataclass
class Decision:
    """Verdict du controleur."""

    action: str  # SWITCH_TRUE | SWITCH_FALSE | HOLD | UNREADABLE
    reason: str
    current: str | None = None
    target: str | None = None
    details: dict = field(default_factory=dict)


def evaluate(
    hosted: HostedSample,
    local: LocalSample,
    current: str | None,
    *,
    saturation_jobs: int = DEFAULT_SATURATION_JOBS,
    saturation_minutes: float = DEFAULT_SATURATION_MINUTES,
    min_free_slots: int = DEFAULT_MIN_FREE_SLOTS,
    dwell_minutes: float = DEFAULT_DWELL_MINUTES,
    max_returned_jobs: int = DEFAULT_MAX_RETURNED_JOBS,
    panic_minutes: float = DEFAULT_PANIC_MINUTES,
    local_confirm: LoadConfirm | None = None,
    last_change_at: datetime | None = None,
    now: datetime | None = None,
) -> Decision:
    """Decide de l'etat voulu de la variable. Fonction PURE (aucun appel).

    L'ordre des regles est significatif : la garde de securite (parc local
    affame) passe avant la saturation, sinon on enverrait du debordement vers
    un parc qui n'absorbe rien.
    """
    now = now or datetime.now(timezone.utc)

    if not hosted.complete or not local.complete:
        parts = []
        if not hosted.complete:
            parts.append(f"offre hebergee non mesuree ({hosted.reason})")
        if not local.complete:
            parts.append(f"parc local non mesure ({local.reason})")
        return Decision(
            action="UNREADABLE",
            reason=" ; ".join(parts) or "mesure incomplete",
            current=current,
            details={"hosted": hosted, "local": local},
        )

    def hold(reason: str, target: str | None = None) -> Decision:
        return Decision(
            action="HOLD",
            reason=reason,
            current=current,
            target=target,
            details={"hosted": hosted, "local": local},
        )

    def hard_backlog() -> bool:
        """Le backlog heberge est-il DUR (starvation etablie) ?

        PREMISSE POSITIVE : « le plus ancien job attend depuis plus de
        `panic_minutes` » est etablie par une lecture meme partielle.
        """
        return (
            hosted.old >= saturation_jobs
            and hosted.oldest_age_min >= panic_minutes
            and local.free >= min_free_slots
        )

    def switch(target: str, reason: str) -> Decision:
        if target == current:
            return hold(f"deja a {target} -- {reason}", target)
        if (
            dwell_minutes > 0
            and last_change_at is not None
            and (now - last_change_at).total_seconds() < dwell_minutes * 60
        ):
            minutes = (now - last_change_at).total_seconds() / 60.0
            # ECHAPPEMENT DU DWELL -- uniquement pour la RE-ABSORPTION
            # (offre hebergee -> parc local) et uniquement quand le backlog
            # heberge est DUR. La nuit du 27/10, la liberation a rendu la
            # cohorte a une offre qui s'etait ensuite etouffeee, et le
            # dwell de 90 min a interdit de revenir a `true` : la file a
            # starve pendant toute la fenetre. Attendre 90 min devant une
            # starvation etablie prolonge la panne.
            #
            # La LIBERATION n'echappe jamais : c'est elle qui fait revenir
            # la cohorte, donc c'est elle qui doit rester freinee.
            #
            # L'echappement ne peut pas creer d'oscillation : il exige un
            # backlog DUR (le plus ancien job attend depuis plus de
            # `panic_minutes`), ce qui est incompatible avec la premise de
            # liberation (« l'offre hebergee n'attend pas ») -- les deux ne
            # peuvent pas etre vraies a la meme lecture.
            if target == "true" and hard_backlog():
                return Decision(
                    action="SWITCH_TRUE",
                    reason=(
                        f"{reason} -- dwell de {dwell_minutes:.0f} min "
                        f"ignore : le plus ancien job heberge attend depuis "
                        f"{hosted.oldest_age_min:.0f} min (backlog dur, "
                        f"seuil {panic_minutes:.0f} min)"
                    ),
                    current=current,
                    target=target,
                    details={"hosted": hosted, "local": local},
                )
            return hold(
                f"bascule vers {target} differee par le dwell "
                f"({minutes:.1f} min < {dwell_minutes:.0f} min depuis la "
                f"derniere ecriture) -- {reason}",
                target,
            )
        return Decision(
            action="SWITCH_TRUE" if target == "true" else "SWITCH_FALSE",
            reason=reason,
            current=current,
            target=target,
            details={"hosted": hosted, "local": local},
        )

    # 1. Garde de securite : le parc local est lui-meme affame.
    #    PREMISSE POSITIVE (« au moins un job affame ») : une lecture
    #    partielle la CONFIRME, la troncature ne l'annule pas.
    if local.starved > 0:
        return switch(
            "false",
            f"le parc local est lui-meme affame ({local.starved} job(s) "
            f"coursia-linux en file) -- on rend la main a l'offre hebergee",
        )

    # 2. LIBERATION : la charge RENDUE doit etre PREDITE et BORNEE.
    #
    #    Ce que la liberation fait : elle rend la COHORTE a l'offre
    #    hebergee. La charge qui revient est donc celle que le parc local
    #    porte MAINTENANT. On ne libere donc que si le parc local ne porte
    #    presque rien : le nombre de slots occupes est la borne de la
    #    charge rendue.
    #
    #    Pourquoi la seule lecture « l'offre hebergee n'attend pas » ne
    #    suffit pas (reserve du coordinateur, 28/10) : pendant que la
    #    cohorte tourne en local, l'offre hebergee ne porte QUE les jobs
    #    hors debordement -- elle parait donc allegee, meme quand la charge
    #    de la cohorte est enorme. Liberer sur cette seule lecture rend
    #    la cohorte entiere a une offre qui s'etouffe derriere, et le dwell
    #    de 90 min interdit ensuite de revenir a `true` : on rejoue la
    #    nuit du 27/10.
    #
    #    Les conditions sont donc CUMULEES :
    #      a) l'offre hebergee n'attend pas (premise NEGATIVE : elle
    #         n'est etablie que par une lecture COMPLETE) ;
    #      b) le parc local ne porte presque rien -- `local.charge`
    #         (occupes + occupation inconnue) <= `--max-returned-jobs` ;
    #      c) aucun job local n'attend (`local.starved == 0`) ;
    #      d) la lecture est CONFIRMEE : une seconde lecture de
    #         l'inventaire, espacee de `--confirm-seconds`, doit porter la
    #         meme borne. Une seule lecture peut tomber sur un instant
    #         vide (le parc vient de finir un lot).
    #
    #    Toute condition non remplie est un HOLD qui NOMME celle qui
    #    manque : un operateur doit pouvoir lire pourquoi la liberation n'a
    #    pas eu lieu.
    release_blockers: list[str] = []
    if hosted.truncated:
        release_blockers.append(
            f"lecture hebergee TRONQUEE ({hosted.reason}) : « l'offre "
            f"hebergee n'attend pas » n'est pas etablie"
        )
    elif hosted.old != 0:
        release_blockers.append(
            f"l'offre hebergee attend encore ({hosted.old} job(s) de plus de "
            f"{saturation_minutes:.0f} min, plus ancien "
            f"{hosted.oldest_age_min:.0f} min)"
        )
    if local.starved > 0:
        release_blockers.append(
            f"{local.starved} job(s) coursia-linux attendent sur le parc local"
        )
    if local.charge > max_returned_jobs:
        release_blockers.append(
            f"le parc local porte {local.charge} job(s) (occupes "
            f"{local.busy} + occupation inconnue {local.unknown}) -- la "
            f"charge rendue depasse le seuil ({max_returned_jobs})"
        )
    if local_confirm is None:
        release_blockers.append(
            "la lecture de confirmation n'a pas ete faite : l'inaction du "
            "parc n'est pas etablie"
        )
    elif not local_confirm.complete:
        release_blockers.append(
            f"lecture de confirmation illisible ({local_confirm.reason})"
        )
    elif local_confirm.charge > max_returned_jobs:
        release_blockers.append(
            f"la lecture de confirmation porte {local_confirm.charge} job(s) "
            f"au lieu de {max_returned_jobs} ou moins : l'inaction du parc "
            f"n'est pas confirmee"
        )
    if not release_blockers:
        return switch(
            "false",
            f"la charge rendue est predite et bornee : le parc local ne "
            f"porte rien ({local.charge} job(s) confirme(s) a "
            f"{local_confirm.charge if local_confirm else '?'} sur la "
            f"seconde lecture) et l'offre hebergee n'attend pas -- la "
            f"cohorte revient a l'offre hebergee",
        )

    # 3. Offre hebergee saturee ET parc local libre : le local absorbe.
    #    « saturee » est une premisse POSITIVE (« au moins N jobs ages ») :
    #    la troncature de l'offre hebergee ne l'annule pas, elle ne fait que
    #    sous-compter. En revanche « le parc local n'est PAS affame » est
    #    une premisse NEGATIVE : sous troncature locale elle n'est pas
    #    etablie, et on n'envoie pas de debordement vers un parc dont on
    #    ignore l'occupation.
    if (
        hosted.old >= saturation_jobs
        and local.free >= min_free_slots
        and not local.truncated
    ):
        return switch(
            "true",
            f"offre hebergee saturee ({hosted.old} job(s) en file depuis plus "
            f"de {saturation_minutes:.0f} min, plus ancien {hosted.oldest_age_min:.0f} min) "
            f"et parc local libre ({local.free} slot(s)) -- le local absorbe",
        )

    notes = []
    if local.truncated:
        notes.append(
            f"lecture locale TRONQUEE ({local.reason}) : « le parc local "
            f"n'est pas affame » n'est pas etablie -> pas de debordement "
            f"vers le local"
        )
    return hold(
        f"conditions non reunies : {hosted.old} job(s) heberge(s) en file "
        f"au-dela de {saturation_minutes:.0f} min (seuil {saturation_jobs}), "
        f"{local.free} slot(s) local(aux) libre(s) (seuil {min_free_slots})"
        + (" ; " + " ; ".join(notes) if notes else "")
        + (
            " ; liberation bloquee : " + " ; ".join(release_blockers)
            if release_blockers
            else ""
        ),
        None,
    )


def _gh_api(
    args: list[str],
    token: str | None = None,
    method: str | None = None,
    payload: dict | None = None,
) -> tuple[int, str, str]:
    """Appelle `gh api` et rend (code retour, stdout, stderr)."""
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    argv = ["gh", "api", *args]
    if method:
        argv[1:1] = ["--method", method]
    stdin = None
    if payload is not None:
        stdin = json.dumps(payload)
        argv[1:1] = ["--input", "-"]
    proc = subprocess.run(
        argv,
        input=stdin,
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
        env=env,
    )
    return proc.returncode, proc.stdout, proc.stderr


def read_variable(
    repo: str, name: str, token: str
) -> tuple[str | None, datetime | None, str]:
    """Lit la variable de depot. Rend (valeur, updated_at, motif d'echec)."""
    rc, out, err = _gh_api(
        [f"repos/{repo}/actions/variables/{name}"], token=token
    )
    if rc != 0:
        message = (err or out or "").strip().splitlines()
        return None, None, message[-1] if message else "lecture impossible"
    try:
        data = json.loads(out)
    except json.JSONDecodeError:
        return None, None, "reponse non-JSON"
    value = data.get("value")
    updated = data.get("updated_at")
    parsed = None
    if isinstance(updated, str):
        try:
            parsed = datetime.fromisoformat(updated.replace("Z", "+00:00"))
        except ValueError:
            parsed = None
    return (value if isinstance(value, str) else None), parsed, ""


def write_variable(repo: str, name: str, value: str, token: str) -> tuple[bool, str]:
    """Ecrit la variable de depot. Rend (succes, motif)."""
    payload = {"name": name, "value": value}
    rc, out, err = _gh_api(
        [f"repos/{repo}/actions/variables/{name}"],
        token=token,
        method="PATCH",
        payload=payload,
    )
    if rc == 0:
        return True, "variable mise a jour"
    message = (err or out or "").strip()
    if "404" in message or "Not Found" in message:
        # La variable n'existe pas encore : on la cree.
        rc2, out2, err2 = _gh_api(
            [f"repos/{repo}/actions/variables"],
            token=token,
            method="POST",
            payload=payload,
        )
        if rc2 == 0:
            return True, "variable creee"
        return False, (err2 or out2 or "creation refusee").strip()
    return False, message or "ecriture refusee"


def collect_hosted(
    repo: str,
    saturation_minutes: float,
    job_budget: int,
    now: datetime,
    token: str | None,
) -> HostedSample:
    """Mesure l'offre hebergee : jobs `ubuntu-latest` en file."""
    if token:
        os.environ["GH_TOKEN"] = token
    starv = crs.fetch_starvation(
        repo,
        HOSTED_LABEL,
        starve_minutes=0.0,
        now=now,
        job_read_budget=job_budget,
    )
    if not starv.complete:
        return HostedSample(
            complete=False,
            reason=(
                f"lecture de la file hebergee incomplete "
                f"({len(starv.listing_failed)} listing(s) en echec, "
                f"{starv.stats.failed} appel(s) en echec)"
            ),
        )
    rows = [row for row in starv.starved if row.age_min is not None]
    old = [row for row in rows if row.age_min > saturation_minutes]
    oldest = max((row.age_min for row in rows), default=0.0)
    reason = ""
    if starv.truncated:
        reason = (
            f"{len(starv.budget_unread)} run(s) non lu(s) (budget de lecture "
            f"{job_budget} atteint) -- les comptes de file sont des bornes "
            f"INFERIEURES"
        )
    return HostedSample(
        queued=len(rows),
        old=len(old),
        oldest_age_min=oldest,
        complete=True,
        truncated=starv.truncated,
        in_progress_unread=starv.in_progress_unread,
        reason=reason,
    )


def collect_local(
    repo: str,
    saturation_minutes: float,
    job_budget: int,
    now: datetime,
    token: str | None,
    measure_starvation: bool = True,
    runners_token: str | None = None,
) -> LocalSample:
    """Mesure le parc local : slots libres, et affames si demande.

    L'inventaire (`/actions/runners`) exige un droit que `github.token` ne
    porte PAS : aucune portee de `permissions:` ne le donne (seul un jeton
    d'administration le porte). Il se lit donc avec le jeton dedie
    (`RUNNERS_READ_PAT`, secret read-only `Administration:read`, deja consomme
    par six workflows du depot), et retombe sur le jeton courant quand aucun
    jeton dedie n'est fourni -- le cas d'un operateur en local, dont le jeton
    a le droit.

    Sans jeton dedie ET sans droit, la mesure est ILLISIBLE et la raison le
    NOMME : le verdict reste `UNREADABLE`, jamais un `OK` par defaut.
    """
    if token:
        os.environ["GH_TOKEN"] = token
    inv = crs.fetch_inventory(repo, LOCAL_LABEL, runners_token or token)
    if not inv.available:
        reason = inv.reason or "inventaire des runners illisible"
        if not runners_token:
            reason = (
                "jeton d'inventaire des runners absent (RUNNERS_READ_PAT) et "
                f"jeton courant sans droit sur actions/runners -- {reason}"
            )
        return LocalSample(complete=False, reason=reason)
    starved = 0
    truncated = False
    in_progress_unread = 0
    reason = ""
    if measure_starvation:
        starv = crs.fetch_starvation(
            repo,
            LOCAL_LABEL,
            starve_minutes=saturation_minutes,
            now=now,
            job_read_budget=job_budget,
        )
        if not starv.complete:
            return LocalSample(
                online=len(inv.online),
                free=inv.free,
                busy=len(inv.busy),
                unknown=len(inv.unknown),
                complete=False,
                reason="lecture de la file locale incomplete",
            )
        starved = len(starv.starved)
        truncated = starv.truncated
        in_progress_unread = starv.in_progress_unread
        if truncated:
            reason = (
                f"{len(starv.budget_unread)} run(s) local(aux) non lu(s) "
                f"(budget de lecture {job_budget} atteint) -- « le parc local "
                f"n'est pas affame » n'est PAS etablie"
            )
    else:
        reason = "affamescence locale non mesuree (--no-local-starvation)"
    return LocalSample(
        online=len(inv.online),
        free=inv.free,
        starved=starved,
        complete=True,
        truncated=truncated,
        in_progress_unread=in_progress_unread,
        reason=reason,
        busy=len(inv.busy),
        unknown=len(inv.unknown),
    )


def confirm_local_idle(
    repo: str,
    token: str | None,
    runners_token: str | None = None,
    delay_seconds: float = DEFAULT_CONFIRM_SECONDS,
) -> LoadConfirm:
    """Seconde lecture de l'occupation du parc local (confirmation).

    La liberation rend la cohorte a l'offre hebergee : la charge qui revient
    est bornee par ce que le parc local porte. Une seule lecture peut
    tomber sur un instant vide (le parc vient de finir un lot) -- la lecture
    est donc confirmee par une **seconde** lecture de l'inventaire,
    espacee de `delay_seconds`.

    Cout : **un** appel d'inventaire (l'inventaire est un seul appel, contre
    ~295 pour la lecture des files). L'appel n'est fait que lorsque la
    liberation est autrement candidate (le parc parait inactif ET l'offre
    hebergee n'attend pas) -- c'est rare, donc la pause aussi.

    Echec de lecture : `complete=False` et la cause nommee -- la liberation
    est alors bloquee (fail-CLOSED).
    """
    if delay_seconds > 0:
        time.sleep(delay_seconds)
    inv = crs.fetch_inventory(repo, LOCAL_LABEL, runners_token or token)
    if not inv.available:
        return LoadConfirm(
            complete=False,
            reason=inv.reason or "inventaire des runners illisible",
        )
    return LoadConfirm(
        busy=len(inv.busy),
        unknown=len(inv.unknown),
        complete=True,
    )


def render_summary(report: dict, rc: int) -> str:
    """Rend le resume du job (markdown) a partir du rapport JSON.

    Le resume **nomme** les deux degrades : le jeton d'ecriture absent
    (rien n'a ete ecrit malgre un verdict) et l'etat de la variable
    illisible. Une ligne `DEGRADE:` par cause -- le workflow la greppe pour
    emettre une annotation, un lecteur la voit dans le resume.
    """
    thresholds = report.get("thresholds", {})
    hosted = report.get("hosted", {})
    local = report.get("local", {})
    lines = [
        "### CI overflow controller (phase B) -- VERDICT",
        "",
        f"- code retour : {rc}",
        f"- verdict : {report.get('verdict')}",
        f"- raison : {report.get('reason')}",
        f"- variable : {report.get('current')} -> {report.get('target')} "
        f"({'ECRIT' if report.get('written') else 'NON ECRIT'})",
        f"- hebergee : {hosted.get('queued')} job(s) en file, "
        f"{hosted.get('old')} de plus de "
        f"{thresholds.get('saturation_minutes', 0):.0f} min"
        + (" [LECTURE TRONQUEE]" if hosted.get("truncated") else ""),
        f"- local : {local.get('online')} slot(s) en ligne, "
        f"{local.get('free')} libre(s), {local.get('starved')} affame(s)"
        + (" [LECTURE TRONQUEE]" if local.get("truncated") else ""),
    ]
    degraded = [
        item for item in (report.get("write_blocked"), report.get("state_reason"))
        if item
    ]
    if degraded:
        lines.append("")
        lines.extend(f"DEGRADE: {item}" for item in degraded)
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pilote la variable de depot CI_OVERFLOW_LOCAL (phase B)."
    )
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--variable", default=DEFAULT_VARIABLE)
    parser.add_argument("--token-env", default="GH_TOKEN")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="ecrit la variable (defaut : dry-run, verdict seul)",
    )
    parser.add_argument("--saturation-jobs", type=int, default=DEFAULT_SATURATION_JOBS)
    parser.add_argument(
        "--saturation-minutes", type=float, default=DEFAULT_SATURATION_MINUTES
    )
    parser.add_argument("--min-free-slots", type=int, default=DEFAULT_MIN_FREE_SLOTS)
    parser.add_argument("--dwell-minutes", type=float, default=DEFAULT_DWELL_MINUTES)
    parser.add_argument(
        "--max-returned-jobs",
        type=int,
        default=DEFAULT_MAX_RETURNED_JOBS,
        help=(
            "charge rendue maximum toleree a la liberation : le parc local "
            "doit porter au plus ce nombre de slots occupes (occupation "
            "inconnue comprise) pour que la liberation soit predicts et "
            "bornee"
        ),
    )
    parser.add_argument(
        "--confirm-seconds",
        type=float,
        default=DEFAULT_CONFIRM_SECONDS,
        help=(
            "pause avant la seconde lecture de l'inventaire local qui "
            "confirme l'inaction du parc (la liberation n'a lieu que si les "
            "DEUX lectures portent une charge sous le seuil)"
        ),
    )
    parser.add_argument(
        "--panic-minutes",
        type=float,
        default=DEFAULT_PANIC_MINUTES,
        help=(
            "age du plus ancien job heberge au-dela duquel le backlog est "
            "considere DUR : la re-absorption (offre -> parc local) n'est "
            "alors plus differee par le dwell"
        ),
    )
    parser.add_argument(
        "--runners-token-env",
        default="RUNNERS_READ_PAT",
        metavar="VAR",
        help=(
            "variable d'environnement du jeton d'inventaire des runners "
            "(defaut RUNNERS_READ_PAT, secret read-only du depot ; vide = "
            "jeton courant, le cas d'un operateur en local)"
        ),
    )
    parser.add_argument("--job-budget", type=int, default=crs.DEFAULT_JOB_READ_BUDGET)
    # Budget local aligne sur le budget hebergee : un budget trop bas rend la
    # lecture locale TRONQUEE en permanence, donc « le parc local n'est pas
    # affame » jamais etabli, donc la bascule vers `true` impossible.
    parser.add_argument("--local-job-budget", type=int, default=120)
    parser.add_argument(
        "--write-token-env",
        default="ACTIONS_VARIABLES_PAT",
        metavar="VAR",
        help=(
            "variable d'environnement du jeton d'ECRITURE de la variable de "
            "depot (defaut ACTIONS_VARIABLES_PAT, secret du depot). Canal "
            "DEDIE, distinct de --token-env : ce jeton sert uniquement a "
            "lire/ecrire la variable. Aucun repli sur un autre jeton."
        ),
    )
    parser.add_argument(
        "--no-local-starvation",
        action="store_true",
        help="ne mesure pas l'affamescence du parc local (garde secondaire)",
    )
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--summary-out",
        metavar="PATH",
        help=(
            "ecrit le resume du job (markdown) dans ce fichier : le verdict, "
            "la cause, et les degrades nommes (jeton d'ecriture absent, etat "
            "de la variable illisible)"
        ),
    )
    parser.add_argument(
        "--now",
        help="instant de reference (ISO 8601) -- determinisme des tests",
    )
    args = parser.parse_args(argv)

    token = os.environ.get(args.token_env) or os.environ.get("GITHUB_TOKEN")
    # Jeton d'ECRITURE de la variable : canal DEDIE, distinct du jeton de
    # mesure. Dans Actions : `secrets.ACTIONS_VARIABLES_PAT`. En local :
    # l'operateur le pose par commande. Il n'y a AUCUN repli sur un autre
    # jeton -- sans lui, le verdict est rendu et rien n'est ecrit.
    write_token = (os.environ.get(args.write_token_env) or "").strip()
    if not token:
        message = (
            f"aucun jeton dans {args.token_env} ni GITHUB_TOKEN : le "
            f"controleur ne peut pas mesurer les files de jobs. "
            f"Prerequisit : un jeton avec le droit `variables: write` sur "
            f"{args.repo} (PAT fin ou App installee) pour le canal "
            f"d'ecriture {args.write_token_env}, et un jeton de mesure dans "
            f"{args.token_env} pour les files."
        )
        if args.json:
            print(json.dumps({"verdict": "REFUSED", "reason": message}, indent=2))
        else:
            print(f"[ci-overflow] REFUSED -- {message}", file=sys.stderr)
        return EXIT_REFUSED

    now = (
        datetime.fromisoformat(args.now.replace("Z", "+00:00"))
        if args.now
        else datetime.now(timezone.utc)
    )

    # Lecture de la variable : le jeton d'ecriture d'abord (il porte le droit
    # `Variables: read-write`), le jeton de mesure en repli LECTURE SEULE
    # (le cas d'un operateur qui n'a pose que le jeton de mesure). Ce repli ne
    # vaut QUE pour la lecture : l'ecriture exige le jeton d'ecriture.
    read_token = write_token or token
    current, updated_at, read_error = read_variable(args.repo, args.variable, read_token)
    state_unknown = current is None and bool(read_error)
    state_reason = ""
    if state_unknown:
        state_reason = (
            f"lecture de la variable {args.variable} impossible : {read_error}. "
            f"Le jeton a-t-il le droit `variables: read` ?"
        )

    hosted = collect_hosted(
        args.repo, args.saturation_minutes, args.job_budget, now, token
    )
    runners_token = os.environ.get(args.runners_token_env) or None
    local = collect_local(
        args.repo,
        args.saturation_minutes,
        args.local_job_budget,
        now,
        token,
        measure_starvation=not args.no_local_starvation,
        runners_token=runners_token,
    )

    # Confirmation de l'inaction du parc local : elle n'est lue QUE si la
    # liberation est autrement candidate (l'offre hebergee n'attend pas et le
    # parc parait inactif). Cout : un appel d'inventaire + la pause.
    local_confirm: LoadConfirm | None = None
    release_candidate = (
        hosted.complete
        and not hosted.truncated
        and hosted.old == 0
        and local.complete
        and local.starved == 0
        and local.charge <= args.max_returned_jobs
    )
    if release_candidate:
        local_confirm = confirm_local_idle(
            args.repo,
            token,
            runners_token=runners_token,
            delay_seconds=args.confirm_seconds,
        )

    decision = evaluate(
        hosted,
        local,
        current,
        saturation_jobs=args.saturation_jobs,
        saturation_minutes=args.saturation_minutes,
        min_free_slots=args.min_free_slots,
        dwell_minutes=args.dwell_minutes,
        max_returned_jobs=args.max_returned_jobs,
        panic_minutes=args.panic_minutes,
        local_confirm=local_confirm,
        last_change_at=updated_at,
        now=now,
    )

    written = False
    write_error = ""
    write_blocked = ""
    if decision.action in ("SWITCH_TRUE", "SWITCH_FALSE") and args.apply:
        if not write_token:
            # Secret absent ou vide : le verdict est RENDU, rien n'est ecrit,
            # et la cause est nommee. Aucun repli sur un autre jeton -- le
            # jeton de mesure n'a pas le droit, et s'en servir serait
            # ecrire avec un jeton non prevu pour cela.
            write_blocked = (
                f"jeton d'ecriture absent ({args.write_token_env}) : le "
                f"verdict est rendu, la variable {args.variable} n'est PAS "
                f"modifiee. Aucun repli sur un autre jeton."
            )
        elif state_unknown:
            write_blocked = (
                f"etat de la variable {args.variable} inconnu : le verdict "
                f"est rendu, l'ecriture est refusee (ni l'etat courant ni le "
                f"dwell ne sont verifiables). {state_reason}"
            )
        else:
            ok, write_error = write_variable(
                args.repo, args.variable, decision.target or "false", write_token
            )
            written = ok
            if not ok:
                decision.action = "REFUSED"
                decision.reason = f"ecriture refusee : {write_error}"

    report = {
        "verdict": decision.action,
        "reason": decision.reason,
        "repo": args.repo,
        "variable": args.variable,
        "current": decision.current,
        "target": decision.target,
        "written": written,
        "mode": "apply" if args.apply else "dry-run",
        "write_token_env": args.write_token_env,
        "write_token_present": bool(write_token),
        "write_blocked": write_blocked,
        "state_known": not state_unknown,
        "state_reason": state_reason,
        "hosted": {
            "queued": hosted.queued,
            "old": hosted.old,
            "oldest_age_min": round(hosted.oldest_age_min, 1),
            "complete": hosted.complete,
            "truncated": hosted.truncated,
            "in_progress_unread": hosted.in_progress_unread,
            "reason": hosted.reason,
        },
        "local": {
            "online": local.online,
            "free": local.free,
            "starved": local.starved,
            "complete": local.complete,
            "truncated": local.truncated,
            "in_progress_unread": local.in_progress_unread,
            "reason": local.reason,
            "busy": local.busy,
            "unknown": local.unknown,
            "charge": local.charge,
        },
        "local_confirm": {
            "read": local_confirm is not None,
            "busy": local_confirm.busy if local_confirm else 0,
            "unknown": local_confirm.unknown if local_confirm else 0,
            "charge": local_confirm.charge if local_confirm else 0,
            "complete": bool(local_confirm.complete) if local_confirm else False,
            "reason": local_confirm.reason if local_confirm else "",
        },
        "thresholds": {
            "saturation_jobs": args.saturation_jobs,
            "saturation_minutes": args.saturation_minutes,
            "min_free_slots": args.min_free_slots,
            "dwell_minutes": args.dwell_minutes,
            "max_returned_jobs": args.max_returned_jobs,
            "confirm_seconds": args.confirm_seconds,
            "panic_minutes": args.panic_minutes,
        },
    }
    if write_error:
        report["write_error"] = write_error

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(
            f"[ci-overflow] {decision.action} -- {decision.reason}\n"
            f"  hebergee : {hosted.queued} job(s) en file "
            f"({hosted.old} de plus de {args.saturation_minutes:.0f} min, "
            f"plus ancien {hosted.oldest_age_min:.0f} min)"
            f"{' -- LECTURE TRONQUEE' if hosted.truncated else ''}\n"
            f"  local    : {local.online} slot(s) en ligne, {local.free} libre(s), "
            f"{local.starved} affame(s), {local.charge} job(s) porte(s) "
            f"(occupes {local.busy} + inconnu {local.unknown})"
            f"{' -- LECTURE TRONQUEE' if local.truncated else ''}\n"
            f"  confirme : "
            + (
                f"{local_confirm.charge} job(s) porte(s) sur la 2e lecture"
                if local_confirm
                else "lecture de confirmation NON faite"
            )
            + "\n"
            f"  variable : {decision.current} -> {decision.target} "
            f"({'ecrit' if written else 'non ecrit'})"
        )
        if write_blocked:
            print(f"  ecriture : REFUSEE -- {write_blocked}")
        if state_reason and not write_blocked:
            print(f"  etat     : {state_reason}")

    if decision.action == "UNREADABLE":
        rc = EXIT_UNREADABLE
    elif decision.action == "REFUSED":
        rc = EXIT_REFUSED
    elif state_unknown:
        # Le verdict est rendu, mais il n'est pas APPLICABLE : ni l'etat
        # courant de la variable ni le dwell ne sont verifiables. Le mode
        # degrade est signale (rc != 0 -> annotation dans le log du job).
        rc = EXIT_UNREADABLE
    else:
        rc = EXIT_OK
    if args.summary_out:
        Path(args.summary_out).write_text(
            render_summary(report, rc), encoding="utf-8"
        )
    return rc


if __name__ == "__main__":
    sys.exit(main())
