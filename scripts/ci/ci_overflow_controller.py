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
- **charge rendue de la cohorte dans la marge hebergee** -> variable a
  `false` : l'offre hebergee n'attend pas, la MARGE de l'offre hebergee
  (plafond moins les jobs heberges en file et en cours) est positive, et la
  charge que la COHORTE rend tient dans cette marge -- confirmee sur une
  **seconde** lecture ;
- sinon -> **HOLD** (on ne touche a rien : une variable qui oscille est pire
  qu'une variable stable).

**Ce qui revient a l'heberge, c'est la COHORTE, pas le parc.** La liberation
rend a l'offre hebergee les jobs dont le workflow lit
`vars.CI_OVERFLOW_LOCAL` (la forme hybride) ; ce sont eux, et eux seuls, qui
migrent selon la variable. Le parc `coursia-linux` porte en permanence des
jobs **STATIQUES** -- meme jeu de labels, workflow qui ne lit pas la variable
-- qui ne reviendront JAMAIS sur l'heberge : les compter comme charge rendue
verrouille la liberation a perpetuite (review du coordinateur, 28/10 : 97
lignes `runs-on` statiques sur ce pool, trois jobs statiques suffisaient).
La liste de la cohorte est **derivee du depot au demarrage**
(`derive_cohort_workflows`), jamais recopiee : un workflow qui rejoint la
forme hybride entre dans le calcul sans qu'on touche a cet organe.

L'ancienne premise -- « le parc local ne porte presque rien », mesuree sur
l'inventaire des SLOTS -- a ete retiree : elle confondait la charge rendue
avec l'occupation du parc, et le seuil absolu qui la bornait n'avait aucun
rapport avec la capacite de l'offre hebergee.

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
  Actions le 2026-10-27T17:05:48Z, valeur regeneree le 2026-10-27T17:24:12Z,
  expiration 2027-10-27).

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

Le cout de l'organe est borne : deux lectures de file systematiques
(hebergee, locale), plafonnees par `--job-budget` (defaut 120) et
`--local-job-budget` (defaut 120) lectures de jobs, plus **une troisieme**
lecture du label local -- la charge rendue de la cohorte -- qui n'est payee
que lorsque la liberation est autrement candidate (l'offre hebergee n'attend
pas et le parc n'est pas affame), exactement comme la seconde lecture de
confirmation qu'elle remplace. Le volume d'appels API est justement l'objet
du volet 5 de #22937, un organe de controle ne doit pas en devenir la cause.
Mesure du 2026-10-27 (file
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
# Plafond de concurrence de l'offre hebergee, en jobs. Mesure du 2026-10-16 :
# 19 jobs heberges en concurrence au pic observe ; on retient 20 (arrondi
# superieur de la mesure). La MARGE hebergee est ce plafond moins les jobs
# heberges en file et en cours : c'est elle, et non un seuil absolu sur le
# parc local, qui borne la charge que la liberation peut rendre.
HOSTED_CONCURRENCY_CAP = 20
# Marqueur de la COHORTE : un workflow est de la cohorte quand il LIT la
# variable de debordement, sous la forme que l'organe d'audit enumere
# (`check_self_hosted_runner_policy.py`, HYBRID_RUNS_ON_OVERFLOW_GUARD :
# `vars.CI_OVERFLOW_LOCAL == 'true'`). Le prefixe `vars.` est delibere : le
# simple nom de la variable apparait aussi dans les commentaires (celui de ce
# controleur, par exemple), et ranger son propre workflow dans la cohorte
# compterait un job STATIQUE du parc local comme charge rendue.
COHORT_MARKER = "vars.CI_OVERFLOW_LOCAL"
# Pause entre les deux lectures de la charge rendue de la cohorte (une seule
# lecture peut tomber sur un instant vide : le parc vient de finir un lot).
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
    # Jobs heberges EN COURS (lus). Avec `queued`, ils occupent la capacite
    # de l'offre : la marge hebergee est le plafond moins ces deux termes.
    in_progress: int = 0
    # Nombre de runs en cours non lus : sous troncature, `in_progress` est une
    # borne INFERIEURE, donc la marge calculee est une borne SUPERIEURE -- la
    # liberation ne peut pas s'appuyer dessus (fail-CLOSED).
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
    # Occupation du parc : slots en ligne et OCCUPES. Rapporte pour
    # l'operateur, mais ce n'est PLUS une premise de decision : le parc porte
    # les jobs de la cohorte ET des jobs statiques, et seule la charge de la
    # cohorte revient a l'offre hebergee (`CohortSample`).
    busy: int = 0
    # Slots en ligne dont l'occupation est INCONNUE (champ `busy` absent de
    # la reponse) : ils sont comptes comme occupes (fail-CLOSED), jamais
    # comme libres.
    unknown: int = 0

    @property
    def charge(self) -> int:
        """Occupation du parc, toutes cohortes confondues (information)."""
        return self.busy + self.unknown


@dataclass
class CohortSample:
    """Charge rendue par la COHORTE, mesuree sur le parc local.

    La liberation rend la cohorte a l'offre hebergee : la charge qui revient
    est le nombre de jobs du label local dont le RUN appartient a un workflow
    de la cohorte, en file (`queued`) comme en cours (`in_progress`). Les
    jobs STATIQUES du meme label n'en font pas partie -- ils ne reviendront
    jamais sur l'heberge.

    `complete=False` : la mesure n'a pas pu etre faite (cohorte illisible,
    listing en echec). `truncated=True` ou `in_progress_unread>0` : la mesure
    est une borne INFERIEURE. Dans les trois cas, la liberation est
    impossible (fail-CLOSED) : elle exige une affirmation NEGATIVE (« la
    charge rendue tient dans la marge »).
    """

    queued: int = 0
    in_progress: int = 0
    complete: bool = True
    truncated: bool = False
    in_progress_unread: int = 0
    reason: str = ""

    @property
    def charge(self) -> int:
        """Charge rendue : jobs de la cohorte en file et en cours."""
        return self.queued + self.in_progress


def hosted_margin(hosted: HostedSample, cap: int = HOSTED_CONCURRENCY_CAP) -> int:
    """Marge de l'offre hebergee : plafond moins les jobs en file et en cours.

    Negative quand l'offre est au-dela de son plafond : la liberation est
    alors impossible, il n'y a pas de place ou rendre la cohorte.
    """
    return cap - (hosted.queued + hosted.in_progress)


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
    hosted_cap: int = HOSTED_CONCURRENCY_CAP,
    panic_minutes: float = DEFAULT_PANIC_MINUTES,
    cohort: CohortSample | None = None,
    cohort_confirm: CohortSample | None = None,
    last_change_at: datetime | None = None,
    now: datetime | None = None,
) -> Decision:
    """Decide de l'etat voulu de la variable. Fonction PURE (aucun appel).

    L'ordre des regles est significatif : la garde de securite (parc local
    affame) passe avant la saturation, sinon on enverrait du debordement vers
    un parc qui n'absorbe rien.

    `cohort` / `cohort_confirm` portent la charge rendue de la COHORTE, sur
    deux lectures ; `cohort=None` signifie « non mesuree » (l'appelant ne la
    mesure que lorsque la liberation est autrement candidate), et bloque la
    liberation sans faire tomber le verdict.
    """
    now = now or datetime.now(timezone.utc)
    margin = hosted_margin(hosted, hosted_cap)

    def details() -> dict:
        return {
            "hosted": hosted,
            "local": local,
            "cohort": cohort,
            "cohort_confirm": cohort_confirm,
            "hosted_margin": margin,
        }

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
            details=details(),
        )

    def hold(reason: str, target: str | None = None) -> Decision:
        return Decision(
            action="HOLD",
            reason=reason,
            current=current,
            target=target,
            details=details(),
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
                    details=details(),
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
            details=details(),
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

    # 2. LIBERATION : la charge rendue par la COHORTE doit tenir dans la
    #    MARGE hebergee.
    #
    #    Ce que la liberation fait : elle rend la COHORTE a l'offre
    #    hebergee -- les jobs dont le workflow lit `vars.CI_OVERFLOW_LOCAL`,
    #    et eux seuls. Le parc `coursia-linux` porte en permanence des jobs
    #    STATIQUES (meme jeu de labels, workflow hors cohorte) qui ne
    #    reviendront JAMAIS sur l'heberge : les compter comme charge rendue
    #    verrouille la liberation des que trois jobs statiques tournent, soit
    #    le regime normal d'une journee de PRs (review du coordinateur,
    #    28/10 -- le defaut avait change de signe, pas de nature).
    #
    #    Le cote heberge n'est pas un seuil absolu mais la MARGE de l'offre :
    #    plafond heberge (`HOSTED_CONCURRENCY_CAP`) moins les jobs heberges
    #    en file et en cours. Rendre la cohorte a une offre qui n'a pas la
    #    place, c'est la nuit du 27/10.
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
    #      b) la marge hebergee est strictement positive, et son terme
    #         « en cours » est entierement lu (sinon la marge est une borne
    #         superieure) ;
    #      c) la charge rendue de la COHORTE (en file + en cours) tient dans
    #         cette marge, sur une lecture complete et non tronquee ;
    #      d) la mesure est CONFIRMEE par une SECONDE lecture de la charge
    #         rendue, espacee de `--confirm-seconds` : une seule lecture peut
    #         tomber sur un instant vide (le parc vient de finir un lot).
    #         Les DEUX lectures doivent tenir dans la marge : c'est la lecture
    #         la plus haute qui decide, jamais la plus basse.
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
    def unreadable(reason: str) -> Decision:
        return Decision(
            action="UNREADABLE",
            reason=reason,
            current=current,
            details=details(),
        )

    if not release_blockers:
        # Les premises « l'offre hebergee n'attend pas » tiennent : c'est ICI
        # que la charge rendue doit etre etablie. Son absence,
        # son illisibilite et sa troncature ne sont pas des reports -- ce
        # sont des mesures ILLISIBLES (fail-CLOSED, jamais une liberation).
        if cohort is None:
            release_blockers.append(
                "la charge rendue de la cohorte n'a pas ete mesuree : « la "
                "charge rendue tient dans la marge hebergee » n'est pas "
                "etablie"
            )
        elif not cohort.complete:
            return unreadable(
                f"la charge rendue de la cohorte n'est pas mesurable "
                f"({cohort.reason}) : ni la liberation ni son refus ne sont "
                f"etablis -- aucune bascule"
            )
        else:
            if hosted.in_progress_unread > 0:
                release_blockers.append(
                    f"{hosted.in_progress_unread} run(s) heberge(s) en cours "
                    f"non lu(s) (budget de lecture) : le nombre de jobs "
                    f"heberges en cours est une borne INFERIEURE, donc la "
                    f"marge hebergee ({margin}) est une borne SUPERIEURE"
                )
            elif margin <= 0:
                release_blockers.append(
                    f"marge hebergee nulle ou negative : plafond "
                    f"{hosted_cap}, {hosted.queued} job(s) heberge(s) en file "
                    f"+ {hosted.in_progress} en cours -> marge {margin}"
                )
            if cohort.truncated:
                release_blockers.append(
                    f"lecture de la charge rendue TRONQUEE "
                    f"({cohort.reason}) : le compte de la cohorte est une "
                    f"borne INFERIEURE"
                )
            if cohort.in_progress_unread > 0:
                release_blockers.append(
                    f"{cohort.in_progress_unread} run(s) local(aux) en cours "
                    f"non lu(s) : la charge rendue de la cohorte est une "
                    f"borne INFERIEURE"
                )
            if margin > 0 and cohort.charge > margin:
                release_blockers.append(
                    f"la charge rendue de la cohorte ({cohort.charge} job(s) : "
                    f"{cohort.queued} en file + {cohort.in_progress} en cours) "
                    f"depasse la marge hebergee ({margin} = plafond "
                    f"{hosted_cap} - {hosted.queued} en file - "
                    f"{hosted.in_progress} en cours)"
                )
            if cohort_confirm is None:
                release_blockers.append(
                    "la confirmation manque (seconde lecture de la charge "
                    "rendue non faite) : la charge rendue n'est pas etablie"
                )
            elif not cohort_confirm.complete:
                return unreadable(
                    f"la seconde lecture de la charge rendue n'est pas "
                    f"mesurable ({cohort_confirm.reason}) : la charge rendue "
                    f"n'est pas confirmee -- aucune bascule"
                )
            else:
                if cohort_confirm.truncated:
                    release_blockers.append(
                        f"seconde lecture TRONQUEE "
                        f"({cohort_confirm.reason}) : la charge rendue "
                        f"confirmee est une borne INFERIEURE"
                    )
                if cohort_confirm.in_progress_unread > 0:
                    release_blockers.append(
                        f"{cohort_confirm.in_progress_unread} run(s) "
                        f"local(aux) en cours non lu(s) sur la seconde "
                        f"lecture : la charge rendue confirmee est une borne "
                        f"INFERIEURE"
                    )
                if margin > 0 and cohort_confirm.charge > margin:
                    release_blockers.append(
                        f"la confirmation contredit la premiere lecture : "
                        f"{cohort_confirm.charge} job(s) de cohorte au lieu "
                        f"de {margin} ou moins (marge hebergee) -- la charge "
                        f"rendue n'est pas confirmee"
                    )
    if not release_blockers:
        return switch(
            "false",
            f"la charge rendue de la cohorte tient dans la marge hebergee : "
            f"{cohort.charge if cohort else '?'} job(s) confirme(s) a "
            f"{cohort_confirm.charge if cohort_confirm else '?'} sur la "
            f"seconde lecture, marge {margin} (plafond {hosted_cap} - "
            f"{hosted.queued} job(s) en file - {hosted.in_progress} en cours) "
            f"et l'offre hebergee n'attend pas -- la cohorte revient a "
            f"l'offre hebergee",
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
    # Un operateur doit pouvoir lire l'etat des deux cotes du calcul de
    # liberation, meme quand la liberation n'a meme pas ete tentee.
    notes.append(
        f"marge hebergee {margin} (plafond {hosted_cap} - "
        f"{hosted.queued} job(s) heberge(s) en file - {hosted.in_progress} "
        f"en cours)"
    )
    if cohort is not None:
        notes.append(
            f"charge rendue de la cohorte {cohort.charge} job(s) "
            f"({cohort.queued} en file + {cohort.in_progress} en cours)"
            + ("" if cohort.complete else f" [ILLISIBLE : {cohort.reason}]")
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
    """Mesure l'offre hebergee : jobs `ubuntu-latest` en file ET en cours.

    Les deux termes occupent la capacite de l'offre : la marge hebergee est
    le plafond moins leur somme. `in_progress_sample=job_budget` demande la
    lecture de TOUS les runs en cours que le budget permet -- un echantillon
    partiel rendrait la marge trop grande, donc la liberation trop facile.
    Les runs en cours non lus restent comptes dans `in_progress_unread`, et
    une marge tiree d'une borne inferieure n'autorise pas la liberation.
    """
    if token:
        os.environ["GH_TOKEN"] = token
    starv = crs.fetch_starvation(
        repo,
        HOSTED_LABEL,
        starve_minutes=0.0,
        now=now,
        job_read_budget=job_budget,
        in_progress_sample=job_budget,
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
        in_progress=len(starv.in_progress),
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


def _without_comment_lines(text: str) -> str:
    """Retire les lignes de COMMENTAIRE YAML avant de chercher le marqueur.

    Le nom de la variable figure legitimement dans des commentaires (l'en-tete
    de ce controleur, celui de son propre workflow). Un fichier qui ne fait
    que MENTIONNER la variable n'est pas de la cohorte : c'est un job
    statique, et le compter comme charge rendue ferait payer la liberation
    pour un job qui ne revient jamais sur l'heberge. On ne retire que les
    lignes entierement commentaires -- une valeur de cle contenant un `#`
    reste lue.
    """
    return "\n".join(
        line for line in text.splitlines()
        if not line.lstrip().startswith("#")
    )


def derive_cohort_workflows(repo_root: Path) -> tuple[set[str], str]:
    """Derive du depot la liste des workflows de la COHORTE.

    La cohorte, ce sont les jobs qui MIGRENT avec la variable : ceux dont le
    workflow lit `vars.CI_OVERFLOW_LOCAL` (la forme hybride, cf
    `check_self_hosted_runner_policy.py`). La liste est **lue** dans le
    checkout a chaque passage, jamais recopiee : un workflow qui rejoint la
    forme hybride entre dans le calcul sans qu'on touche a cet organe, et un
    workflow qui la quitte en sort.

    Rend `(chemins, motif)`, `chemins` sous la forme que porte `run.path`
    dans l'API des runs (`.github/workflows/<fichier>`). `motif` est vide
    quand la derivation a reussi. Les deux echecs -- repertoire absent ou
    illisible, liste VIDE -- rendent un ensemble vide ET un motif : un
    ensemble vide ne doit JAMAIS se lire « la cohorte ne rend rien » (ce
    serait une liberation), il se lit « la cohorte n'est pas etablie »
    (fail-CLOSED, cf `collect_cohort_charge`).

    `repo_root` est un parametre pour que la derivation se teste sur un
    petit repertoire de fixtures, sans lire le depot reel.
    """
    workflows_dir = Path(repo_root) / ".github" / "workflows"
    if not workflows_dir.is_dir():
        return set(), f"repertoire des workflows absent ({workflows_dir})"
    try:
        files = sorted(
            list(workflows_dir.glob("*.yml")) + list(workflows_dir.glob("*.yaml"))
        )
    except OSError as exc:  # enumeration impossible : permission, disque
        return set(), f"enumeration des workflows impossible ({exc})"
    paths: set[str] = set()
    for path in files:
        try:
            content = path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            # Un seul fichier illisible suffit : la cohorte serait
            # silencieusement amputee, donc sous-estimee, donc la liberation
            # trop facile.
            return set(), f"lecture de {path.name} impossible ({exc})"
        if COHORT_MARKER in _without_comment_lines(content):
            paths.add(f".github/workflows/{path.name}")
    if not paths:
        return set(), (
            f"aucun workflow de {workflows_dir} ne lit "
            f"`{COHORT_MARKER}` -- la cohorte n'est pas etablie"
        )
    return paths, ""


def collect_cohort_charge(
    repo: str,
    cohort_paths: set[str],
    job_budget: int,
    now: datetime,
    token: str | None,
    delay_seconds: float = 0.0,
) -> CohortSample:
    """Mesure la charge que la COHORTE rend au parc local.

    Une lecture de file sur le label local (`fetch_starvation`, seuil d'age
    nul : on veut TOUS les jobs, pas seulement les affames), puis un filtre
    par chemin de workflow -- le chemin est deja dans la reponse des runs, le
    filtre ne coute aucun appel de plus.

    Sont comptes les jobs en FILE et EN COURS dont `run_path` appartient a la
    cohorte. Les jobs STATIQUES (meme label, workflow hors cohorte) ne
    reviendront jamais sur l'heberge : ils ne sont pas comptes. Un
    `run_path` vide (champ absent de la reponse) ne compte pas non plus -- il
    n'est pas etabli que le run soit de la cohorte, et compter « inconnu »
    comme cohorte ferait payer la liberation pour des jobs qui ne reviennent
    pas ; l'inverse (l'ignorer) est borne par le fait que la troncature, elle,
    bloque (fail-CLOSED).

    `delay_seconds` : la pause de la SECONDE lecture. La confirmation de la
    charge rendue, c'est exactement le meme appel, espace de
    `--confirm-seconds` -- une seule lecture peut tomber sur un instant vide
    (le parc vient de finir un lot).

    Echec de lecture, liste de cohorte vide, troncature du budget et runs en
    cours non lus rendent `complete=False`, `truncated` ou
    `in_progress_unread>0` -- jamais une liberation.
    """
    if not cohort_paths:
        return CohortSample(
            complete=False,
            reason="liste de la cohorte vide : la charge rendue n'est pas etablie",
        )
    if delay_seconds > 0:
        time.sleep(delay_seconds)
    if token:
        os.environ["GH_TOKEN"] = token
    starv = crs.fetch_starvation(
        repo,
        LOCAL_LABEL,
        starve_minutes=0.0,
        now=now,
        job_read_budget=job_budget,
        in_progress_sample=job_budget,
    )
    if not starv.complete:
        return CohortSample(
            complete=False,
            reason=(
                f"lecture de la file locale incomplete "
                f"({len(starv.listing_failed)} listing(s) en echec, "
                f"{starv.stats.failed} appel(s) en echec)"
            ),
        )

    def in_cohort(row: crs.JobRow) -> bool:
        # `run_path` vide = chemin non rendu par l'API : jamais un membre de
        # la cohorte (une chaine vide ne doit pas matcher un ensemble).
        return bool(row.run_path) and row.run_path in cohort_paths

    queued = [row for row in starv.starved if in_cohort(row)]
    running = [row for row in starv.in_progress if in_cohort(row)]
    reason = ""
    if starv.truncated:
        reason = (
            f"{len(starv.budget_unread)} run(s) local(aux) non lu(s) (budget "
            f"de lecture {job_budget} atteint) -- le compte de la cohorte est "
            f"une borne INFERIEURE"
        )
    return CohortSample(
        queued=len(queued),
        in_progress=len(running),
        complete=True,
        truncated=starv.truncated,
        in_progress_unread=starv.in_progress_unread,
        reason=reason,
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
    cohort = report.get("cohort", {})
    confirm = report.get("cohort_confirm", {})
    lines = [
        "### CI overflow controller (phase B) -- VERDICT",
        "",
        f"- code retour : {rc}",
        f"- verdict : {report.get('verdict')}",
        f"- raison : {report.get('reason')}",
        f"- variable : {report.get('current')} -> {report.get('target')} "
        f"({'ECRIT' if report.get('written') else 'NON ECRIT'})",
        f"- hebergee : {hosted.get('queued')} job(s) en file, "
        f"{hosted.get('in_progress')} en cours, "
        f"{hosted.get('old')} de plus de "
        f"{thresholds.get('saturation_minutes', 0):.0f} min, "
        f"marge {report.get('hosted_margin')} "
        f"(plafond {thresholds.get('hosted_cap')})"
        + (" [LECTURE TRONQUEE]" if hosted.get("truncated") else ""),
        f"- local : {local.get('online')} slot(s) en ligne, "
        f"{local.get('free')} libre(s), {local.get('starved')} affame(s)"
        + (" [LECTURE TRONQUEE]" if local.get("truncated") else ""),
        f"- cohorte : charge rendue {cohort.get('charge')} job(s) "
        f"({cohort.get('queued')} en file + {cohort.get('in_progress')} en "
        f"cours) sur {cohort.get('workflows')} workflow(s) derive(s) du "
        f"depot"
        + (" [NON MESUREE]" if not cohort.get("measured") else "")
        + (
            f" [ILLISIBLE : {cohort.get('reason')}]"
            if cohort.get("measured") and not cohort.get("complete")
            else ""
        )
        + (" [LECTURE TRONQUEE]" if cohort.get("truncated") else ""),
        f"- confirmation : charge rendue "
        + (
            f"{confirm.get('charge')} job(s)"
            if confirm.get("measured")
            else "NON MESUREE (pas de seconde lecture)"
        ),
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
        "--hosted-cap",
        type=int,
        default=HOSTED_CONCURRENCY_CAP,
        help=(
            "plafond de concurrence de l'offre hebergee, en jobs : la marge "
            "hebergee est ce plafond moins les jobs heberges en file et en "
            "cours, et la liberation exige que la charge rendue de la "
            "cohorte tienne dans cette marge"
        ),
    )
    parser.add_argument(
        "--confirm-seconds",
        type=float,
        default=DEFAULT_CONFIRM_SECONDS,
        help=(
            "pause avant la seconde lecture de la charge rendue de la "
            "cohorte (la liberation n'a lieu que si les DEUX lectures "
            "tiennent dans la marge hebergee)"
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

    # Liste de la COHORTE : derivee du depot a chaque passage, jamais
    # recopiee (un workflow qui rejoint la forme hybride entre dans le calcul
    # sans qu'on touche a cet organe).
    repo_root = Path(__file__).resolve().parents[2]
    cohort_paths, cohort_reason = derive_cohort_workflows(repo_root)

    # Charge rendue de la cohorte : elle n'est lue QUE si la liberation est
    # autrement candidate (l'offre hebergee n'attend pas et le parc local
    # n'est pas affame) -- sinon elle ne peut rien changer au verdict et
    # couterait une lecture de file entiere. La confirmation est la MEME
    # lecture, espacee de `--confirm-seconds`.
    cohort: CohortSample | None = None
    cohort_confirm: CohortSample | None = None
    release_candidate = (
        hosted.complete
        and not hosted.truncated
        and hosted.old == 0
        and local.complete
        and local.starved == 0
    )
    if not cohort_paths:
        # Cohorte non etablie : `evaluate` rend UNREADABLE des que la
        # liberation est le seul verdict possible. La nommer ici (et non la
        # laisser `None`) permet au rapport de dire POURQUOI.
        cohort = CohortSample(
            complete=False,
            reason=(
                "liste de la cohorte derivee du depot vide ou illisible "
                f"({cohort_reason})"
            ),
        )
    elif release_candidate:
        cohort = collect_cohort_charge(
            args.repo, cohort_paths, args.local_job_budget, now, token
        )
        if (
            cohort.complete
            and not cohort.truncated
            and cohort.in_progress_unread == 0
        ):
            cohort_confirm = collect_cohort_charge(
                args.repo,
                cohort_paths,
                args.local_job_budget,
                now,
                token,
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
        hosted_cap=args.hosted_cap,
        panic_minutes=args.panic_minutes,
        cohort=cohort,
        cohort_confirm=cohort_confirm,
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
            "in_progress": hosted.in_progress,
            "in_progress_unread": hosted.in_progress_unread,
            "reason": hosted.reason,
        },
        "hosted_margin": hosted_margin(hosted, args.hosted_cap),
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
        # La cohorte, ce sont les workflows qui LISENT la variable : la liste
        # est derivee du depot a chaque passage (`derive_cohort_workflows`),
        # le compte la rend verifiable sans recopier les chemins.
        "cohort": {
            "measured": cohort is not None,
            "workflows": len(cohort_paths),
            "derivation": cohort_reason,
            "queued": cohort.queued if cohort else 0,
            "in_progress": cohort.in_progress if cohort else 0,
            "charge": cohort.charge if cohort else 0,
            "complete": bool(cohort.complete) if cohort else False,
            "truncated": bool(cohort.truncated) if cohort else False,
            "in_progress_unread": cohort.in_progress_unread if cohort else 0,
            "reason": cohort.reason if cohort else "",
        },
        "cohort_confirm": {
            "measured": cohort_confirm is not None,
            "queued": cohort_confirm.queued if cohort_confirm else 0,
            "in_progress": cohort_confirm.in_progress if cohort_confirm else 0,
            "charge": cohort_confirm.charge if cohort_confirm else 0,
            "complete": bool(cohort_confirm.complete) if cohort_confirm else False,
            "truncated": bool(cohort_confirm.truncated) if cohort_confirm else False,
            "in_progress_unread": (
                cohort_confirm.in_progress_unread if cohort_confirm else 0
            ),
            "reason": cohort_confirm.reason if cohort_confirm else "",
        },
        "thresholds": {
            "saturation_jobs": args.saturation_jobs,
            "saturation_minutes": args.saturation_minutes,
            "min_free_slots": args.min_free_slots,
            "dwell_minutes": args.dwell_minutes,
            "hosted_cap": args.hosted_cap,
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
            f"  hebergee : {hosted.queued} job(s) en file, "
            f"{hosted.in_progress} en cours ({hosted.old} de plus de "
            f"{args.saturation_minutes:.0f} min, plus ancien "
            f"{hosted.oldest_age_min:.0f} min), marge "
            f"{hosted_margin(hosted, args.hosted_cap)} "
            f"(plafond {args.hosted_cap})"
            f"{' -- LECTURE TRONQUEE' if hosted.truncated else ''}\n"
            f"  local    : {local.online} slot(s) en ligne, {local.free} libre(s), "
            f"{local.starved} affame(s), {local.charge} slot(s) occupe(s) "
            f"(occupes {local.busy} + inconnu {local.unknown}) -- information, "
            f"le parc porte aussi des jobs statiques"
            f"{' -- LECTURE TRONQUEE' if local.truncated else ''}\n"
            f"  cohorte  : charge rendue "
            + (
                f"{cohort.charge} job(s) ({cohort.queued} en file + "
                f"{cohort.in_progress} en cours) sur {len(cohort_paths)} "
                f"workflow(s) derive(s) du depot"
                + ("" if cohort.complete else f" -- ILLISIBLE ({cohort.reason})")
                if cohort is not None
                else "NON MESUREE"
            )
            + "\n"
            f"  confirme : "
            + (
                f"{cohort_confirm.charge} job(s) de cohorte sur la 2e lecture"
                if cohort_confirm
                else "seconde lecture NON faite"
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
