#!/usr/bin/env python3
"""Rejoue les jambes `PR gate` bloquees par le MINUTEUR DWELL, une fois le
plancher brut ecoule.

Pourquoi cet organe existe
--------------------------
Le plancher DWELL (`scripts/ci/merge_dwell.py`, `DEFAULT_DWELL_MIN = 120`)
produit un rouge de `PR gate` qui n'est **pas** un defaut du code : c'est un
minuteur. La jambe se re-agrege au balayage suivant
(`pr-gate-stale-sweep.yml`, cadence MESUREE 2 h 33 a 5 h 18 entre tirs, pas
horaire malgre son cron `7 * * * *` -- #15197). D'ici la, chaque lane qui
retrouve une PR rouge fait le meme calcul a la main.

Le piege mesure (#27242, 2026-11-18) : le message du minuteur porte DEUX
horodatages.
  - `reste NN min`      : l'etat du plancher ;
  - `ecoule a <T>`      : la **prochaine pointe du balayage**, PAS l'echeance
                          du plancher (le plancher brut, c'est la tete + 120 min).
Lire `ecoule a` comme une echeance retarde chaque PR d'environ une heure ; le
champ existe pour dire a la lane "tu reverras ce resultat au prochain
balayage", pas "rien ne bougera avant".

Ce que fait l'organe, donc :
  1. relit la tete de la PR et l'heure de commit (celle du minuteur) ;
  2. calcule le **plancher brut** = heure de commit + `DEFAULT_DWELL_MIN` ;
  3. verifie que la jambe `PR gate` est bien un minuteur DWELL (pas un rouge
     reel) -- un rouge de code n'est **jamais** rejoue par cet organe ; une
     jambe **en cours** n'est ni verte ni rouge (GitHub n'ecrit son titre
     qu'a la fin du job : un titre vide y ressemble a un echec etrange) ;
  4. rejoue la jambe (`gh run rerun <run_id> --job <job_id>`) si et seulement
     si le plancher brut est passe.

Perimetre et fraicheur (demande du coordinateur, 19/11)
------------------------------------------------------
  5. la PR doit etre **ouverte** (`state=open`) : une PR fermee est hors
     perimetre, meme si son minuteur est un vestige ;
  6. juste avant le geste, l'etat est **relu** (tete, `state`, controle
     `PR gate` selectionne) : si la premiere lecture a vieilli, le geste est
     **refuse** -- fail-CLOSED, une relecture impossible n'est jamais « rien
     n'a change ».

Orthogonalement : le minuteur se laisse lever par le label
`merge-dwell-waived` (urgence `main` rouge) -- l'organe n'y touche pas.

Lecture STRICTE (c3272)
-----------------------
Une reponse **absente**, **mal formee** ou **tronquee** est un **refus**,
jamais une valeur par defaut. Concretement :
  - `labels` absent, non-liste, ou element sans `name` -> refus ;
  - `draft` absent, ou non booleen -> refus ;
  - `check_runs` absent, non-liste, ou element non objet -> refus ;
  - plafond de pagination atteint (liste tronquee) -> refus.
Un refus ne produit **aucun verdict** : l'entree sort en action `incomplet`
et l'organe sort en rc 2. C'est la distinction qui compte : « je n'ai pas
reussi a lire » n'est pas « la jambe n'existe pas » -- l'absence de
check-run se deduit d'une lecture **complete**, jamais d'une lecture cassee.

Usage
-----
    python scripts/ci/replay_dwell_floors.py --pr 27262 27263      # lecture
    python scripts/ci/replay_dwell_floors.py --pr 27262 --apply    # rejoue
    python scripts/ci/replay_dwell_floors.py --all --json          # inventaire

Le mode par defaut est la **lecture seule** (dry-run) : `--apply` est
explicite, comme `scripts/ci/prune_merged_worktrees.py`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import merge_dwell  # noqa: E402  (chemin ajoute ci-dessus)
from merge_dwell import (  # noqa: E402
    DEFAULT_DWELL_MIN,
    WAIVER_LABEL,
    head_committed_at,
    parse_iso8601,
    parse_pending_message,
)

REPO_DEFAULT = "jsboige/CoursIA"
GATE_NAME = "PR gate"


class LectureIncomplete(RuntimeError):
    """La lecture n'a pas produit une information exploitable.

    Distincte de l'echec d'appel (reseau, `gh` absent) : ici la reponse est
    arrivee mais elle est **mal formee**, **tronquee**, ou **absente** sur un
    champ dont l'organe a besoin pour decider. Une telle lecture ne doit
    **jamais** produire de verdict : elle est un refus, pas une donnee.

    Pourquoi (c3272, point du coordinateur) : `pr_info` transformait des
    `labels` absents ou mal formes en `[]`, et un `draft` absent en `False` ;
    `inspect_pr` ecrivait alors `labels_lus = True`. Une reponse lue de
    travers se distingue d'une reponse lue : l'absent devenait un **fait**
    (« pas de derogation », « pas un brouillon »). De meme, une liste de
    `check_runs` de forme invalide devenait une liste vide -- et une liste
    vide se lit « aucune check-run `PR gate` », c'est-a-dire une **absence**,
    alors que la lecture etait **cassee**.
    """


# --------------------------------------------------------------------------
# Fonctions PURES (testables sans reseau)
# --------------------------------------------------------------------------

def dwell_floor(committed_at: datetime, dwell_min: float = DEFAULT_DWELL_MIN) -> datetime:
    """Plancher BRUT : l'heure de commit de la tete + le dwell.

    C'est l'echeance reelle du minuteur. Le champ `ecoule a` du message n'est
    pas cette echeance (voir l'entete du module).
    """
    return committed_at + timedelta(minutes=dwell_min)


def is_dwell_timer(title: str) -> bool:
    """Vrai si le message de la jambe est celui d'un plancher NON ecoule.

    On reutilise le parseur de l'emetteur (`merge_dwell.parse_pending_message`)
    plutot qu'une copie de la forme : une copie deriverait en silence, et le
    minuteur redeviendrait invisible -- c'est exactement le piege que
    `merge_dwell` documente.
    """
    return parse_pending_message(title or "") is not None


def emitter_floor(title: str) -> tuple[datetime, datetime, float] | None:
    """`(plancher brut, head_at, dwell_min)` lus dans le message de l'emetteur.

    Le plancher n'est plus **recalcule** par l'organe : il est **lu** dans le
    message que l'emetteur a produit pour la tete exacte. `head_at` est la
    date de `last_authoritative_committed_at()` -- le dernier commit qui
    **modifie le cote PR** -- et `dwell_min` est le dwell que l'emetteur a
    reellement applique (il peut differer du defaut du module).

    Pourquoi (c3271, exige du coordinateur) : l'organe recalculait le
    plancher depuis la date de **tete**. Apres un `update-branch` **sans
    conflit**, la date de tete est plus recente que `head_at` -- le
    rafraichissement de base est *prouve* content-free, il ne rearme donc pas
    le plancher -- et le plancher de l'organe etait **plus tardif** que celui
    de l'emetteur : l'organe disait « attendre » la ou le gate disait deja
    « plancher ecoule ». Un plancher **lu** ne peut pas diverger de celui qui
    l'a produit.
    """
    parsed = parse_pending_message(title or "")
    if not parsed:
        return None
    head_at = parse_iso8601(parsed["head_at"])
    dwell_min = float(parsed["dwell_min"])
    return head_at + timedelta(minutes=dwell_min), head_at, dwell_min


def decide(
    *,
    conclusion: str,
    title: str,
    committed_at: datetime,
    now: datetime,
    dwell_min: float = DEFAULT_DWELL_MIN,
    waived: bool = False,
    status: str = "completed",
    draft: bool = False,
    state: str = "open",
) -> tuple[str, str]:
    """Decide quoi faire d'une jambe `PR gate`. Fonction PURE.

    Renvoie `(action, motif)` avec `action` dans :
      - ``"rejouer"``  : le plancher brut est passe, la jambe est un minuteur ;
      - ``"attendre"`` : plancher brut pas encore passe, ou jambe EN COURS ;
      - ``"ignorer"``  : rien a faire (legende verte, derogation, brouillon,
        rouge reel).

    Un rouge **reel** (echec qui n'est pas le minuteur) n'est jamais rejoue :
    rejouer un test rouge rend le MEME rouge, et le cache des legs la rendrait
    silencieuse.

    Cas mesure le 2026-11-18 (#26989) : une jambe **en cours** porte un
    `output.title` **vide** (GitHub ne l'ecrit qu'a la fin du job). Sans le
    test de `status`, un titre vide passait pour « pas le minuteur » et le
    verdict tombait sur « rouge reel » : un minuteur etait classe dans la
    mauvaise famille, et un consommateur qui s'arrete sur ce verdict abandonnait
    la PR. Une jambe qui n'a pas fini n'est **ni verte ni rouge** -- elle est en
    cours, et le seul geste possible est d'attendre.

    Lecture stricte (relire du coordinateur, 19/11 00:05Z) : le rejeu exige
    une jambe **explicitement terminee ET en echec**. Un `status` absent
    n'est pas « terminee » (la reponse est incomplete : fail-CLOSED), et une
    conclusion qui n'est pas `failure` n'est pas un echec (annulee, ignoree,
    neutre : rien a rejouer). Mesure du 19/11 : les jambes `PR gate` porteuses
    du minuteur sont `completed` + `failure` (#27273, #27297, #27319).

    Le plancher est celui de l'**emetteur** (`emitter_floor`), pas un recalcul
    depuis `committed_at` : voir la note de `emitter_floor`. `committed_at` et
    `dwell_min` ne servent plus qu'a l'affichage et a la compatibilite de
    l'appel ; le verdict, lui, sort du message.

    PERIMETRE (reserve du coordinateur du 19/11 01:32Z) : le rejeu ne porte
    que sur une PR **ouverte**. Une PR fermee est hors perimetre : son
    minuteur peut etre un vestige d'une PR qu'on ne rejouera plus, et
    `--all` peut rencontrer une fermeture **apres** son inventaire.

    Une `head_at` **dans le futur** (decalage d'horloge entre l'hote qui a
    produit le message et celui qui le lit) ne vaut pas un plancher ecoule :
    fail-CLOSED.
    """
    if draft:
        return "ignorer", ("PR en brouillon -- exclue par conception "
                           "(comme le balayeur `pr-gate-stale-sweep.yml`), "
                           "jamais rejouee")
    if state != "open":
        # Exigence du coordinateur (reserve du 19/11 01:32Z, #27273) : une PR
        # **fermee** est hors perimetre du rejeu. `pr_info` ne lisait pas
        # `state` : un ancien minuteur pouvait etre relance sur une PR
        # fermee, et `--all` pouvait rencontrer une fermeture apres son
        # inventaire. Fermer une PR ne rend pas sa jambe rejouable : la
        # decision porte sur l'etat **du PR**, pas sur celui du minuteur.
        return "ignorer", ("PR fermee (state=`{}`) -- hors perimetre du "
                           "rejeu".format(state or "absent"))
    if conclusion == "success":
        return "ignorer", "jambe verte"
    if waived:
        return "ignorer", "derogation par label `{}`".format(WAIVER_LABEL)
    if status != "completed":
        # Un `status` ABSENT n'est pas « terminee » : c'est une reponse
        # incomplete. Fail-CLOSED : on attend, on ne rejoue pas sur une
        # lecture qui n'a pas tout dit (relire du coordinateur, 19/11).
        return "attendre", ("jambe en cours ou reponse incomplete (statut `{}`)".format(
            status or "absent"))
    if conclusion != "failure":
        # Une jambe terminee mais conclue autrement (annulee, ignoree, neutre)
        # n'est pas un echec : il n'y a rien a rejouer. Le rejeu exige une
        # jambe **explicitement** terminee ET en echec.
        return "ignorer", ("conclusion `{}` -- ni verte ni en echec : rien a rejouer".format(
            conclusion or "absente"))
    plancher = emitter_floor(title)
    if plancher is None:
        return "ignorer", "echec qui n'est pas le minuteur DWELL (rouge reel)"
    floor, head_at, _dwell_reel = plancher
    if head_at > now:
        return "attendre", ("tete datee dans le futur ({}) -- fail-CLOSED".format(
            head_at.strftime("%Y-%m-%dT%H:%M:%SZ")))
    if now < floor:
        return "attendre", "plancher brut pas encore passe ({})".format(
            floor.strftime("%Y-%m-%dT%H:%M:%SZ"))
    return "rejouer", "plancher brut passe ({})".format(
        floor.strftime("%Y-%m-%dT%H:%M:%SZ"))


# --------------------------------------------------------------------------
# Acces reseau (injectable pour les tests)
# --------------------------------------------------------------------------

def gh_json(path: str) -> object:
    """Lecture JSON via `gh api` (meme contrat que `merge_dwell._gh_json`)."""
    try:
        completed = subprocess.run(
            ["gh", "api", path], capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=False,
        )
    except FileNotFoundError as exc:  # pragma: no cover - environnement
        raise RuntimeError("gh introuvable : {}".format(exc)) from exc
    if completed.returncode != 0:
        raise RuntimeError("gh api {} a echoue : {}".format(
            path, (completed.stderr or completed.stdout or "").strip()[:200]))
    try:
        return json.loads(completed.stdout or "null")
    except json.JSONDecodeError as exc:
        raise RuntimeError("gh api {} : JSON illisible".format(path)) from exc


def open_pr_numbers(repo: str, per_page: int = 100,
                    max_pages: int = 100) -> list[int]:
    """Toutes les PR ouvertes du depot -- **toutes les pages**.

    CORRECTION c3271 : la version precedente lisait UNE seule page
    (`per_page=100`, sans pagination). Le depot comptait 194 PRs ouvertes le
    2026-11-18 : `--all` n'examinait que les 100 premieres (les plus
    recentes, l'ordre par defaut de l'API), soit **la moitie du parc** -- et
    l'organe annoncait dans son aide « examine toutes les PR ouvertes du
    depot ». Une promesse que l'organe ne tient pas est un defaut de
    l'organe : on pagine jusqu'a epuisement, et on expose le nombre de pages
    lues dans la sortie JSON pour que l'ecart soit verifiable.

    CORRECTION c3272 : le plafond de pages ne tronque plus **silencieusement** :
    une liste tronquee se lirait comme un inventaire complet. Le plafond
    atteint est un **refus** (`LectureIncomplete`), comme une reponse qui
    n'est pas une liste.
    """
    numbers: list[int] = []
    page = 1
    while True:
        payload = gh_json(
            "repos/{}/pulls?state=open&per_page={}&page={}".format(
                repo, per_page, page))
        if not isinstance(payload, list):
            raise LectureIncomplete(
                "liste des PRs ouvertes illisible (page {}) -- forme "
                "inattendue".format(page))
        if not payload:
            break
        for p in payload:
            if not isinstance(p, dict) or "number" not in p:
                raise LectureIncomplete(
                    "liste des PRs ouvertes mal formee (page {})".format(page))
            numbers.append(int(p["number"]))
        if len(payload) < per_page:
            break
        page += 1
        if page > max_pages:  # garde-fou : ne pas boucler sur une API qui
            # renverrait toujours la meme page pleine. Une troncature est un
            # **refus**, pas un inventaire.
            raise LectureIncomplete(
                "plafond de pagination atteint ({} pages) -- inventaire "
                "tronque, aucune conclusion tiree".format(max_pages))
    return numbers


def pr_head_sha(repo: str, number: int) -> str:
    payload = gh_json("repos/{}/pulls/{}".format(repo, number))
    head = payload.get("head") if isinstance(payload, dict) else None
    sha = head.get("sha") if isinstance(head, dict) else None
    if not sha:
        raise LectureIncomplete(
            "PR {} : tete absente de la reponse".format(number))
    return str(sha)


def pr_info(repo: str, number: int) -> dict:
    """Ce qu'il faut de la PR pour decider : tete, labels, brouillon, etat.

    Les `labels` et le `draft` sont lus dans la **meme** charge utile que la
    tete : une derogation ne peut etre annoncee respectee que si ses labels
    ont ete **lus** (point 7 du coordinateur, c3271), et un brouillon doit
    etre identifiable pour etre mis a part (point 3 du message de 22:46Z).

    LECTURE STRICTE (c3272) : un champ **absent** ou **mal forme** est un
    refus (`LectureIncomplete`), jamais une valeur par defaut. L'ancien
    comportement transformait des `labels` absents ou mal formes en `[]`, et
    un `draft` absent en `False` : une reponse **cassee** se lisait « pas de
    derogation, pas un brouillon », c'est-a-dire deux **faits** affirmes sur
    une lecture qui n'avait pas eu lieu. `labels_lus` ne vaut `True` que si
    les labels ont ete **reellement lus**.

    Meme exigence pour `state` (reserve du coordinateur du 19/11 01:32Z) : un
    `state` absent est une **lecture incomplete** (refus), jamais « ouverte ».
    C'est le meme piege : une reponse cassee ne vaut pas un etat par defaut.
    """
    payload = gh_json("repos/{}/pulls/{}".format(repo, number))
    if not isinstance(payload, dict):
        raise LectureIncomplete("PR {} : charge utile illisible".format(number))
    head = payload.get("head")
    if not isinstance(head, dict) or not head.get("sha"):
        raise LectureIncomplete(
            "PR {} : tete absente de la reponse".format(number))
    if "labels" not in payload:
        raise LectureIncomplete(
            "PR {} : champ `labels` absent de la reponse".format(number))
    labels = payload["labels"]
    if not isinstance(labels, list):
        raise LectureIncomplete(
            "PR {} : `labels` n'est pas une liste".format(number))
    noms: list[str] = []
    for l in labels:
        if not isinstance(l, dict) or "name" not in l:
            raise LectureIncomplete(
                "PR {} : `labels` mal forme (element sans `name`)".format(number))
        noms.append(str(l["name"]))
    if "draft" not in payload:
        raise LectureIncomplete(
            "PR {} : champ `draft` absent de la reponse".format(number))
    draft = payload["draft"]
    if not isinstance(draft, bool):
        raise LectureIncomplete(
            "PR {} : `draft` n'est pas un booleen".format(number))
    if "state" not in payload:
        raise LectureIncomplete(
            "PR {} : champ `state` absent de la reponse".format(number))
    state = payload["state"]
    if not isinstance(state, str) or not state:
        raise LectureIncomplete(
            "PR {} : `state` n'est pas une chaine".format(number))
    return {
        "sha": str(head["sha"]),
        "labels": noms,
        "labels_lus": True,
        "draft": draft,
        "state": state,
    }


def gate_check_run(repo: str, sha: str, per_page: int = 100,
                  max_pages: int = 20) -> dict | None:
    """La check-run `PR gate` la plus recente, ou ``None`` s'il n'y en a pas.

    CORRECTION c3271 (point 2 du coordinateur) : la lecture ne se limitait pas
    a la premiere page. Au-dela de 100 check-runs sur une tete, la liste est
    **tronquee** et la jambe `PR gate` peut ne pas y etre : decider sur une
    lecture partielle reviendrait a decider sur une absence, et « pas de
    check-run trouve » n'est **pas** une absence.

    CORRECTION c3272 : ce refus est desormais explicite.
      - une `check_runs` de forme invalide (absente, ou pas une liste) est
        une **lecture cassee** -- elle ne se lit plus « aucune check-run » ;
      - le **plafond de pagination** atteint est une liste tronquee.
    Les deux lèvent `LectureIncomplete` : aucun verdict n'est tire.
    """
    runs: list[dict] = []
    page = 1
    while True:
        payload = gh_json(
            "repos/{}/commits/{}/check-runs?per_page={}&page={}".format(
                repo, sha, per_page, page))
        if not isinstance(payload, dict):
            raise LectureIncomplete(
                "check-runs illisibles pour {}".format(sha))
        if "check_runs" not in payload:
            raise LectureIncomplete(
                "check-runs de forme invalide pour {} : champ `check_runs` "
                "absent".format(sha))
        chunk = payload["check_runs"]
        if not isinstance(chunk, list):
            raise LectureIncomplete(
                "check-runs de forme invalide pour {} : `check_runs` n'est "
                "pas une liste".format(sha))
        for r in chunk:
            if not isinstance(r, dict):
                raise LectureIncomplete(
                    "check-runs de forme invalide pour {} : element non "
                    "objet".format(sha))
            runs.append(r)
        if len(chunk) < per_page:
            break
        page += 1
        if page > max_pages:
            raise LectureIncomplete(
                "plafond de pagination des check-runs atteint ({} pages) pour "
                "{} -- lecture tronquee, aucune decision prise".format(
                    max_pages, sha))
    gates = [r for r in runs if r.get("name") == GATE_NAME]
    if not gates:
        return None
    gates.sort(key=lambda r: (r.get("started_at") or "", r.get("id") or 0))
    return gates[-1]


def job_ref(details_url: str) -> tuple[str, str] | None:
    """(run_id, job_id) deduits de l'URL de la check-run."""
    match = re.search(r"/actions/runs/(\d+)/job/(\d+)", details_url or "")
    if not match:
        return None
    return match.group(1), match.group(2)


def gh_rerun(run_id: str, job_id: str, repo: str = REPO_DEFAULT) -> tuple[int, str]:
    """Rejoue une jambe. `--repo` est **explicite** (c3271, point 3).

    Sans `--repo`, `gh run rerun` agit sur le depot du **repertoire courant**
    de l'appelant : l'organe pouvait rejouer un run d'un autre depot -- ou
    echouer sur un depot sans ce run -- alors qu'il mesure un repo donne.
    """
    completed = subprocess.run(
        ["gh", "run", "rerun", run_id, "--job", job_id, "--repo", repo],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False,
    )
    return completed.returncode, (completed.stderr or completed.stdout or "").strip()


def verifie_fraicheur(inventaire: dict, frais: dict | None) -> tuple[bool, str]:
    """Le geste ne part que si l'etat **relu au moment du geste** est celui
    de l'inventaire. Fonction PURE.

    Exigence du coordinateur (reserve du 19/11 01:32Z, #27273) : « verifier
    aussi la tete, le statut de la PR et le controle selectionne avant le
    geste si la premiere lecture a vieilli ».

    Pourquoi c'est un garde, pas une precaution : `--all` liste les PRs puis
    agit. Entre la liste et le geste, une PR peut etre **poussee** (nouvelle
    tete : le minuteur porte sur l'ancienne, son plancher a change), **fermee**
    (plus rien a rejouer), ou sa jambe `PR gate` peut etre **rejouee par un
    tiers** (le controle selection n'est plus celui qu'on a lu). Dans les
    trois cas, le rejeu partirait sur une **decision perimee** : c'est le
    geste qu'on ne veut pas faire, et il est irreversible (un run part).

    Fail-CLOSED : une relecture impossible (pas de `frais`) **refuse** le
    geste ; elle ne vaut jamais « rien n'a change ».
    """
    if not frais:
        return False, ("relecture impossible avant le geste -- geste refuse "
                       "(fail-CLOSED)")
    sha_inv = inventaire.get("head_sha") or ""
    sha_frais = frais.get("sha") or ""
    if sha_frais != sha_inv:
        return False, ("tete changee depuis l'inventaire (`{}` -> `{}`) -- "
                       "geste refuse".format(sha_inv[:9], sha_frais[:9]))
    state = frais.get("state") or ""
    if state != "open":
        return False, ("PR fermee depuis l'inventaire (state=`{}`) -- geste "
                       "refuse".format(state or "absent"))
    # Le BROUILLON et la DEROGATION sont **relus**, et refuses s'ils sont
    # atteints : `decide` les exclut par construction (un brouillon n'est pas
    # mergeable ; une dispense n'est pas soumise au minuteur). La relecture
    # les relit parce qu'une PR peut les ATTEINDRE entre l'inventaire et le
    # geste -- et le geste, lui, est irreversible.
    # Fail-CLOSED : un etat relu qui ne porte pas ces champs ne prouve rien.
    for cle, phrase in (("draft", "PR devenue brouillon"),
                        ("derogation", "PR devenue dispensee (label)")):
        if cle not in frais:
            return False, ("etat relu sans le champ `{}` -- geste refuse "
                           "(fail-CLOSED)".format(cle))
        if cle not in inventaire:
            return False, ("inventaire sans le champ `{}` -- geste refuse "
                           "(fail-CLOSED)".format(cle))
        if frais[cle]:
            return False, ("{} depuis l'inventaire -- geste refuse (le rejeu "
                           "ne porte ni sur un brouillon ni sur une "
                           "dispense)".format(phrase))
        if bool(inventaire[cle]) != bool(frais[cle]):
            return False, ("etat `{}` change depuis l'inventaire -- geste "
                           "refuse".format(cle))
    gate_inv = inventaire.get("gate_id")
    gate_frais = frais.get("gate_id")
    if not gate_inv or not gate_frais:
        # Un identifiant de controle **absent d'un seul cote** ne prouve pas
        # que le controle relu est celui de l'inventaire : c'est un identifiant
        # non prouve, pas une egalite. Fail-CLOSED.
        return False, ("identifiant de controle `{}` absent d'un des deux "
                       "cotes (inventaire={}, relecture={}) -- geste refuse "
                       "(fail-CLOSED)".format(GATE_NAME, gate_inv, gate_frais))
    if gate_inv != gate_frais:
        return False, ("controle `{}` change depuis l'inventaire -- geste "
                       "refuse".format(GATE_NAME))
    status = frais.get("status") or ""
    if status != "completed":
        return False, ("jambe terminee ? statut `{}` -- geste refuse".format(
            status or "absent"))
    conclusion = frais.get("conclusion") or ""
    if conclusion != "failure":
        return False, ("jambe plus en echec (conclusion `{}`) -- geste "
                       "refuse".format(conclusion or "absente"))
    return True, "etat relu identique -- geste autorise"


def relit_etat(repo: str, number: int) -> dict:
    """Relit la PR et son controle `PR gate` **au moment du geste**.

    Renvoie `{}` si la lecture est cassee : l'appelant treat alors comme un
    refus (fail-CLOSED), jamais comme un etat favorable.

    Le `draft` et la derogation sont **relus et rendus** : sans eux, la
    relecture ne prouverait pas que la PR est encore rejouable (une PR peut
    devenir brouillon, ou gagner le label de derogation, entre l'inventaire
    et le geste).
    """
    try:
        info = pr_info(repo, number)
        gate = gate_check_run(repo, info["sha"]) or {}
    except (LectureIncomplete, RuntimeError):
        return {}
    return {
        "sha": info["sha"],
        "state": info["state"],
        "gate_id": gate.get("id"),
        "status": gate.get("status") or "",
        "conclusion": gate.get("conclusion") or "",
        # Le BROUILLON et la DEROGATION sont RELUS, pas jetes : sans eux, la
        # relecture ne prouve pas que la PR est encore rejouable (une PR peut
        # devenir brouillon entre l'inventaire et le geste).
        "draft": info["draft"],
        "derogation": WAIVER_LABEL in info["labels"],
        "labels_lus": True,
    }


# --------------------------------------------------------------------------
# Collecte
# --------------------------------------------------------------------------

def inspect_pr(repo: str, number: int, now: datetime,
                dwell_min: float = DEFAULT_DWELL_MIN) -> dict:
    """Etat d'une PR pour le minuteur DWELL (lecture seule)."""
    entry: dict = {"pr": number, "action": "ignorer", "motif": ""}
    info = pr_info(repo, number)
    sha = info["sha"]
    entry["head_sha"] = sha
    entry["draft"] = info["draft"]
    entry["state"] = info["state"]
    # `labels_lus` ne vaut True que si les labels ont ete REELLEMENT lus :
    # `pr_info` refuse (Lever) une reponse dont les labels sont absents ou
    # mal formes (c3272).
    entry["labels_lus"] = bool(info.get("labels_lus"))
    # Une lecture cassee ou tronquee leve `LectureIncomplete` : elle se
    # propage jusqu'a `main`, qui refuse de decider (action `incomplet`).
    gate = gate_check_run(repo, sha)
    if gate is None:
        entry["motif"] = "aucune check-run `{}` sur cette tete".format(GATE_NAME)
        return entry
    title = (gate.get("output") or {}).get("title") or ""
    conclusion = gate.get("conclusion") or ""
    status = gate.get("status") or ""
    entry["conclusion"] = conclusion
    entry["status"] = status
    entry["gate_title"] = title[:200]
    entry["gate_id"] = gate.get("id")
    committed_at = head_committed_at(repo, sha)
    entry["committed_at"] = committed_at.strftime("%Y-%m-%dT%H:%M:%SZ")
    # Plancher de l'EMETTEUR (lu dans le message), et non recalcule : les deux
    # peuvent diverger apres un `update-branch` sans conflit.
    plancher = emitter_floor(title)
    if plancher is not None:
        floor, head_at, dwell_reel = plancher
        entry["head_at_emetteur"] = head_at.strftime("%Y-%m-%dT%H:%M:%SZ")
        entry["dwell_min_emetteur"] = dwell_reel
        entry["floor"] = floor.strftime("%Y-%m-%dT%H:%M:%SZ")
    else:
        entry["floor"] = dwell_floor(committed_at, dwell_min).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
    # Derogation : annoncee seulement si les labels ont ete LUS (ils viennent
    # de la meme charge utile que la tete).
    waived = WAIVER_LABEL in info["labels"]
    entry["derogation"] = waived
    action, motif = decide(conclusion=conclusion, title=title,
                           committed_at=committed_at, now=now, dwell_min=dwell_min,
                           status=status, waived=waived, draft=info["draft"],
                           state=info["state"])
    entry["action"] = action
    entry["motif"] = motif
    ref = job_ref(gate.get("details_url") or "")
    if ref:
        entry["run_id"], entry["job_id"] = ref
    return entry


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=REPO_DEFAULT)
    ap.add_argument("--pr", nargs="*", type=int, default=None,
                    help="numeros de PR a examiner (defaut : aucune)")
    ap.add_argument("--all", action="store_true",
                    help="examine toutes les PR ouvertes du depot")
    ap.add_argument("--apply", action="store_true",
                    help="rejoue reellement (defaut : lecture seule)")
    ap.add_argument("--dwell-min", type=float, default=DEFAULT_DWELL_MIN)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.all:
        try:
            numbers = open_pr_numbers(args.repo)
        except LectureIncomplete as exc:
            # Inventaire tronque : aucune conclusion tiree (c3272).
            if args.json:
                print(json.dumps({"repos": args.repo, "apply": args.apply,
                                  "rc": 2, "echecs": 0, "incomplets": 1,
                                  "brouillons": 0, "compteurs": {},
                                  "prs": [{"pr": 0, "action": "incomplet",
                                           "motif": str(exc)}]},
                                 ensure_ascii=False, indent=2))
            else:
                print("inventaire incomplet : {}".format(exc))
            return 2
    else:
        numbers = list(args.pr or [])
    if not numbers:
        ap.error("rien a examiner : --pr N... ou --all")

    now = datetime.now(timezone.utc)
    entries: list[dict] = []
    echecs = 0            # geste rate (rejeu refuse) ou PR illisible
    incomplets = 0        # lecture incomplete -> aucune decision possible
    for number in numbers:
        try:
            entry = inspect_pr(args.repo, number, now, args.dwell_min)
        except LectureIncomplete as exc:
            # Lecture cassee ou tronquee : REFUS de decider (c3272). Ce n'est
            # pas un echec de geste (rc 1) : c'est un inventaire incomplet
            # (rc 2), et la distinction se lit dans le rc de sortie.
            entry = {"pr": number, "action": "incomplet",
                     "motif": "lecture incomplete -- {}".format(exc),
                     "draft": False, "labels_lus": False}
            incomplets += 1
        except RuntimeError as exc:
            entry = {"pr": number, "action": "erreur", "motif": "erreur: {}".format(exc)}
            echecs += 1
        if args.apply and entry.get("action") == "rejouer":
            run_id, job_id = entry.get("run_id"), entry.get("job_id")
            if not run_id or not job_id:
                entry["motif"] = "run/job introuvables : {}".format(
                    entry.get("gate_title", "")[:80])
                entry["rerun_rc"] = 1
                echecs += 1
            else:
                frais = relit_etat(args.repo, number)
                ok, motif_fraicheur = verifie_fraicheur(entry, frais)
                if not ok:
                    entry["motif"] = motif_fraicheur
                    entry["rerun_rc"] = 1
                    echecs += 1
                else:
                    rc, out = gh_rerun(run_id, job_id, args.repo)
                    entry["rerun_rc"] = rc
                    entry["rerun_sortie"] = out[:200]
                    if rc != 0:
                        entry["motif"] = "rejeu refuse : {}".format(out[:160])
                        echecs += 1
        entries.append(entry)

    counts: dict[str, int] = {}
    for entry in entries:
        counts[entry["action"]] = counts.get(entry["action"], 0) + 1
    brouillons = sum(1 for e in entries if e.get("draft"))
    # Un rejeu refuse doit etre **visible** par le consommateur : l'organe
    # sortait 0 meme apres un echec du geste (c3271, point 4). Ici :
    #   0 = lecture seule, ou tous les gestes tentes ont reussi ;
    #   1 = au moins un geste rate (rejeu refuse) ;
    #   2 = inventaire incomplet (PR illisible ou couverture tronquee).
    rc_final = 1 if echecs else (2 if incomplets else 0)
    if args.json:
        print(json.dumps({"repos": args.repo, "apply": args.apply,
                          "rc": rc_final, "echecs": echecs,
                          "incomplets": incomplets, "brouillons": brouillons,
                          "compteurs": counts, "prs": entries},
                         ensure_ascii=False, indent=2))
    else:
        for entry in entries:
            print("#{} [{}] {}".format(entry["pr"], entry["action"], entry["motif"]))
        print("compteurs: {} (brouillons: {})".format(counts, brouillons))
    return rc_final


if __name__ == "__main__":
    sys.exit(main())
