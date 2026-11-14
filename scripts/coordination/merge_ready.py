#!/usr/bin/env python3
r"""Organe merge_ready -- fusion hors cycle des PRs prevalidees (Q40, 2026-09-22).

Mandat (sign-off user 2026-09-22, registre Q40 option b) : les merges ne
doivent plus attendre le cycle de 2 h du coordinateur. Mesure fondatrice :
97 merges en 24 h concentres sur 4 creneaux avec 12 heures vides ; lead time
median d'une PR 28,5 h ; sur un echantillon de 20 PRs dont le dossier
d'adjoint etait rejete par le gate, 14 avaient une tete perimee et 13 une
discussion ayant bouge APRES le dossier, 0 un refus de fond. Un dossier
perit pendant qu'il attend le coordinateur.

Arbitrage user 2026-09-28 (Q67, option a) : l'organe ne merge QUE ce que le
coordinateur a LU et APPROUVE. Il ne remplace pas cette lecture ; il evite
seulement qu'un dossier perisse entre elle et le merge. Jusque-la, la
disposition de review n'etait que relevee : sur les 211 merges du journal
(23/09 -> 28/09), 6 portaient une approbation ``myia-ai-01``, et toute lane
ne portant pas la PR pouvait la faire merger par son seul dossier.

Arbitrage user 2026-10-19 (Q131) : les grains DEEP et les PRs hors flotte de
la session cloud (branche ``claude/*``, sans tag ``Grain:``) entrent dans le
perimetre, a la meme condition que toutes les autres : l'approbation
prealable du coordinateur (etape 2ter). L'organe ne merge rien que le
coordinateur n'a pas valide au prealable.

Retrait du dossier (2026-11-05, mandat user) : « On fait de la paperasse
pour faire de la paperasse, et au lieu d'accélérer ton travail, tous ces
tokens dépensés le ralentissent considérablement. » Mesure sur 24 h :
117 dossiers ``[ADJOINT PREFLIGHT]`` poses pour 96 PRs, dont 21 re-tampons
sur 13 PRs -- le dossier meurt a chaque changement de tete ou de discussion,
puis il est re-tamponne sans fin. Le dossier n'est plus une condition
d'entree : chaque fait qu'il attestait est revifie EN DIRECT au moment du
merge (approbation du coordinateur, organe B.0, collisions twin et slot,
base et piles declarees, arbre fusionne, ``mergeable_state`` et tete
inchangee), et la lecture qu'il documentait appartient a l'approbation du
coordinateur, qui seule gouverne le merge. Seule la porte STACK du gate
survit, appelee en processus (etape 3) : c'est le seul apport du gate
qu'aucune autre etape ne couvrait.

L'organe est deterministe et tourne sous l'identite coordinateur
(myia-ai-01) toutes les ~20 minutes, et seulement en perimetre (b) -- hors
harnais. Tour de controle par PR, TOUT doit tenir sinon skip avec raison
nommee :

1. pas un brouillon ;
2. perimetre (b) fail-closed : aucun fichier sous ``.claude/``, aucun
   ``CLAUDE.md`` (n'importe quel repertoire), aucun fichier sous
   ``.github/`` ; tier du tag ``Grain:`` DEEP, MED ou LIGHT (tier illisible
   refuse, sauf branche hors flotte ``claude/*`` qui n'a pas de tag, Q131)
   -- lecture par le parseur PARTAGE
   ``scripts/grain_tag.py`` (#9485, meme lecteur que variation_light_cap
   et le guard CI), jamais une regex locale ; liste de fichiers TRONQUEE
   (``changedFiles`` > fichiers listes, ou absent) -> skip fail-closed,
   un fichier harnais non liste ne doit pas passer ; PR qui se reclame
   (titre ou body) d'un parapluie GELE par un veto user
   (``FROZEN_UMBRELLAS``) -> skip ;
2ter. approbation du coordinateur : la DERNIERE voix de ``myia-ai-01``
   (etat reel ``APPROVED``/``CHANGES_REQUESTED``, ou verdict type en
   corps -- latest-wins, ``DISMISSED`` jamais) est un ``APPROVED`` reel,
   et elle couvre le CONTENU de la tete : soit elle est posee sur la tete
   elle-meme, soit la tete n'en differe que par des rafraichissements de
   base PROUVES content-free (``merge_dwell.last_authoritative_sha``, la
   remontee du plancher DWELL : un ``update-branch`` sans conflit ne
   perime pas la lecture, une resolution de conflit ou un commit de
   contenu la perime). Absente -> ``no-coordinator-approval`` ; perimee
   -> ``coordinator-approval-stale`` ; preuve illisible ->
   ``coordinator-approval-unverifiable`` (fail-closed). Controle place
   AVANT la porte STACK : une PR non lue ne paie pas l'index de pile ;
3. porte STACK (#20251), EN PROCESSUS via le module du gate
   (``check_adjoint_prevalidation`` importe, jamais un sous-processus) :
   ``gate.default_stack_index()`` construit et met en cache l'index des
   piles des PRs ouvertes ; ``gate.stack_reasons(pr, index)`` rend une
   raison par PR partenaire ouverte dont la tete porte des corrections
   absentes ici (sommet de pile perime) -> skip ``stack-top:<parente>`` ;
   index illisible (``None``) -> fail-open assume (convention UNKNOWN !=
   rouge forge), etat ``unmeasured`` journalise avec ses incidents ;
4. organe B.0 ``check_unaddressed_nits.py <PR>`` exit 0 -- code de
   retour capture DIRECTEMENT (subprocess.returncode, jamais a travers
   un pipe) ;
5bis. si la PR touche ``scripts/notebook_tools/twin_pairs.d/`` : organe
   ``check_twin_index_collisions.py --base origin/main --head <tete>``
   exit 0, apres ``git fetch origin main pull/<N>/head``. Deux PRs au
   meme index sont chacune CLEAN contre ``main`` ; la seconde fait
   rougir ``main`` des que la premiere est mergee. La relecture a lieu
   PR par PR, contre le ``main`` du moment, donc apres les merges deja
   faits dans ce run. Collision -> skip ; fetch ou organe illisible ->
   skip fail-closed ;
5quinquies. organe ``premerge_combined_check.py --pr <N> --head <tete>``
   exit 0 : les tests d'integrite du depot (registres, inventaires,
   index) joues sur l'ARBRE FUSIONNE ``main`` du moment + tete. Mesure du
   2026-11-05 : ``main`` rouge ~18 h sur 30, chaque episode ouvert par une
   PR verte a sa propre tete et rouge une fois combinee a ce qui avait ete
   merge entretemps. Rouge -> ``combined-tree-red:<test>`` ; conflit ->
   ``combined-tree-conflict`` ; illisible -> ``combined-tree-unreadable``
   (fail-closed). ~1 min par PR qui atteint cette etape. Retrait
   operateur : ``MERGE_READY_COMBINED_CHECK=0`` ;
6. REST ``repos/jsboige/CoursIA/pulls/<N>`` : ``mergeable_state`` ==
   ``clean`` (jusqu'a 12 relectures a 10 s d'intervalle pendant ``unknown`` --
   apres un merge les PRs soeurs passent ``unknown``), et ``head.sha``
   identique a la tete de la vue, celle que l'approbation couvre ;
7. merge ``gh pr merge <N> --repo jsboige/CoursIA --squash
   --match-head-commit <sha>`` -- jamais ``--delete-branch``, jamais
   ``--admin``.

Comportement :
- DRY-RUN par defaut (imprime ce qui serait merge et pourquoi chaque
  autre PR est skippee) ; ``--apply`` merge reellement. ``--max N``
  (defaut 15) plafonne les merges par run (disjoncteur). Une erreur
  inattendue ATTRIBUABLE A UNE PR (reponse d'outil illisible, rc hors
  contrat pour cette seule PR) est journalisee ``run-error`` pour elle et
  le balayage CONTINUE (#17672 point 3 : une PR bizarre ne gele plus
  l'evaluation des suivantes) ; une erreur de PORTEE GENERALE -- jeton
  refuse, quota d'API, reseau injoignable, cf ``PASS_WIDE_ERROR_MARKERS``
  -- ARRETE le run, car la repeter sur chaque PR restante ne dirait rien
  de plus. ``rc=1`` est rendu des qu'une PR a erreur, isolee ou non, et le
  bilan nomme leur nombre. Jamais de merge en aveugle.
- Jeton : chaque sous-processus gh recoit ``GH_TOKEN`` epingle depuis
  ``gh auth token --user myia-ai-01``, resolu UNE fois au depart ;
  jamais ``gh auth switch``. Jeton irresolu -> exit 2.
- Ordre : PR la plus ancienne d'abord (par numero).
- Retenues : ``hold.txt`` a cote du journal (surchargeable
  ``--hold-file``), une PR par ligne -- ``<numero> [motif]`` ; lignes
  vides et commentaires ``# ...`` ignores. La sentinelle reserve le numero
  0 pour l'etat de ``Scripts Tests (CPU)`` sur ``main`` : ``failure`` ->
  retenue globale, ``success`` -> retrait de sa seule ligne. Le verdict
  juge est celui du **dernier commit de ``main`` qui porte un verdict
  TERMINE** de ce check : un check en cours, une annulation ou un
  ``timed_out`` ne sont pas des regressions, le verdict remonte au commit
  precedent ; au-dela de 20 commits sans verdict termine, refus fail-closed
  (borne ecrite). Une PR listee est
  sautee (``hold:<motif>``) AVANT tout appel gh. Fichier absent = aucune
  retenue utilisateur ; fichier illisible ou ligne malformee -> exit 2 (on
  ne merge pas sans savoir ce qui est retenu).
- **Qui merge le correctif d'un ``main`` rouge** : la retenue globale saute
  aussi la PR qui repare le rouge. Cette PR est donc mergee **a la main par
  le coordinateur** (``myia-ai-01``), qui retire ensuite la retenue :
  ``python scripts/coordination/merge_ready.py --clear-main-red-hold
  --hold-file <chemin>`` -- la commande ne touche que la ligne de la
  sentinelle, jamais les retenues du coordinateur. Le chemin vert la retire
  de lui-meme au run suivant, si ce run a lieu avant le correctif.
- Review : deux lectures distinctes. La disposition journalisee (champ
  ``review``) est CLASSEE a la tete que la ligne declare
  (``approved-exact-head`` / ``approval-not-on-head`` / ``no-approval``,
  point 1 de #17672) sur TOUTES les voix, bots compris ; elle informe.
  Ce qui BLOQUE est l'etape 2ter : la seule voix du coordinateur.
  Une quatrieme valeur, ``review-ready`` (point 2 de #17672), signale
  les PRs qui ont franchi TOUTES les portes delegables (perimetre, tag
  Grain, parapluie gele) et n'attendent que la relecture
  coordinateur -- le dashboard les distingue des PRs bloquees sur
  un autre probleme.
- Journal : une ligne JSON par PR evaluee (ts UTC en Z, pr, head,
  verdict, reason, merged, review, stack, plus stack_incidents quand la
  porte STACK en a publie) dans
  ``%LOCALAPPDATA%/CoursIA/merge_ready/journal.jsonl`` (surchargeable
  ``--journal``), plus un resume humain sur stdout ; ``--json`` pour la
  sortie machine. ``stack`` nomme l'etat de la porte STACK mesuree en
  processus (#22005) : ``measured`` | ``unmeasured`` ; ``null`` = la
  porte n'a pas ete atteinte (skip en amont). Un would-merge dont la
  porte n'a pas ete mesuree est signale comme tel dans
  le resume humain (#22066), sans changer la decision de merge.
- Codes de sortie : 0 run termine (merge ou non) ; 1 arret sur erreur
  inattendue ; 2 impossible de demarrer (jeton/env).

Tous les sous-processus passent par un runner injectable -- la logique
est testable sans reseau (scripts/tests/test_merge_ready.py).
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol

# Les modules partages vivent dans scripts/ : grain_tag.py est LE lecteur du
# tag Grain (un seul lecteur depuis #9485, meme discipline que
# variation_light_cap.py) et check_adjoint_prevalidation.py porte la porte
# STACK (index des piles, #20251) -- la seule part du gate que l'organe
# appelle encore, en processus. L'organe ne re-ecrit NI la grammaire du tag
# NI le predicat de pile.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
COORDINATION_DIR = Path(__file__).resolve().parent
for _shared_dir in (SCRIPTS_DIR, COORDINATION_DIR):
    if str(_shared_dir) not in sys.path:
        sys.path.insert(0, str(_shared_dir))

from grain_tag import TIERS, parse_grain_tag  # noqa: E402
import check_adjoint_prevalidation as gate  # noqa: E402
# Les campagnes gelees par veto user (#17040) ont une definition PARTAGEE avec
# le gate (scripts/coordination/frozen_campaigns.py) : le gate ne peut pas
# importer cet organe (cet organe importe deja le gate), les deux importent
# le module -- un seul lecteur, meme discipline que grain_tag.
from frozen_campaigns import (  # noqa: E402,F401
    FROZEN_BRANCH_PREFIXES,
    FROZEN_UMBRELLAS,
    frozen_umbrella_exclusion,
)

# Le canon d'emission du verdict de review vit dans scripts/ci/ : le jeton de
# review du cluster ne peut poster que des COMMENT (#16926), donc le verdict
# reel s'ecrit ``VERDICT: <token>`` dans le CORPS de la voix. Importe, jamais
# recopie -- une regex locale divergerait en silence du canon qui gouverne le
# triage du pool.
# Le format de l'attestation de `lake build` local (#24989) vit dans
# scripts/lean/ : l'organe qui l'ECRIT (attest_local_build.py) et la garde
# qui la LIT ne doivent pas pouvoir diverger en silence. Un seul lecteur du
# format, meme discipline que grain_tag et merge_dwell. Le repertoire est
# ajoute AVANT scripts/ci pour que scripts/ci reste en priorite de resolution.
LEAN_DIR = SCRIPTS_DIR / "lean"
if str(LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(LEAN_DIR))

CI_DIR = SCRIPTS_DIR / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import pool_review_verdicts as review_canon  # noqa: E402
# La remontee first-parent qui saute les rafraichissements de base PROUVES
# content-free est celle du plancher DWELL (#16149) : importee, pas recopiee,
# pour que « la lecture du coordinateur couvre-t-elle encore cette tete ? » et
# « depuis quand le contenu n'a-t-il pas bouge ? » ne divergent jamais.
import merge_dwell  # noqa: E402
# Le format de l'attestation de build Lean local (#24989) : un seul lecteur,
# partage avec l'organe qui ecrit l'attestation.
import lean_build_attestation  # noqa: E402
# Le pli des jambes de check (#25059) : le fold CANONIQUE est
# scripts/pr_gate.py::dedupe_latest -- celui du gate lui-meme -- et la
# normalisation d'une jambe (check-run REST ou entree de rollup) est celle de
# scripts/check_run_state.py. Importes, jamais recopiés : une seconde
# implementation du pli divergerait en silence de celle qui gouverne le gate,
# et c'est exactement le defaut que #25059 veut fermer (l'organe qui l'a
# remplace n'a pas repris le pli de la chaine v9).
import pr_gate  # noqa: E402
import check_run_state  # noqa: E402
# #17437 : normalisation de l'auteur d'une review (orthographe REST des
# identites App) -- source unique de la forme canonique, jamais recopiee.
import gh_identity  # noqa: E402

REPO = "jsboige/CoursIA"
COORDINATOR_USER = "myia-ai-01"
# La voix du coordinateur : le login humain SEUL. L'App ``coursia-lane-ai-01``
# n'en fait PAS partie (arbitrage ai-01 2026-11-13, portee par ce module).
#
# Sa cle privee vit sur la machine ai-01, dans le clone du depot
# (``.secrets/github-apps/coursia-lane-ai-01.pem``, cf
# ``scripts/secrets/github_app_manifest.KEY_DIR``). La machine porte DEUX
# lanes : ``myia-ai-01:CoursIA`` (le coordinateur) et ``myia-ai-01:CoursIA-2``
# (la lane worker sœur). La seconde lit le meme fichier et forge donc le meme
# jeton d'installation : compter cette App comme voix du coordinateur
# ouvrirait la porte Q131 a une lane non coordinatrice -- une APPROVE ou un
# ``[OVERRIDE]`` de CoursIA-2 vaudrait ceux du coordinateur. Une App PROPRE a
# la lane coordinateur est le prealable ; une App nommee par machine ne le
# remplace pas.
#
# Le mecanisme de preuve d'identite reste en place (``_voice_login`` /
# ``_typed_reviews``) : la preuve est le TYPE porte par la ligne, jamais une
# sonde ``users/<login>[bot]``. Il sert la voix humaine et refuse toute forme
# App ; le jour ou une App de lane coordinateur existe, elle s'ajoute ici par
# une edition consciente, accompagnee de sa cle dediee.
COORDINATOR_VOICES = frozenset((COORDINATOR_USER,))
NITS_PATH = SCRIPTS_DIR / "check_unaddressed_nits.py"
TWIN_PATH = SCRIPTS_DIR / "notebook_tools" / "check_twin_index_collisions.py"
TWIN_CLAIMS_PATH = SCRIPTS_DIR / "notebook_tools" / "twin_open_claims.py"
TWIN_REGISTRY_PREFIX = "scripts/notebook_tools/twin_pairs.d/"
# Issue #20774 : au merge, le slot-reservation-guard doit lire la source
# `open_prs` (mode en ligne) pour qu'une collision cross-PR rougisse avant
# le merge. La voie rapide continue de l'appeler en `--offline` (pas de
# `gh` reseau) -- ici on dispose de `gh`, on en sert.
SLOT_PATH = SCRIPTS_DIR / "notebook_tools" / "check_slot_reservation.py"
SLOT_NOTEBOOK_PREFIX = "MyIA.AI.Notebooks/"
SLOT_RESERVATIONS_PATH = SCRIPTS_DIR / "notebook_tools" / "slot_reservations.json"
# Etape 5quinquies : tests d'integrite joues sur l'arbre fusionne (2026-11-05).
COMBINED_PATH = SCRIPTS_DIR / "coordination" / "premerge_combined_check.py"
COMBINED_DISABLE_ENV = "MERGE_READY_COMBINED_CHECK"
REPO_ROOT = SCRIPTS_DIR.parent


def _repo_relative(path: Path) -> str:
    """Chemin d'organe RELATIF au depot, pour l'argv des sous-processus.

    #26102 (repro ai-01 2026-11-13) : les argv absolus embarquent le chemin
    du worktree de la machine. Un worktree nomme pour une PR (p. ex.
    ``CoursIA-26102``) fait alors tripper toute assertion qui cherche le
    NUMERO d'une autre PR dans les commandes enregistrees, et le journal
    d'un meme run differe d'une machine a l'autre. Le couplage est double :
    argv relatifs ici + ``cwd=REPO_ROOT`` epingle dans
    ``SubprocessRunner.run`` -- les organes appeles resolvent leurs propres
    chemins depuis ``__file__`` ou le cwd, jamais depuis cet argv.
    Forme canonique en barres obliques (``as_posix``) : l'argv est identique
    sous Windows et POSIX -- Python accepte les deux sur les deux OS.
    """
    return path.relative_to(REPO_ROOT).as_posix()

# Parapluies et branches de campagne GELES par un veto user, exemption des
# redressements comprise : definition et historique portes par le module
# PARTAGE scripts/coordination/frozen_campaigns.py (importe ci-dessus -- les
# noms restent des attributs de cet organe pour ses appelants et ses tests).

# Codes de retour DOCUMENTES des organes appeles. Tout autre rc est une
# erreur inattendue -> arret du run, jamais de merge en aveugle.
NITS_DOCUMENTED_RC = frozenset({0, 1})  # clear / blocked
# Issue #20774 : 0 = tous les slots libres, 1 = collision, 2 = lecture impossible.
# Tout autre rc est inattendu -> arret du run, comme les autres organes.
SLOT_DOCUMENTED_RC = frozenset({0, 1, 2})  # clear / collision / unreadable

# --- disposition de review classsee a la tete evaluee (point 1 de #17672) ------
# Le dossier HACHE l'oid de chaque review dans son empreinte
# (``check_adjoint_prevalidation._fingerprint_payload``) sans le CLASSER : rien
# ne dit si l'approbation porte sur le commit qui va etre merge. Trois etats,
# toujours lus a la tete que la ligne de journal declare :
#   ``approved-exact-head``  une voix approbatrice gouverne CETTE tete ;
#   ``approval-not-on-head`` une approbation existe dans la fenetre lue, mais
#                            elle ne couvre pas la tete evaluee (tete avancee
#                            depuis l'approbation, ou voix posterieure qui n'approuve
#                            pas) ;
#   ``no-approval``          aucune approbation lue.
# Les deux surfaces du canon sont lues : l'etat REEL de l'API (APPROVED, quand un
# humain review) et le verdict type du CORPS en COMMENT -- la seule surface dont
# dispose le jeton du cluster. Lire la seule premiere classerait « sans
# approbation » des PR revues, le faux compte que #16926 a deja puni deux fois.
APPROVED_EXACT_HEAD = "approved-exact-head"
APPROVAL_NOT_ON_HEAD = "approval-not-on-head"
NO_APPROVAL = "no-approval"
NOT_EVALUATED = "not-evaluated"  # ligne d'un run interrompu avant evaluation
#: Disposition de la PR telle que la verrait l'organe si la lecture du
#: coordinateur etait reglee : perimetre, tag Grain et parapluie gele
#: sont verts, seule manque l'approbation du coordinateur a la tete
#: exacte. Sert au dashboard coordinateur a distinguer
#: « PR qui n'attend que sa relecture » de « PR qui a un autre probleme ».
#: Voir #17672 point 2.
REVIEW_READY = "review-ready"

#: Ce qui vaut approbation : l'etat REEL ``APPROVED``, ou le verdict type
#: ``LGTM`` emis en corps de voix (``VERDICT_RE`` du canon ne type que LGTM et
#: CONCERNS -- les deux etats reels suffisent au reste).
APPROVING_VOICES = frozenset({"APPROVED", "LGTM"})

MAX_MERGES_DEFAULT = 15
PR_LIST_LIMIT = 500  # le pool ouvert mesure ~220 PRs ; au-dela, ordre ancien d'abord
# Mesure du 2026-09-22 (22:15Z-22:45Z), merges en rafale sur la file vivante :
# avec 3 relectures espacees de 5 s, 5 PRs sur 20 restaient `unknown` et
# etaient sautees ; avec 12 relectures espacees de 10 s, les 11 suivantes
# (dont ces 5) sont toutes passees `clean` et ont ete mergees. Le plafond
# d'attente par PR (~2 min) reste petit devant le tour de 20 min.
MERGEABLE_RETRIES = 12
MERGEABLE_RETRY_SLEEP_S = 10.0


class CannotRunError(Exception):
    """Le run ne peut pas demarrer (jeton irresolu, env invalide)."""


class UnexpectedError(Exception):
    """Erreur inattendue d'un outil ou de l'API, non prevue par le contrat.

    Depuis #17672 (point 3), elle n'arrete plus le run par principe : le
    balayage distingue une erreur **attribuable a la PR** en cours (reponse
    illisible pour elle, rc hors contrat pour elle) -- journalisee
    ``run-error`` et le balayage continue -- d'une erreur de **portee
    generale** (jeton, quota, reseau), qui arrete tout (cf
    ``is_pass_wide``). Un ECHEC DE MERGE garde son propre disjoncteur
    (``MergeFailedError``) : il ne se confond pas avec ces deux cas.
    """


class MergeFailedError(Exception):
    """La commande de merge a echoue -- arret du run (disjoncteur)."""


# Marqueurs d'une erreur de PORTEE GENERALE : ce qui frappe tous les appels de
# la meme facon ne doit pas etre isole par PR, sinon une panne de jeton ou de
# quota se lit comme une collection de ``run-error`` attribuees a des PRs
# innocentes (#17672, point 3). Liste volontairement courte et litterale : un
# texte non reconnu fait ISOLER l'erreur (le balayage continue, rc=1, la PR
# est nommee), jamais l'inverse -- arreter le run sur un motif devine rendrait
# le balayage dependant d'une devinette.
PASS_WIDE_ERROR_MARKERS = (
    "bad credentials",
    "requires authentication",
    "rate limit",
    "http 401",
    "http 403",
    "could not resolve host",
    "no such host",
    "connection refused",
    "connection reset",
    "timed out",
)


def is_pass_wide(exc: BaseException) -> bool:
    """L'erreur frappe-t-elle TOUTE la passe (jeton, quota, reseau) ou une seule PR ?

    Le texte cherche est celui que les appels gh renseignent avec le stderr de
    l'outil (cf ``fetch_pr_view``), donc un refus d'authentification
    ou un quota epuise y figure tel que gh l'a ecrit.
    """
    text = str(exc).lower()
    return any(marker in text for marker in PASS_WIDE_ERROR_MARKERS)


# --- runner injectable --------------------------------------------------------


@dataclass(frozen=True)
class RunResult:
    returncode: int
    stdout: str
    stderr: str


class Runner(Protocol):
    """Contrat d'execution : un sous-processus capture, un sommeil."""

    def run(self, cmd: list[str], env: dict[str, str] | None = None) -> RunResult: ...

    def sleep(self, seconds: float) -> None: ...


class SubprocessRunner:
    """Runner reel : rc capture DIRECTEMENT (subprocess.returncode, jamais un pipe)."""

    def run(self, cmd: list[str], env: dict[str, str] | None = None) -> RunResult:
        # cwd epingle a la racine du depot : les argv d'organes sont RELATIFS
        # (cf. ``_repo_relative``) -- c'est ce qui les rend resolus ici, et le
        # journal independant du chemin du worktree de la machine.
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            env=env,
            cwd=REPO_ROOT,
        )
        return RunResult(proc.returncode, proc.stdout or "", proc.stderr or "")

    def sleep(self, seconds: float) -> None:
        time.sleep(seconds)


# --- petites pieces pures -----------------------------------------------------


@dataclass(frozen=True)
class PRVerdict:
    """Verdict terminal d'une PR pour ce run (forme de la ligne de journal)."""

    pr: int
    head: str | None
    verdict: str  # skipped | would-merge | merged | merge-failed | run-error
    reason: str | None
    merged: bool
    #: Disposition de review classee a ``head`` (point 1 de #17672) ; une ligne
    #: ecrite avant evaluation (erreur inattendue) porte ``not-evaluated``.
    review: str = NOT_EVALUATED
    #: Etat de la porte STACK mesuree en processus (#22005) :
    #: ``measured`` | ``unmeasured``. ``None`` = la porte n'a pas ete
    #: atteinte (skip en amont).
    stack: str | None = None
    #: Incidents de mesure de la porte STACK, quand la porte en a publie.
    stack_incidents: tuple[str, ...] | None = None

    def journal_dict(self) -> dict:
        row = {
            "ts": utc_now_iso(),
            "pr": self.pr,
            "head": self.head,
            "verdict": self.verdict,
            "reason": self.reason,
            "merged": self.merged,
            "review": self.review,
            "stack": self.stack,
        }
        if self.stack_incidents:
            row["stack_incidents"] = list(self.stack_incidents)
        return row


def utc_now_iso() -> str:
    """Horodatage UTC explicite, suffixe Z (jamais une heure locale nue)."""
    return _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def default_journal_path() -> Path:
    base = Path(os.environ.get("LOCALAPPDATA") or Path.home() / "AppData" / "Local")
    return base / "CoursIA" / "merge_ready" / "journal.jsonl"


# Une retenue decidee par le coordinateur (collision, ordre de stack,
# arbitrage en attente) est invisible aux portes comme a B.0 : un would-merge
# ne dit pas que j'ai decide de merger. Avant ce fichier, les retenues
# vivaient dans un hold.txt de scratchpad de SESSION, que cet organe ne
# lisait pas -- un run --apply, ou la tache planifiee, les aurait ignorees.
HOLD_LINE = re.compile(r"^(\d+)(?:\s+(.*))?$")
MAIN_RED_HOLD_PREFIX = "main-red-sentinel "
MAIN_RED_HOLD_NUMBER = 0  # identifiant global reserve, jamais un numero de PR
SCRIPTS_TESTS_CHECK = "Scripts Tests (CPU)"

#: Borne ECRITE de la remontee dans l'historique de `main` (#24828, revue
#: ai-01 du 2026-11-10, point 1). On juge le dernier commit qui porte un
#: VERDICT TERMINE de `Scripts Tests (CPU)` ; au-dela de cette borne, et
#: seulement au-dela, l'organe refuse de demarrer (fail-closed).
MAIN_RED_HISTORY_LIMIT = 20

#: Conclusions qui portent un VERDICT DE CODE. Seul `failure` pose la
#: retenue, `success` la retire. Tout le reste -- `cancelled`,
#: `timed_out`, `action_required`, `skipped`, `stale` -- est de l'INFRA :
#: une annulation ou un runner perdu n'est pas une regression, et le
#: verdict remonte au commit precedent (point 2 de la meme revue).
MAIN_RED_CODE_VERDICTS = ("success", "failure")

#: Etapes d'INFRASTRUCTURE du job `Scripts Tests (CPU)`. Une `failure` dont
#: la PREMIERE etape en echec est l'une d'elles n'est pas un verdict de code :
#: le job n'a pas execute un seul test. Le cas mesure (12/11, run 43316243195,
#: job 131524893709, runner `myia-ai-01-wsl-14`) : l'etape
#: `actions/checkout@v4` a tire les 1 606 branches (`fetch-depth: 0`) de 22:12
#: a 22:31Z puis a echoue sur `RPC failed; curl 28 Operation too slow`. Les
#: gardes de plancher de collection qui suivent ont alors echoue faute de
#: fichiers -- consequence, pas cause. Aucun test n'etait identifie dans le
#: log : la sentinelle retenait `main` sur une panne de checkout.
#:
#: Les marqueurs sont des sous-chaines du NOM de l'etape, en minuscules. Les
#: noms rendus par l'API sont ceux du workflow (mesure sur le job cite :
#: `Run actions/checkout@v4`, `Run actions/setup-python@v5`,
#: `Install dependencies`, `Purger un work dir reutilise au graphe
#: incomplet (#15387)`).
MAIN_RED_INFRA_STEP_MARKERS = (
    "set up job",
    "actions/checkout",
    "actions/setup-python",
    "install dependencies",
    "purger un work dir",
    "[heal]",
    # T-K (#25510) : les deux etapes du checkout borne tirees
    # ("T-K : ascendance de la tete + la base, sans les 1 606 branches",
    # "T-K : controle -- la base est visible, son historique est lu").
    # Une panne de reseau sur le `git fetch --unshallow` est une panne
    # d'infrastructure, pas un verdict de code : la sentinelle doit
    # remonter au commit precedent, comme pour `actions/checkout`.
    "t-k :",
)


def default_hold_path(journal_path: Path) -> Path:
    """La retenue vit a cote du journal : meme machine, meme duree de vie."""
    return journal_path.parent / "hold.txt"


def load_holds(path: Path) -> dict[int, str]:
    """Lit le fichier de retenues : ``{numero: motif}``.

    Absent -> aucune retenue. Une ligne qui n'est ni vide, ni un commentaire,
    ni ``<numero> [motif]`` est une erreur : ``#17530`` en tete de ligne se
    lirait sinon comme un commentaire et la retenue tomberait en silence.
    """
    if not path.exists():
        return {}
    try:
        text = path.read_text(encoding="utf-8-sig")
    except OSError as exc:
        raise CannotRunError(f"fichier de retenues {path} illisible : {exc}") from exc
    holds: dict[int, str] = {}
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#") and not re.match(r"#\s*\d", line):
            continue
        match = HOLD_LINE.match(line)
        if match is None:
            raise CannotRunError(
                f"fichier de retenues {path}, ligne {lineno} malformee : {raw!r} "
                "(attendu : <numero> [motif])"
            )
        reason = (match.group(2) or "").strip().lstrip("#-").strip()
        holds[int(match.group(1))] = reason or "hold.txt"
    return holds


def _main_commit_history(
    runner: Runner, gh_env: dict[str, str], limit: int = MAIN_RED_HISTORY_LIMIT
) -> list:
    """SHA des `limit` derniers commits de `main`, du plus recent au plus ancien.

    L'historique est lu en UN appel : c'est lui qui remplace la lecture de la
    seule tete, puisque le verdict a juger n'est pas forcement celui de la
    tete (point 1 de la revue ai-01 du 2026-11-10).
    """
    result = runner.run(
        [
            "gh", "api",
            f"repos/{REPO}/commits?sha=main&per_page={limit}",
            "--jq", ".[] | .sha",
        ],
        env=gh_env,
    )
    if result.returncode != 0:
        raise CannotRunError(
            "lecture de l'historique de main impossible pour la sentinelle CI"
        )
    shas = []
    for line in (result.stdout or "").splitlines():
        sha = line.strip().strip('"')
        if re.fullmatch(r"[0-9a-fA-F]{7,40}", sha):
            shas.append(sha)
    return shas


def _scripts_tests_check(
    runner: Runner, gh_env: dict[str, str], sha: str
) -> "dict | None":
    """Check ``Scripts Tests (CPU)`` d'un commit, ou None si ce check n'existe pas.

    None signifie « pas de signal sur ce commit » -- une poussee qui ne
    touche pas les chemins du workflow, ou un check renomme. Ce n'est ni un
    vert ni un rouge : la remontee continue.
    """
    checks_result = runner.run(
        [
            "gh", "api", f"repos/{REPO}/commits/{sha}/check-runs?per_page=100",
            "--paginate", "--jq",
            ".check_runs[] | {name, conclusion, status, started_at, output, details_url} | tojson",
        ],
        env=gh_env,
    )
    if checks_result.returncode != 0:
        raise CannotRunError(f"lecture des checks de {sha} impossible")
    try:
        checks = [
            json.loads(line) for line in (checks_result.stdout or "").splitlines()
            if line.strip()
        ]
    except ValueError as exc:
        raise CannotRunError(f"reponse des checks de {sha} non JSON") from exc
    scripts_checks = [row for row in checks if row.get("name") == SCRIPTS_TESTS_CHECK]
    if not scripts_checks:
        return None
    return max(scripts_checks, key=lambda row: str(row.get("started_at") or ""))


def _job_id_of_check(check: dict) -> str:
    """Identifiant du job GitHub Actions qui a produit ce check-run.

    Le `details_url` d'un check-run de job porte le job : mesure sur le job
    cite par le coordinateur (131524893709), il vaut
    `https://github.com/jsboige/CoursIA/actions/runs/43316243195/job/131524893709`.
    On retombe sur l'identifiant du check-run lui-meme, qui vaut le job
    dans ce cas. Vide si rien n'est identifiable -- et alors on ne lit
    AUCUNE etape : une lecture impossible ne vaut pas un verdict.
    """
    details_url = str(check.get("details_url") or "")
    match = re.search(r"/job/(\d+)", details_url)
    if match:
        return match.group(1)
    raw = str(check.get("id") or "").strip()
    return raw if raw.isdigit() else ""


def _first_failing_step(runner: Runner, gh_env: dict[str, str],
                        check: dict) -> str:
    """Nom de la PREMIERE etape en echec du job ("" si elle est illisible).

    Une seule lecture de job par commit juge, et seulement dans le cas
    `failure` sans test identifie. Le tri se fait sur le numero d'etape :
    l'API renvoie les etapes dans l'ordre, mais le tri le rend explicite.
    """
    job_id = _job_id_of_check(check)
    if not job_id:
        return ""
    result = runner.run(
        [
            "gh", "api", f"repos/{REPO}/actions/jobs/{job_id}",
            "--jq",
            '[.steps[] | select(.conclusion == "failure")'
            ' | {n: .name, o: .number}] | sort_by(.o) | .[0].n // ""',
        ],
        env=gh_env,
    )
    if result.returncode != 0:
        return ""
    return (result.stdout or "").strip().strip('"')


def _is_infra_step(step_name: str) -> bool:
    """Vrai si l'etape nommee est une etape d'INFRASTRUCTURE."""
    lowered = (step_name or "").lower()
    return any(marker in lowered for marker in MAIN_RED_INFRA_STEP_MARKERS)


def _identified_test(runner: Runner, gh_env: dict[str, str], check: dict) -> str:
    """Nom du test en echec identifie dans le check, sinon dans le log du run.

    Vide quand aucun test n'est identifie -- et c'est precisement ce cas
    qui demande de regarder les ETAPES du job : un `failure` sans test
    identifiable peut etre une panne d'infrastructure.
    """
    summary = str((check.get("output") or {}).get("summary") or "")
    test_match = re.search(r"(?:FAILED|ERROR)\s+([^\s<]+(?:\s*::\s*[^\s<]+)*)", summary)
    if test_match:
        return test_match.group(1)
    # Le check-run natif Actions contient souvent un resume sans le detail
    # pytest. Dans ce cas, lire le log d'echec du run associe au check.
    details_url = str(check.get("details_url") or "")
    run_match = re.search(r"/actions/runs/(\d+)(?:/|$)", details_url)
    if run_match:
        log_result = runner.run(
            ["gh", "run", "view", run_match.group(1), "--repo", REPO, "--log-failed"],
            env=gh_env,
        )
        if log_result.returncode == 0:
            test_match = re.search(
                r"(?:FAILED|ERROR)\s+([^\s<]+(?:\s*::\s*[^\s<]+)*)",
                log_result.stdout or "",
            )
            if test_match:
                return test_match.group(1)
    return ""


def refresh_main_red_hold(
    runner: Runner, gh_env: dict[str, str], hold_path: Path
) -> None:
    """Actualise la retenue globale depuis le dernier VERDICT DE CODE de `main`.

    Ce qui est juge, et comment (#24828, revue ai-01 du 2026-11-10) :

    1. **Un check en cours n'est pas un refus de demarrer.** On remonte
       l'historique de `main` jusqu'au dernier commit qui porte un verdict
       TERMINE de `Scripts Tests (CPU)`, et on juge celui-la. Refuser parce
       que la tete est en cours serialiserait tous les merges sur la suite
       lourde -- mesure du 2026-11-10 sur la flotte : mediane 26,6 min,
       p90 112,8 min, et 69,7 % des runs annules par la poussee suivante.
    2. **Seul `failure` pose la retenue.** `cancelled`, `timed_out` et les
       autres conclusions sans verdict de code sont de l'INFRA (runner
       perdu, annulation en rafale) : le verdict remonte au commit
       precedent, comme au point 1.
    3. **Fail-closed borne.** Si aucun des `MAIN_RED_HISTORY_LIMIT` derniers
       commits ne porte de verdict termine, l'organe refuse de demarrer et
       nomme la borne.
    4. **Une `failure` sans test identifie peut etre une panne
       d'infrastructure.** On lit alors les etapes du job : si la PREMIERE
       etape en echec est une etape d'infrastructure (checkout, setup-python,
       installation, purge HEAL), le commit est ecarte comme
       `infra(failure-step:<nom>)` et le verdict remonte au commit
       precedent, comme pour `cancelled`. Le cas mesure (12/11, run
       43316243195) : le checkout avait echoue sur `curl 28` apres 19 min
       de fetch, aucun test n'avait ete execute, et la sentinelle retenait
       `main` sur une panne d'infrastructure.

    La ligne posee par cette sentinelle est la seule que le chemin vert peut
    retirer ; les retenues du coordinateur ne sont jamais touchees.
    """
    history = _main_commit_history(runner, gh_env, MAIN_RED_HISTORY_LIMIT)
    if not history:
        raise CannotRunError(
            "historique de main vide pour la sentinelle CI ; refus fail-closed"
        )

    judged = None
    skipped = []
    for sha in history:
        check = _scripts_tests_check(runner, gh_env, sha)
        if check is None:
            skipped.append((sha, "check-absent"))
            continue
        status = str(check.get("status") or "").lower()
        conclusion = str(check.get("conclusion") or "").lower()
        if status != "completed":
            skipped.append((sha, f"en-cours({status or 'sans-statut'})"))
            continue
        if conclusion not in MAIN_RED_CODE_VERDICTS:
            skipped.append((sha, f"infra({conclusion or 'sans-verdict'})"))
            continue
        test_name = ""
        if conclusion == "failure":
            test_name = _identified_test(runner, gh_env, check)
            if not test_name:
                # Aucun test identifie : la `failure` peut venir de
                # l'infrastructure. UNE lecture de job, dans ce cas seul.
                step = _first_failing_step(runner, gh_env, check)
                if step and _is_infra_step(step):
                    skipped.append((sha, f"infra(failure-step:{step})"))
                    print(
                        "merge_ready : sentinelle main-red -- commit "
                        f"{sha[:9]} ecarte, premiere etape en echec "
                        f"'{step}' (infrastructure) : le verdict remonte au "
                        "commit precedent"
                    )
                    continue
        judged = (sha, check, conclusion, test_name)
        break

    if judged is None:
        raise CannotRunError(
            "aucun verdict termine de {!r} sur les {} derniers commits de main "
            "({} ecarte(s) : {}) ; refus fail-closed".format(
                SCRIPTS_TESTS_CHECK, len(history), len(skipped),
                ", ".join(f"{sha[:9]}:{motif}" for sha, motif in skipped[:5]),
            )
        )

    sha, check, conclusion, test_name = judged

    lines = hold_path.read_text(encoding="utf-8-sig").splitlines() if hold_path.exists() else []
    owned = [line for line in lines if line.strip().startswith(f"{MAIN_RED_HOLD_NUMBER} {MAIN_RED_HOLD_PREFIX}")]
    retained = [line for line in lines if line not in owned]
    if conclusion == "success":
        updated = retained
    else:
        test_name = test_name or "test-non-identifie-dans-le-check"
        reason = (
            f"{MAIN_RED_HOLD_NUMBER} {MAIN_RED_HOLD_PREFIX}sha={sha} "
            f"check={SCRIPTS_TESTS_CHECK} conclusion={conclusion} test={test_name}"
        )
        updated = [*retained, reason]
    if updated != lines:
        hold_path.parent.mkdir(parents=True, exist_ok=True)
        tmp_path = hold_path.with_name(hold_path.name + ".tmp")
        tmp_path.write_text("\n".join(updated) + ("\n" if updated else ""), encoding="utf-8")
        tmp_path.replace(hold_path)


def clear_main_red_hold(hold_path: Path) -> bool:
    """Retire UNIQUEMENT la ligne de la sentinelle du fichier de retenues.

    Le chemin vert la retire deja au run suivant ; cette fonction existe pour
    le cas ou le correctif d'un `main` rouge doit etre merge AVANT ce run --
    la retenue globale saute aussi la PR qui repare le rouge (point 3 de la
    revue ai-01 du 2026-11-10). Les retenues du coordinateur ne sont
    jamais touchees. Renvoie True si une ligne a ete retiree.
    """
    if not hold_path.exists():
        return False
    lines = hold_path.read_text(encoding="utf-8-sig").splitlines()
    kept = [
        line for line in lines
        if not line.strip().startswith(
            f"{MAIN_RED_HOLD_NUMBER} {MAIN_RED_HOLD_PREFIX}")
    ]
    if kept == lines:
        return False
    tmp_path = hold_path.with_name(hold_path.name + ".tmp")
    tmp_path.write_text("\n".join(kept) + ("\n" if kept else ""), encoding="utf-8")
    tmp_path.replace(hold_path)
    return True


def scope_exclusion(path: str) -> str | None:
    """Raison d'exclusion de perimetre (b) pour un chemin, sinon None.

    Fail-closed : .claude/ et .github/ (repertoires), CLAUDE.md (tout
    niveau). Les separateurs sont normalises en / (gh rend des /, on
    accepte aussi des \\ par prudence).
    """
    p = (path or "").replace("\\", "/")
    if p == ".claude" or p.startswith(".claude/"):
        return f"scope:.claude:{path}"
    if p == ".github" or p.startswith(".github/"):
        return f"scope:.github:{path}"
    if p == "CLAUDE.md" or p.endswith("/CLAUDE.md"):
        return f"scope:CLAUDE.md:{path}"
    return None


OUT_OF_FLEET_BRANCH_PREFIX = "claude/"


def grain_exclusion(body: str | None, head_ref: str | None = None) -> str | None:
    """Raison d'exclusion du tag Grain, sinon None.

    Le lecteur est le parseur PARTAGE (grain_tag.parse_grain_tag, #9485) :
    formes tolerees (gras, titre, sans deux-points) et refus de substance
    (aucun TIER/GENRE lisible -> None). DEEP est dans le perimetre depuis
    Q131 (2026-10-19), sous la meme approbation prealable du coordinateur
    que MED et LIGHT. Une PR hors flotte (branche ``claude/*``) n'a pas de
    tag par construction : son absence n'est pas une exclusion. Ailleurs,
    un tag absent ou un tier hors (DEEP, MED, LIGHT) est illisible au sens
    de la grammaire -> fail-closed.
    """
    tag = parse_grain_tag(body)
    if tag is None:
        if (head_ref or "").startswith(OUT_OF_FLEET_BRANCH_PREFIX):
            return None
        return "grain-tier-unparsable"
    tier = tag.get("tier") or ""
    if tier not in TIERS:
        return f"grain-tier-unknown:{tier}"
    return None


# --- appels gh (tous par le runner, tous avec GH_TOKEN epingle) ---------------


def resolve_token(runner: Runner) -> str:
    """Resout UNE fois le jeton du coordinateur, sans jamais ``gh auth switch``.

    GH_TOKEN/GITHUB_TOKEN sont RETIRES de l'env de resolution : une variable
    ambiante prendrait precedent sur ``--user`` et rendrait silencieusement le
    jeton d'une autre identite.
    """
    env = {
        key: value
        for key, value in os.environ.items()
        if key not in ("GH_TOKEN", "GITHUB_TOKEN")
    }
    res = runner.run(["gh", "auth", "token", "--user", COORDINATOR_USER], env=env)
    token = res.stdout.strip()
    if res.returncode != 0 or not token:
        raise CannotRunError(
            f"gh auth token --user {COORDINATOR_USER} a echoue "
            f"(rc={res.returncode}) : {res.stderr.strip()[:200]}"
        )
    return token


def _json_stdout(res: RunResult, what: str) -> object:
    try:
        return json.loads(res.stdout)
    except json.JSONDecodeError as exc:
        raise UnexpectedError(f"{what} : stdout illisible ({exc})") from exc


def list_open_prs(runner: Runner, gh_env: dict[str, str]) -> list[int]:
    """Numeros des PRs ouvertes, triees croissant (la plus ancienne d'abord)."""
    res = runner.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "open",
         "--limit", str(PR_LIST_LIMIT), "--json", "number"],
        env=gh_env,
    )
    if res.returncode != 0:
        raise UnexpectedError(
            f"gh pr list rc={res.returncode} : {res.stderr.strip()[:200]}"
        )
    rows = _json_stdout(res, "gh pr list")
    if not isinstance(rows, list):
        raise UnexpectedError("gh pr list : la reponse n'est pas une liste")
    numbers = sorted(
        int(row["number"])
        for row in rows
        if isinstance(row, dict) and row.get("number") is not None
    )
    return numbers


#: ``reviews`` est lu par la MEME commande que le reste : la disposition de
#: review se classe sans appel supplementaire (l'oid de review y figure, mesure
#: du 2026-09-25 : ``gh pr view --json reviews`` rend ``commit.oid``).
PR_VIEW_FIELDS = (
    "number,title,isDraft,body,headRefName,headRefOid,baseRefName,baseRefOid,files,"
    "changedFiles,comments,reviews"
)


def fetch_pr_view(runner: Runner, pr: int, gh_env: dict[str, str]) -> dict:
    """Une vue par PR : brouillon, body (tag Grain), tete, fichiers, commentaires,
    reviews (disposition de review classee a la tete, point 1 de #17672)."""
    res = runner.run(
        ["gh", "pr", "view", str(pr), "--repo", REPO, "--json", PR_VIEW_FIELDS],
        env=gh_env,
    )
    if res.returncode != 0:
        raise UnexpectedError(
            f"gh pr view {pr} rc={res.returncode} : {res.stderr.strip()[:200]}"
        )
    view = _json_stdout(res, f"gh pr view {pr}")
    if not isinstance(view, dict):
        raise UnexpectedError(f"gh pr view {pr} : la reponse n'est pas un objet")
    return view


def _review_voice_state(review: dict) -> str | None:
    """L'etat REEL d'une review, ou le verdict type de son corps (canal COMMENT).

    Meme lecture a deux surfaces que le canon (``REAL_STATES`` puis
    ``VERDICT_RE``), pour la meme raison : le jeton du cluster ne peut poster que
    des COMMENT, son verdict vit donc dans le corps (#16926). Une voix sans
    verdict type n'est pas une approbation -- un commentaire de lane, de CI ou
    un ``COMMENTED`` muet ne dit rien de la disposition.

    ``DISMISSED`` n'est jamais approbateur : une approbation ANNULEE ne
    gouverne plus, meme si son corps porte encore le jeton type (reserve 2
    Hermes 2026-09-26 : le croisement des deux surfaces manquait).
    """
    state = str(review.get("state") or "")
    if state == "DISMISSED":
        return None
    if state in review_canon.REAL_STATES:
        return state
    match = review_canon.VERDICT_RE.search(str(review.get("body") or ""))
    return match.group(1) if match else None


def review_disposition(view: dict, head: str) -> str:
    """La disposition de review, CLASSEE a la tete evaluee (point 1 de #17672).

    La tete gouverne : une approbation posee sur un commit anterieur ne couvre
    pas le commit qui va etre merge, et c'est cette difference que le dossier
    n'exprime pas (il hache l'oid de review sans le comparer). La voix qui
    gouverne une tete est la PLUS RECENTE des VOIX posees sur cette tete
    (latest-wins, la discipline du canon) : une approbation suivie, sur la
    meme tete, d'une voix qui n'approuve pas, n'est plus une approbation.
    Une ligne qui n'est pas une voix au sens du canon (pas d'etat REEL ni de
    ``VERDICT`` type en corps -- commentaire de lane, ``[OVERRIDE]``, CI) ne
    detrone rien : le latest-wins porte sur les voix, pas sur les lignes
    ``reviews[]`` (reserve 1 Hermes 2026-09-26).

    Fonction pure : la vue est deja fetchee, aucun appel supplementaire.
    """
    reviews = [row for row in (view.get("reviews") or []) if isinstance(row, dict)]
    at_head = [
        row
        for row in reviews
        if str(((row.get("commit") or {}).get("oid")) or "") == head
    ]
    voices_at_head = [row for row in at_head if _review_voice_state(row)]
    if voices_at_head:
        latest = max(voices_at_head, key=lambda row: str(row.get("submittedAt") or ""))
        if _review_voice_state(latest) in APPROVING_VOICES:
            return APPROVED_EXACT_HEAD
    if any(_review_voice_state(row) in APPROVING_VOICES for row in reviews):
        return APPROVAL_NOT_ON_HEAD
    return NO_APPROVAL


# --- approbation du coordinateur (etape 2ter, Q67 option a) --------------------


def _voice_login(row: dict) -> str:
    """Login d'auteur d'une ligne de review, TYPE PAR LA LIGNE elle-meme.

    #17437, relecture ai-01 du 2026-11-12 : la preuve d'identite est le
    champ de TYPE de la ligne (REST ``user.type`` / GraphQL
    ``author.__typename``), JAMAIS une sonde globale -- ``gh api
    users/<slug>[bot]`` prouve que l'App EXISTE, pas que l'AUTEUR de la
    ligne est l'App : un compte UTILISATEUR homonyme du slug serait
    confondu avec elle. Les lignes typees reconstruisent le suffixe par
    ``gh_identity`` ; une ligne NON typee n'est une voix que pour
    l'orthographe canonique EXACTE de l'humain (``myia-ai-01``, nu par
    construction) : toute forme nue App est refusee, sans sonde ni
    reconstruction -- fail-closed par construction, plus de cas muets.
    """
    author = row.get("author") or row.get("user") or {}
    if not isinstance(author, dict):
        return ""
    if author.get("__typename") or author.get("type"):
        return gh_identity.normalize_author_login(author)
    login = str(author.get("login") or "")
    if login == COORDINATOR_USER:
        return login
    return ""


def _typed_reviews(runner: Runner, pr: int,
                   gh_env: dict[str, str] | None = None) -> list[dict]:
    """Reviews d'une PR sur la surface REST TYPEE, en forme canonique.

    #17437 : ``gh pr view --json reviews`` rend l'auteur SANS champ de type ;
    la preuve de type par ligne se prend sur une surface qui le transporte.
    REST ``pulls/N/reviews`` rend chaque ligne avec ``user.login`` (deja
    suffixe pour une App) ET ``user.type`` -- les deux ce dont
    ``_voice_login`` a besoin. La ligne est mappee a la forme attendue par
    ``_review_voice_state`` et le latest-wins (``submittedAt``,
    ``commit.oid`` depuis ``commit_id``).

    Echec de lecture : liste vide -- la preuve illisible vaut refus, le
    verdict ``no-coordinator-approval`` en rend compte (fail-closed).
    """
    cmd = ["gh", "api", f"repos/{REPO}/pulls/{pr}/reviews",
           "--paginate", "--slurp"]
    res = runner.run(cmd, env=gh_env) if gh_env else runner.run(cmd)
    if res.returncode != 0 or not (res.stdout or "").strip():
        return []
    try:
        pages = json.loads(res.stdout)
    except json.JSONDecodeError:
        return []
    flat: list = []
    for page in pages if isinstance(pages, list) else [pages]:
        if isinstance(page, list):
            flat.extend(page)
        elif isinstance(page, dict):
            flat.append(page)
    out: list[dict] = []
    for row in flat:
        if not isinstance(row, dict):
            continue
        user = row.get("user") or {}
        out.append({
            "author": {
                "login": (user or {}).get("login") or "",
                "type": (user or {}).get("type") or "",
            },
            "state": row.get("state") or "",
            "body": row.get("body") or "",
            "submittedAt": row.get("submitted_at") or "",
            "commit": {"oid": row.get("commit_id") or ""},
        })
    return out


def coordinator_approval_oid(view: dict, runner: Runner | None = None,
                             gh_env: dict[str, str] | None = None) -> str | None:
    """Oid du commit que la DERNIERE voix du coordinateur approuve, ou None.

    #17437 : la voix du coordinateur est le login humain seul
    (``COORDINATOR_VOICES``) -- toute forme App y est refusee : une App de
    machine est forgeable par la lane soeur (bloc justificatif au-dessus de
    sa definition). La preuve d'identite est TYPEE PAR LIGNE :
    avec un runner, les reviews se relisent sur la surface REST typee
    (``pulls/N/reviews``, ``user.type`` par ligne) ; sans runner (lecture
    pure, tests), seules comptent les lignes deja typees du payload et
    l'orthographe canonique exacte de l'humain -- une forme nue App n'est
    JAMAIS resolue (relecture ai-01 2026-11-12 : la sonde prouve que
    l'App existe, pas que l'auteur de la ligne est l'App).

    Latest-wins sur les seules voix du coordinateur, lues comme le canon (etat
    reel, puis verdict type en corps) : un ``CHANGES_REQUESTED`` ou un
    ``VERDICT: CONCERNS`` posterieur retire l'approbation, un ``COMMENTED``
    sans verdict (une phrase de levee, par exemple) ne la retire pas. Seul
    l'etat REEL ``APPROVED`` vaut approbation : c'est le geste explicite de
    lecture, pas un jeton de corps.
    """
    rows: list = []
    if runner is not None and isinstance(view.get("number"), int):
        rows = _typed_reviews(runner, view["number"], gh_env)
    if not rows:
        # Surface CLI non typee : l'humain nu canonique y est reconnu
        # (orthographe exacte), toute forme App y est invisible -- les
        # lignes typees du payload restent valables (tests, GraphQL).
        rows = [row for row in view.get("reviews") or []
                if isinstance(row, dict)]
    voices = [
        row
        for row in rows
        if _voice_login(row) in COORDINATOR_VOICES
        and _review_voice_state(row)
    ]
    if not voices:
        return None
    latest = max(voices, key=lambda row: str(row.get("submittedAt") or ""))
    if str(latest.get("state") or "") != "APPROVED":
        return None
    oid = str(((latest.get("commit") or {}).get("oid")) or "")
    return oid or None


def _dwell_fetch(runner: Runner, gh_env: dict[str, str]):
    """``fetch`` de ``merge_dwell`` passe par le runner, jeton epingle."""

    def fetch(path: str) -> object:
        res = runner.run(["gh", "api", path], env=gh_env)
        if res.returncode != 0:
            raise merge_dwell.DwellError(f"gh api {path} rc={res.returncode}")
        try:
            return json.loads(res.stdout)
        except json.JSONDecodeError as exc:
            raise merge_dwell.DwellError(f"gh api {path} : reponse non-JSON") from exc

    return fetch


def _dwell_git(runner: Runner):
    """``run_git`` de ``merge_dwell`` passe par le runner, dans ce depot."""

    def run_git(args: list[str]) -> tuple[int, str]:
        res = runner.run(["git", "-C", str(REPO_ROOT), *args])
        return res.returncode, res.stdout

    return run_git


def coordinator_approval_reason(
    view: dict, head: str, runner: Runner, gh_env: dict[str, str]
) -> str | None:
    """Etape 2ter : ``None`` si l'approbation du coordinateur couvre ``head``.

    Une approbation posee sur une tete anterieure couvre encore la tete
    courante si les deux ne different que par des rafraichissements de base
    prouves content-free : les deux tetes remontent alors au MEME dernier
    commit de contenu. Toute autre difference perime la lecture ; une preuve
    illisible vaut refus.
    """
    approved = coordinator_approval_oid(view, runner, gh_env)
    if approved is None:
        return "no-coordinator-approval"
    if approved == head:
        return None
    base = str(view.get("baseRefOid") or "")
    if not base:
        return "coordinator-approval-unverifiable:no-base"
    fetch = _dwell_fetch(runner, gh_env)
    run_git = _dwell_git(runner)
    try:
        current = merge_dwell.last_authoritative_sha(
            REPO, head, base, fetch=fetch, run_git=run_git
        )
        read = merge_dwell.last_authoritative_sha(
            REPO, approved, base, fetch=fetch, run_git=run_git
        )
    except merge_dwell.DwellError:
        return "coordinator-approval-unverifiable"
    if current == read:
        return None
    return "coordinator-approval-stale"


def lean_build_attestation_reason(
    view: dict, head: str, runner: Runner, gh_env: dict[str, str]
) -> str | None:
    """Etape 2bis (#24989) : ``None`` si la PR n'exige pas d'attestation Lean,
    ou si elle en porte une qui couvre la tete courante.

    La regle HARD `lean-merge-discipline.md` §1 exige un ``lake build``
    **local** par ai-01 avant tout merge d'une PR qui touche du Lean : le
    vert de la CI ne le remplace pas (incident #866, revert #885). Depuis le
    retrait du dossier (2026-11-05), l'APPROVE du coordinateur est la seule
    porte -- la regle ne tenait plus que par sa vigilance.

    Detection : le diff contient-il un fichier Lean (``.lean``,
    ``lakefile.*``, ``lean-toolchain``, ``lake-manifest.json``) ? Une PR qui
    n'en contient pas n'est pas concernee : le controle ne coute alors rien.

    Preuve exigee : un commentaire d'attestation pose par ``myia-ai-01``
    (l'organe `scripts/lean/attest_local_build.py` le produit ; une lane ne
    s'atteste pas elle-meme). La couverture de tete suit la MEME regle que
    l'APPROVE : l'attestation vaut a la tete exacte, ou sur une tete qui n'en
    differe que par des rafraichissements de base PROUVES content-free. Un
    commit de contenu posterior la perime.

    Motifs : ``lean:no-local-build-attestation`` (aucune attestation, ou
    attestation perimee) et ``lean:local-build-attestation-unverifiable``
    (preuve illisible : base absente, ou chaine de commits illisible).
    """
    touched = lean_build_attestation.lean_paths(
        str((row or {}).get("path") or "") for row in (view.get("files") or [])
    )
    if not touched:
        return None
    attestation = lean_build_attestation.attestation_from_comments(
        view.get("comments") or []
    )
    if attestation is None:
        return "lean:no-local-build-attestation"
    attested = str(attestation.get("sha") or "")
    if attested == head:
        return None
    base = str(view.get("baseRefOid") or "")
    if not base:
        return "lean:local-build-attestation-unverifiable:no-base"
    fetch = _dwell_fetch(runner, gh_env)
    run_git = _dwell_git(runner)
    try:
        current = merge_dwell.last_authoritative_sha(
            REPO, head, base, fetch=fetch, run_git=run_git
        )
        read = merge_dwell.last_authoritative_sha(
            REPO, attested, base, fetch=fetch, run_git=run_git
        )
    except merge_dwell.DwellError:
        return "lean:local-build-attestation-unverifiable"
    if current == read:
        return None
    return "lean:no-local-build-attestation"


def run_nits(runner: Runner, pr: int, gh_env: dict[str, str]) -> int:
    """Etape 4 : organe B.0. Retourne son rc (0 = clear), hors contrat -> arret."""
    res = runner.run([sys.executable, _repo_relative(NITS_PATH), str(pr)], env=gh_env)
    if res.returncode not in NITS_DOCUMENTED_RC:
        raise UnexpectedError(
            f"B.0 PR {pr} rc={res.returncode} hors contrat : "
            f"{(res.stderr or res.stdout).strip()[:200]}"
        )
    return res.returncode


def twin_collision_reason(
    runner: Runner, pr: int, head: str, files: list[dict]
) -> str | None:
    """Etape 5bis : collision d'index twin-pairs contre le ``main`` du moment.

    Ne coute rien aux PRs qui ne touchent pas le registre twin. Pour les
    autres, un fetch puis l'organe partage : ``None`` si l'organe rend 0,
    un motif de skip sinon. L'organe rend 1 sur collision, 2 quand il n'a
    pas pu lire deux revisions -- et « je n'ai pas pu lire » n'est pas
    « c'est propre » : skip, jamais merge.

    La classification semantique de la collision (#18725) distingue deux cas :
      ON-MAIN    la base porte deja l'index et une tete le RE-porte.
                 Le merge rendrait le garde CI ``test_audit_index_unique``
                 DRIFT-INTRO sur une autre PR qui n'a rien demande.
                 Skip dur, motif ``twin-collision-on-main:<pair>/<index>``
                 + message human lisible nommant la collision et le geste.
      MULTI-PR   la base NE porte PAS l'index, mais deux ou plusieurs tetes
                 differentes le portent (concurrence de lanes). La premiere
                 mergee gagne, la seconde renumerote. Avertissement seul,
                 le merge continue (le gate CI bloque de toute facon si la
                 seconde arrive avant renumerotation).

    Le jugement le plus tranchant est celui de l'ARBRE DE FUSION (`--merged`) :
    il repond a la seule question qui compte au merge -- « `main` sera-t-il
    rouge apres ce merge ? ». Le jugement base+tete compare deux revisions
    prises separement, et la base lue est celle du MOMENT DE LA LECTURE ;
    une collision introduite sur `main` par une autre PR entretemps n'y est
    pas visible, alors qu'elle est dans l'arbre de fusion (mesure du
    2026-11-03 : #23832 et #24010 ont alloue les memes ordinals 0024-0026
    sur `search-05-geneticalgorithms`, et les deux PRs sont passees).
    """
    touched = any(
        str((row or {}).get("path") or "").startswith(TWIN_REGISTRY_PREFIX)
        for row in files
    )
    if not touched:
        return None
    fetch = runner.run(
        ["git", "-C", str(REPO_ROOT), "fetch", "--quiet", "origin", "main",
         f"pull/{pr}/head"]
    )
    if fetch.returncode != 0:
        return "twin-collision-unreadable:fetch"
    # Les PRs OUVERTES : l'ordinal qu'une PR CONCURRENTE revendique deja. Ni
    # le jugement base+tete ni l'arbre de fusion ne le voient -- les deux ne
    # portent que des revisions MERGEES. L'API des PRs ouvertes, elle, sait.
    # Mesure du 2026-11-04 : 5 collisions de ce type etaient VIVANTES entre PRs
    # ouvertes (csp-1-fundamentals 0034, csp-6-hybridization 0024/0025,
    # gametheory-15-cooperativegames 0044, search-13-limited-discrepancy-search
    # 0013) -- aucune n'etait visible de l'arbre de fusion, puisque aucune des
    # deux PRs n'etait mergee.
    claims_res = runner.run(
        [sys.executable, _repo_relative(TWIN_CLAIMS_PATH), "--json"]
    )
    if claims_res.returncode != 0:
        # « je n'ai pas pu lire » n'est pas « c'est propre » : skip dur, comme
        # pour le fetch de l'arbre de fusion. La PR sera rejugee.
        return "twin-collision-unreadable:open-claims"
    try:
        fd, claims_path = tempfile.mkstemp(prefix="twin-claims-",
                                           suffix=".json")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(claims_res.stdout)
    except OSError:
        return "twin-collision-unreadable:open-claims"
    try:
        res = runner.run(
            [sys.executable, _repo_relative(TWIN_PATH), "--repo", ".",
             "--base", "origin/main", "--head", head, "--merged", "--json",
             "--open-claims", claims_path, "--head-pr", str(pr)]
        )
    finally:
        # L'organe a lu le fichier ; il ne sert plus.
        try:
            os.unlink(claims_path)
        except OSError:
            pass
    # Le rapport JSON est lu MEME quand l'organe rend 0 : le mode `--merged`
    # peut etre ILLISIBLE (merge en conflit) alors que le jugement classique
    # ne bloque rien -- et « je n'ai pas pu lire » n'est pas « c'est propre ».
    # Lecture JSON tolérante : si le champ `verdict` est absent (organe
    # anterieur a #18683), on retombe sur le motif historique
    # ``twin-index-collision`` pour rétro-compat.
    try:
        data = json.loads(res.stdout)
    except (json.JSONDecodeError, ValueError):
        data = None
    if isinstance(data, dict):
        # --- ARBRE DE FUSION (le jugement qui repond a la question du merge)
        # Le jugement base+tete dit ce que la base et la tete portent
        # separement. L'arbre de fusion dit ce que le MERGE rend visible --
        # c'est le seul verdict qui repond a « `main` sera-t-il rouge apres
        # ce merge ? ». Il est juge AVANT le classement ON-MAIN/MULTI-PR :
        # un doublon que le merge INTRODUIT ne se classe pas (il n'existe
        # dans aucune revision prise isolement), et le laisser passer parce
        # que `cross_ref` est vide laisserait merger la PR qui casse `main`.
        merged_reasons = data.get("merged_reasons") or []
        if merged_reasons:
            first = merged_reasons[0]
            return (
                "twin-collision-on-merge:%s/%s -- %s"
                % (first.get("pair"), first.get("index"),
                   first.get("gist")
                   or "renumeroter le fichier que la tete ajoute vers le "
                      "premier index libre de la paire par `git mv` PUR")
            )
        if data.get("merged_unreadable"):
            # « je n'ai pas pu lire » n'est pas « c'est propre » : l'arbre de
            # fusion n'est pas definissable (merge en conflit). Skip dur --
            # la PR sera rejugee apres rebasage.
            return "twin-collision-unreadable:merged"
        # --- PRs OUVERTES : l'ordinal revendique par une PR concurrente
        # L'arbre de fusion repond a « que portera `main` apres ce merge ? ».
        # Il ne voit pas une PR CONCURRENTE non encore mergee : les deux PRs
        # revendiquent le meme ordinal, aucune n'est dans l'arbre de fusion, et
        # la collision n'apparait qu'apres le second merge -- en rouge
        # fleet-wide. Merger celle-ci la rendrait inevitable.
        open_reasons = data.get("open_pr_reasons") or []
        if open_reasons:
            first = open_reasons[0]
            return (
                "twin-collision-open-pr:%s/%s -- %s"
                % (first.get("pair"), first.get("index"),
                   first.get("gist")
                   or "renumeroter le fichier de la tete vers le premier "
                      "index libre de la paire par `git mv` PUR")
            )
    if res.returncode == 0:
        return None
    if res.returncode == 1:
        # L'organe a detecte une collision ; on la classifie par verdict.
        if not isinstance(data, dict):
            return "twin-index-collision"
        cross_ref = data.get("cross_ref") or []
        base_ref = data.get("base_ref") or "origin/main"
        # Verdict requis sur CHAQUE collision : si UNE collision n'a pas de
        # verdict reconnu (organe anterieur a #18683 / #18725, ou verdict
        # inconnu/None), on ne peut pas distinguer ON-MAIN de MULTI-PR, et
        # un ON-MAIN ferait rougir `main` CI des le premier merge. Fail-closed
        # : on garde le motif historique ``twin-index-collision`` tant que la
        # classification de toutes les collisions n'est pas acquise. Pas de
        # confiance silencieuse sur un mix verdict-connu + verdict-absent.
        if not all(
            isinstance(c, dict) and c.get("verdict") in ("ON-MAIN", "MULTI-PR")
            for c in cross_ref
        ):
            return "twin-index-collision"
        # Si aucun verdict ON-MAIN, c'est du MULTI-PR (avertissement seul).
        on_main = [
            c for c in cross_ref
            if isinstance(c, dict) and c.get("verdict") == "ON-MAIN"
        ]
        if not on_main:
            return None  # MULTI-PR : la premiere mergee gagne
        # ON-MAIN : skip dur. On nomme la premiere collision pour le diagnostic.
        first = on_main[0]
        pair = str(first.get("pair") or "?")
        index = str(first.get("index") or "?")
        gist = (
            "renumeroter la tete vers le premier index libre de "
            f"'{pair}' (max sur base + 1) par `git mv` PUR, "
            "puis committer. Voir scripts/notebook_tools/"
            "check_twin_index_collisions.py::ordinal_correction_gist."
        )
        return f"twin-collision-on-main:{pair}/{index} -- {gist}"
    return f"twin-collision-unreadable:rc={res.returncode}"


def slot_reservation_reason(
    runner: Runner, pr: int, head: str, files: list[dict]
) -> str | None:
    """Etape 5bis.bis (#20774) : collision de slot contre les PRs ouvertes.

    Le `slot-reservation-guard` (scripts/notebook_tools/check_slot_reservation.py)
    est appele en voie rapide en `--offline` (pas de `gh` reseau). Au merge on
    dispose de `gh` : on appelle ici le MEME organe en mode en ligne, et la
    source `open_prs` devient lisible. Une collision entre la PR courante et
    une autre PR ouverte sur le meme slot est un skip dur -- sans cette
    garde, deux PRs distinctes visent le meme slot ICT-48 sous des noms
    differents et mergent l'une apres l'autre sans que rien ne rouspette
    (cf. ICT-48 et SL-12b mesures le 14/10 dans #20774).

    Cout nul pour les PRs qui ne touchent pas de carnet (filtre prefixe).
    Pour les autres, un fetch puis l'organe partage. Sortie : ``None`` si
    l'organe rend 0 (clear), un motif de skip sinon.

    Filiation avec `twin_collision_reason` (5bis) :
      - 5bis porte les collisions de twin-pair (registre `twin_pairs.d/`) ;
      - 5bis.bis porte les collisions de slot de carnet contre la base et
        les PRs ouvertes. Les deux sont independants et complementaires :
        un meme slot vise par deux PRs n'est PAS une collision de
        twin-pair (les chemins different) -- c'est precisement le trou
        que cette garde bouche, et que `check_pr_path_collisions.py` ne
        couvre pas par construction (collision de chemins != collision
        de slot).
    """
    touched = any(
        str((row or {}).get("path") or "").startswith(SLOT_NOTEBOOK_PREFIX)
        and str((row or {}).get("path") or "").endswith(".ipynb")
        and not str((row or {}).get("path") or "").endswith("_output.ipynb")
        for row in files
    )
    if not touched:
        return None
    # Le fetch que la docstring annonce : l'organe lit l'arbre de `head` par
    # `git`, et ne le rapatrie pas lui-meme. Une tete absente du clone de
    # l'organe (clone partiel, PR jamais fetchee) le faisait sortir en rc=2,
    # donc en skip `slot-collision-unreadable` d'une PR pourtant approuvee a
    # sa tete exacte (mesure du 17/10 : #20468 et #20471, trois passes de
    # suite). Meme geste que `twin_collision_reason` (5bis).
    fetch = runner.run(
        ["git", "-C", str(REPO_ROOT), "fetch", "--quiet", "origin", "main",
         f"pull/{pr}/head"]
    )
    if fetch.returncode != 0:
        return "slot-collision-unreadable:fetch"
    # Mode en ligne : sans `--offline`, l'organe lit `gh pr list --json files`
    # pour la source `open_prs`. La voie rapide ne dispose pas de `gh`, ce
    # qui l'a forcee a `--offline` ; ici on en sert.
    res = runner.run(
        [sys.executable, _repo_relative(SLOT_PATH),
         "--base", "origin/main", "--head", head,
         "--exclude-pr", str(pr),
         "--json"],
        env={**os.environ, "GH_TOKEN": _runner_token(runner)},
    )
    if res.returncode == 0:
        return None
    if res.returncode == 1:
        # L'organe a detecte une collision : on tente de nommer la premiere
        # pour le diagnostic. Lecture JSON tolerante (cf. pattern 5bis).
        try:
            data = json.loads(res.stdout)
        except (json.JSONDecodeError, ValueError):
            return "slot-collision"
        if not isinstance(data, dict):
            return "slot-collision"
        # L'organe rend une liste sous la cle `verdicts` (cf. emit JSON de
        # `check_slot_reservation.py` ligne 1001) ; la collision est un etat
        # `conflict` avec un `conflicts[0]["state"]`. On prend la premiere
        # pour la nommer. Note : avant #20913-fixes, le parse lisait
        # `data.get("targets")` (cle inexistante), ce qui rendait la branche
        # de motif nomme morte (fallback `slot-collision` muet) ; les tests
        # passaient par des fixtures qui n'alignaient pas sur l'organe reel.
        conflicts: list[tuple[str, str]] = []
        for row in (data.get("verdicts") or []):
            if isinstance(row, dict) and row.get("verdict") == "conflict":
                state = str((row.get("conflicts") or [{}])[0].get("state") or "?")
                target = str(row.get("target") or "?")
                conflicts.append((target, state))
        if not conflicts:
            return "slot-collision"
        first_target, first_state = conflicts[0]
        # Motif : on cite la cible et la cause (taken_on_base / reserved_by_open_pr /
        # declared_reserved / duplicate_within_revision). Le geste est explicite
        # par la cause : voir la docstring de l'organe.
        return (
            f"slot-collision-on-merge:{first_state}:{first_target} -- "
            f"renumeroter ou retirer la PR concurrente (voir {SLOT_PATH.name})"
        )
    if res.returncode == 2:
        return "slot-collision-unreadable"
    return f"slot-collision-unreadable:rc={res.returncode}"


def _runner_token(runner: Runner) -> str:
    """Renvoie le token gh resolu par le runner (helpers, ne double pas l'appel)."""
    return resolve_token(runner)


# Conventions retenues pour detecter une PR empilee sur une parente non-encore
# mergee, dans le body de la PR courante. Le format le plus frequent dans
# CoursIA est "Depends on #N" (po-2024 Origami pli 2-9 sur pli 1), suivi de
# "Blocked by #N" (GitHub-style) et de "Stacked on #N" (convention locale
# signalee par po-2027 c.1485). Les emojis prefixant la mention sont
# tolerees (PRs pedagogiques :sparkles: Depends on #N).
_STACKED_PATTERNS = (
    re.compile(r"(?:^|\s|[\W_])(?:depends\s+on|blocked\s+by|stacked\s+on|"
               r"requires|stack\s*:)\s*#(\d+)", re.IGNORECASE | re.MULTILINE),
)


def find_stacked_parents(body: str | None) -> list[int]:
    """Renvoie TOUS les numeros de parentes empilees declarees, dedupliques.

    Un body peut declarer plusieurs dependances **directes** de la meme PR :
    ``Depends on #A`` puis ``Blocked by #B``. Ce n'est pas une chaine
    recursive, ce sont deux parentes que la PR courante attend l'une **et**
    l'autre -- n'en lire qu'une laisse la seconde invisible, et si la
    premiere est MERGED le chemin nominal repart sans avoir examine la
    seconde (defaut mesure du 2026-10-08, review du coordinateur).

    Ne considere pas les PRs mentionnees en passant : le marqueur
    "depends on" / "blocked by" doit etre explicite. L'ordre d'apparition
    est conserve, les doublons retires -- un body qui repete la meme
    parente ne fait pas travailler le runner deux fois."""
    if not body:
        return []
    seen: dict[int, None] = {}
    for pattern in _STACKED_PATTERNS:
        for match in pattern.finditer(body):
            seen.setdefault(int(match.group(1)), None)
    return list(seen)


def combined_tree_reason(
    runner: Runner, pr: int, head: str, gh_env: dict[str, str]
) -> str | None:
    """Etape 5quinquies : les tests d'integrite passent-ils sur ``main`` + tete ?

    ``None`` si l'organe rend GREEN (exit 0). Sinon un motif de skip :
    ``combined-tree-red:<premier test rouge>``, ``combined-tree-conflict``, ou
    ``combined-tree-unreadable:<etape>`` -- « je n'ai pas pu jouer les
    tests » n'est pas « ils passent ». ``MERGE_READY_COMBINED_CHECK=0``
    retire l'etape (rollback operateur, jamais un reglage de lane).
    """
    if os.environ.get(COMBINED_DISABLE_ENV, "1").strip() == "0":
        return None
    res = runner.run(
        [sys.executable, _repo_relative(COMBINED_PATH), "--pr", str(pr), "--head", head,
         "--json"],
        env=gh_env,
    )
    payload: dict = {}
    lines = (res.stdout or "").strip().splitlines()
    if lines:
        try:
            parsed = json.loads(lines[-1])
            if isinstance(parsed, dict):
                payload = parsed
        except ValueError:
            payload = {}
    verdict = payload.get("verdict")
    if res.returncode == 0 and verdict == "GREEN":
        return None
    if res.returncode == 1 and verdict == "CONFLICT":
        return "combined-tree-conflict"
    if res.returncode == 1 and verdict == "RED":
        failed = payload.get("failed") or []
        return f"combined-tree-red:{failed[0] if failed else 'unnamed'}"
    return f"combined-tree-unreadable:{payload.get('reason') or 'rc-' + str(res.returncode)}"


def stacked_parent_state(
    runner: Runner, parent_pr: int, gh_env: dict[str, str]
) -> str:
    """Renvoie l'etat logique de la PR parente empilee.

    Sorties : ``MERGED``, ``OPEN``, ``CLOSED``, ``unreadable``. Le check
    d'empilement est fail-CLOSED : tout etat non lisible equivaut a
    ``unreadable`` et bloque le merge par defaut (meme politique que
    ``base_ref_liveness`` ligne 905)."""
    res = runner.run(
        ["gh", "pr", "view", str(parent_pr),
         "--json", "state,mergedAt", "--repo", REPO],
        env=gh_env,
    )
    if res.returncode != 0:
        return "unreadable"
    data = _json_stdout(res, f"gh pr view {parent_pr}")
    if not isinstance(data, dict):
        return "unreadable"
    state = str(data.get("state") or "").upper()
    merged_at = data.get("mergedAt")
    if state == "MERGED" or merged_at:
        return "MERGED"
    if state == "OPEN":
        return "OPEN"
    if state in {"CLOSED", "DRAFT"}:
        return "CLOSED"
    return "unreadable"


def base_ref_liveness(
    runner: Runner, gh_env: dict[str, str], base_ref_name: str
) -> str:
    """Etape 5ter, suite (#19014) : la base non-`main` peut etre **vivante**
    (une PR ouverte dont la tete est cette branche) ou **morte** (la PR
    porteuse a ete fermee ou squash-marigee, la branche n'est rattachee a
    aucune PR ouverte). Le gate refusait les deux (#19002) ; depuis le
    retrait du dossier (2026-11-05), merge_ready porte seul ce refus et doit
    nommer lequel des deux s'applique -- une lane qui lit ``base-live-not-main`` doit
    attendre le merge de la PR porteuse, une lane qui lit ``base-gone``
    doit retargeter sur ``main`` (cf. git-workflow.md L898 collision guard).

    La distinction se fait sur la liste ``gh pr list --state all`` filtree
    sur ``head:<base_ref_name>``. Une PR OPEN avec cette tete = live,
    sinon (CLOSE/MERGED/absente) = gone. Erreur REST = ``unreadable``
    (fail-CLOSED : on ne declare pas un etat qu'on n'a pas mesure)."""
    res = runner.run(
        ["gh", "pr", "list", "--repo", REPO, "--state", "all",
         "--search", f"head:{base_ref_name}",
         "--json", "number,state", "--limit", "5"],
        env=gh_env,
    )
    if res.returncode != 0:
        return "unreadable"
    rows = _json_stdout(res, "gh pr list --search head:")
    if not isinstance(rows, list):
        return "unreadable"
    for row in rows:
        if not isinstance(row, dict):
            continue
        if str(row.get("state") or "").upper() == "OPEN":
            return "live"
    return "gone"


def mergeable_state_and_head(
    runner: Runner, pr: int, gh_env: dict[str, str]
) -> tuple[str, str]:
    """Etape 6 : (mergeable_state, head.sha) via REST, avec retry sur ``unknown``.

    Apres un merge, les PRs soeurs passent ``unknown`` le temps que GitHub
    recalcule : jusqu'a MERGEABLE_RETRIES relectures avec court sommeil avant
    de conclure au skip.
    """
    data: dict = {}
    for attempt in range(MERGEABLE_RETRIES + 1):
        res = runner.run(
            ["gh", "api", f"repos/{REPO}/pulls/{pr}"], env=gh_env
        )
        if res.returncode != 0:
            raise UnexpectedError(
                f"gh api pulls/{pr} rc={res.returncode} : {res.stderr.strip()[:200]}"
            )
        data = _json_stdout(res, f"pulls/{pr}")  # type: ignore[assignment]
        if not isinstance(data, dict):
            raise UnexpectedError(f"pulls/{pr} : la reponse n'est pas un objet")
        state = str(data.get("mergeable_state") or "")
        if state != "unknown":
            return state, str(((data.get("head") or {}).get("sha")) or "")
        if attempt < MERGEABLE_RETRIES:
            runner.sleep(MERGEABLE_RETRY_SLEEP_S)
    state = str(data.get("mergeable_state") or "")
    return state, str(((data.get("head") or {}).get("sha")) or "")


# --- etape 6 bis : `unstable` est-il un etat mergeable ? (#25059) -------------

#: Une jambe terminee et sans reproche : meme ensemble que le gate
#: (``pr_gate.CONCLUSION_OK`` -- success, neutral, skipped). Un ``cancelled``
#: n'y est pas : une jambe annulee n'a rien mesure.
CHECK_GREEN = pr_gate.CONCLUSION_OK

#: Le nom du check requis : la porte elle-meme. C'est le nom que le gate
#: utilise pour se comparer a lui (``DEFAULT_SELF_NAME``).
GATE_CHECK_NAME = pr_gate.DEFAULT_SELF_NAME

#: Second marqueur de non-bloquant du depot : le gate reconnait ``advisory``
#: (``pr_gate.ADVISORY_MARKER``), et le depot ecrit aussi ``non-blocking``
#: dans le nom de certains checks. #25059 les nomme tous les deux.
NON_BLOCKING_MARKER = "non-blocking"

#: Roster des jobs dont le WORKFLOW porte le marqueur advisory (le nom du job
#: ne le porte pas). Derive des YAML de ``.github/workflows``, une fois par
#: run : le relire a chaque PR serait du gaspillage.
_ADVISORY_JOBS: frozenset[str] | None = None


def advisory_jobs() -> frozenset[str]:
    """Le roster advisory du depot, lu une fois.

    Fail-open sur le roster : un roster illisible signifie « moins de checks
    reconnus comme non bloquants », donc une decision PLUS stricte -- jamais
    un merge plus permissif.
    """
    global _ADVISORY_JOBS
    if _ADVISORY_JOBS is None:
        try:
            _ADVISORY_JOBS = pr_gate.derive_advisory_jobs()
        except Exception:  # pragma: no cover - lecture des YAML impossible
            _ADVISORY_JOBS = frozenset()
    return _ADVISORY_JOBS


def _is_non_blocking(name: str, jobs: frozenset[str]) -> bool:
    """Un check qui ne bloque pas, au sens du gate ET de #25059.

    Le test est celui du gate : ``pr_gate.is_advisory`` (le job porte le
    marqueur, ou son workflow le porte -- roster derive des YAML). Le second
    marqueur du depot (``non-blocking``) est ajoute ici parce qu'il n'est pas
    dans ``ADVISORY_MARKER`` : un check qui ne porte QUE ce marqueur ne
    bloque pas le gate, il ne doit pas bloquer l'organe de merge non plus.
    """
    workflow_label = "advisory" if name in jobs else ""
    if pr_gate.is_advisory(name, workflow_label):
        return True
    return NON_BLOCKING_MARKER in (name or "").lower()


def unstable_state_reason(
    runner: Runner, pr: int, head: str, gh_env: dict[str, str]
) -> tuple[str | None, str]:
    """Etape 6 bis (#25059) : l'etat ``unstable`` accepte-t-il la PR ?

    Retourne ``(raison, detail)``. ``raison is None`` = la PR passe, et
    ``detail`` porte le compte ``unstable-accepted:<n advisory/cancelled-
    superseded>>``. Sinon ``raison`` nomme le check qui bloque -- un saut
    nomme, jamais un refus muet.

    Le pli est celui du gate : ``pr_gate.dedupe_latest``, applique deux fois
    sur deux ensembles de jambes :
      - sur TOUTES les jambes : la plus recente par nom -- c'est elle qui
        fait foi (une jambe encore en vol est donc celle qui compte) ;
      - sur les jambes TERMINEES seulement : la derniere terminee par nom --
        c'est elle qui dit si le nom a ete vert au moins une fois.

    Regle (#25059) : ``unstable`` est accepte si et seulement si
      1. la derniere jambe du ``PR gate`` est terminee et ``success`` ;
      2. chaque nom de check non advisory a au moins une jambe terminee ;
      3. la derniere jambe TERMINEE de chaque nom non advisory est verte.

    Ce qui n'est pas accepte : une porte absente ou non verte, un nom sans
    jambe terminee, un nom dont la derniere jambe terminee est rouge, et une
    lecture des jambes impossible (fail-closed : l'absence de mesure n'est
    pas une mesure).
    """
    res = runner.run(
        ["gh", "api",
         f"repos/{REPO}/commits/{head}/check-runs?per_page=100",
         "--paginate",
         "--jq",
         ".check_runs[] | {name, conclusion, status, started_at, id} | tojson"],
        env=gh_env,
    )
    if res.returncode != 0:
        return ("mergeable-state:unstable:check-runs-unreadable", "")
    try:
        raw = [
            json.loads(line)
            for line in (res.stdout or "").splitlines()
            if line.strip()
        ]
    except ValueError:
        return ("mergeable-state:unstable:check-runs-unreadable", "")
    legs: list[dict] = []
    for row in raw:
        leg = check_run_state.normalize_leg(row)
        # `normalize_leg` garde cinq champs ; le statut est ajoute ici pour
        # que le motif du saut dise « en vol » plutot que « sans verdict ».
        leg["status"] = str(row.get("status") or "").lower()
        legs.append(leg)
    latest = {leg["name"]: leg for leg in pr_gate.dedupe_latest(legs)}
    done_legs = [leg for leg in legs if leg.get("conclusion")]
    latest_done = {leg["name"]: leg for leg in pr_gate.dedupe_latest(done_legs)}

    # 1. la porte elle-meme : sa derniere jambe (la plus recente) doit etre
    #    terminee et verte. Une porte qui tourne encore n'est pas un acquis.
    gate_leg = next(
        (leg for name, leg in latest.items()
         if name == GATE_CHECK_NAME or name.startswith(GATE_CHECK_NAME + " /")),
        None,
    )
    if gate_leg is None:
        return ("mergeable-state:unstable:no-pr-gate-leg", "")
    if gate_leg.get("conclusion") != "success":
        state = (gate_leg.get("conclusion") or gate_leg.get("status")
                 or "no-verdict")
        return (f"mergeable-state:unstable:{GATE_CHECK_NAME}:{state}", "")

    jobs = advisory_jobs()
    advisory_count = 0
    for name in sorted(latest):
        if name == gate_leg["name"]:
            continue
        if _is_non_blocking(name, jobs):
            advisory_count += 1
            continue
        done = latest_done.get(name)
        if done is None:
            return (f"mergeable-state:unstable:{name}:no-completed-leg", "")
        if done.get("conclusion") not in CHECK_GREEN:
            return (
                f"mergeable-state:unstable:{name}:{done.get('conclusion')}",
                "",
            )
    # Le compte du verdict : les checks non bloquants rencontres, et les
    # jambes annulees d'un run remplace (une jambe annulee qui n'est pas la
    # derniere terminee de son nom a ete supersedee par une verte).
    superseded = 0
    for name, leg in latest_done.items():
        superseded += sum(
            1
            for other in done_legs
            if other["name"] == name
            and other.get("conclusion") == "cancelled"
            and (other.get("started_at") or "", other.get("id") or 0)
            != (leg.get("started_at") or "", leg.get("id") or 0)
        )
    return (
        None,
        f"unstable-accepted:{advisory_count + superseded} advisory/cancelled-superseded",
    )


def merge_pr(runner: Runner, pr: int, head: str, gh_env: dict[str, str]) -> None:
    """Etape 7 : squash merge epingle sur la tete evaluee (jamais --admin,
    jamais --delete-branch)."""
    res = runner.run(
        ["gh", "pr", "merge", str(pr), "--repo", REPO,
         "--squash", "--match-head-commit", head],
        env=gh_env,
    )
    if res.returncode != 0:
        raise MergeFailedError(
            f"gh pr merge {pr} rc={res.returncode} : "
            f"{(res.stderr or res.stdout).strip()[:200]}"
        )


# --- tour de controle par PR ---------------------------------------------------

# La raison rendue par ``gate.stack_reasons`` nomme la PR partenaire sous la
# forme ``OPEN #<N>`` : le motif de skip n'en retient que ce numero (motif
# court ; la raison complete vit dans le rapport de la porte).
_STACK_PARTNER_RE = re.compile(r"OPEN #(\d+)")


def evaluate_pr(
    view: dict, pr: int, runner: Runner, gh_env: dict[str, str]
) -> PRVerdict:
    """Applique dans l'ordre les controles pre-merge (1 a 6, 5bis compris). Tout echec = skip nomme.

    Les controles bon marche (brouillon, perimetre, tag) passent AVANT la
    porte STACK -- la premiere etape couteuse, dont l'index de pile est
    construit une fois par run puis cache par le module du gate ; la porte
    avant les organes ; le REST en dernier, juste avant le merge, pour
    minimiser la fenetre de course.

    La disposition de review (point 1 de #17672) est classee pour TOUTE PR
    evaluee, skip compris, et reportee a la tete que la ligne declare : la
    tete de la vue -- celle que l'approbation couvre et que le merge
    epingle, l'etape 6 ayant deja refuse une tete qui a bouge depuis.
    """

    view_head = str(view.get("headRefOid") or "")
    disposition = review_disposition(view, view_head)

    def skip(reason: str, stack: str | None = None,
             stack_incidents: tuple[str, ...] | None = None) -> PRVerdict:
        return PRVerdict(pr, view_head, "skipped", reason, False, disposition,
                         stack, stack_incidents)

    # 1. prefiltre bon marche.
    if view.get("isDraft"):
        return skip("draft")
    # 2. perimetre (b), fail-closed.
    for file_row in view.get("files") or []:
        reason = scope_exclusion(str((file_row or {}).get("path") or ""))
        if reason is not None:
            return skip(reason)
    # `gh pr view --json files` plafonne la liste : une PR plus grosse que ce
    # plafond cacherait peut-etre un fichier hors perimetre -> fail-closed.
    changed = view.get("changedFiles")
    listed = len(view.get("files") or [])
    if not isinstance(changed, int) or changed > listed:
        return skip(f"files-truncated:{listed}/{changed}")
    reason = grain_exclusion(view.get("body"), view.get("headRefName"))
    if reason is not None:
        return skip(reason)
    reason = frozen_umbrella_exclusion(
        view.get("title"), view.get("body"), view.get("headRefName")
    )
    if reason is not None:
        return skip(reason)
    # 2bis. garde Lean (#24989) : une PR qui touche du Lean exige une
    # attestation de `lake build` local posee par le coordinateur et
    # couvrant la tete (regle HARD `lean-merge-discipline.md` §1). Placee
    # AVANT 2ter : une PR sans attestation n'attend pas sa relecture, elle
    # est bloquee pour un AUTRE motif -- la porter en disposition
    # ``review-ready`` serait un mensonge.
    reason = lean_build_attestation_reason(view, view_head, runner, gh_env)
    if reason is not None:
        return skip(reason)
    # 2ter. approbation du coordinateur (Q67) : une PR non lue ne paie pas
    # l'index de pile. Si on skip ici, les portes delegables EN AMONT ont
    # toutes ete vertes (perimetre 2, tag et parapluie gele) -- c'est
    # precisement la definition de l'etat REVIEW_READY (#17672 point 2) :
    # seule manque l'approbation ai-01 a la tete exacte. On la porte en
    # disposition, le ``reason`` conserve la granularite
    # (``no-coordinator-approval`` / ``coordinator-approval-stale`` /
    # ``coordinator-approval-unverifiable``).
    reason = coordinator_approval_reason(view, view_head, runner, gh_env)
    if reason is not None:
        return PRVerdict(pr, view_head, "skipped", reason, False, REVIEW_READY)
    # 3. porte STACK (#20251), en processus. C'est le seul apport du gate
    # qu'aucune autre etape ne couvrait ; le module du gate l'expose
    # directement : ``default_stack_index`` construit l'index une fois par
    # run (verrou + cache dans le module), ``stack_reasons`` nomme les
    # sommets de pile perimes. Fail-open sur index illisible, meme
    # convention que le gate (UNKNOWN != rouge forge) : l'etat se
    # journalise, il ne fabrique aucun refus.
    stack_state: str | None
    stack_inc: tuple[str, ...] | None
    index = gate.default_stack_index()
    if index is None:
        stack_state = "unmeasured"
        # Acces direct au cache du module : c'est lui qui porte les incidents
        # de la mesure qui vient d'echouer (aucun accesseur public ne les
        # expose).
        incidents = gate._STACK_INDEX_CACHE.get("incidents") or []
        stack_inc = tuple(str(item) for item in incidents) or None
    else:
        stack_state = "measured"
        stack_inc = None
        reasons = gate.stack_reasons(pr, index)
        if reasons:
            # Motif court nommant la PR partenaire ; la raison complete du
            # gate (commits partages, sujets manquants) vit dans le rapport
            # de la porte elle-meme.
            match = _STACK_PARTNER_RE.search(reasons[0])
            partner = match.group(1) if match else "?"
            return skip(f"stack-top:{partner}", "measured")
    # 4. organe B.0 (re-verification reelle).
    if run_nits(runner, pr, gh_env) != 0:
        return skip("b0-organ-blocked", stack_state, stack_inc)
    # 5bis. collision d'index twin contre le main du moment.
    reason = twin_collision_reason(runner, pr, view_head, view.get("files") or [])
    if reason is not None:
        return skip(reason, stack_state, stack_inc)
    # 5bis.bis. collision de slot contre la base ET les PRs ouvertes (#20774).
    # Independant de 5bis : 5bis = twin-pair registry, 5bis.bis = slot de carnet.
    reason = slot_reservation_reason(runner, pr, view_head, view.get("files") or [])
    if reason is not None:
        return skip(reason, stack_state, stack_inc)
    # 5ter. defense en profondeur : la base de la PR doit etre `main` (#19002,
    # distingue en #19014). Depuis le retrait du dossier (2026-11-05),
    # merge_ready est seul porteur de ce controle : c'est l'organe qui
    # **execute** le merge, il doit verifier lui-meme. Le `view` charge a
    # l'etape 0 porte la base via `PR_VIEW_FIELDS` ; on la lit ici pour
    # eviter un round-trip REST supplementaire. La base morte
    # (squash-mergee ou fermee) et la base empilee sur une PR ouverte
    # (vivante) portent toutes deux un nom qui n'est pas `main`, mais la
    # lane n'a pas le meme geste a faire (retargeter vs. attendre) -- d'ou
    # les deux motifs distincts `base-gone` et `base-live-not-main`.
    base_ref_name = view.get("baseRefName") or ""
    if base_ref_name != "main":
        liveness = base_ref_liveness(runner, gh_env, base_ref_name)
        if liveness == "live":
            return skip(f"base-live-not-main:{base_ref_name}",
                        stack_state, stack_inc)
        if liveness == "gone":
            return skip(f"base-gone:{base_ref_name}", stack_state, stack_inc)
        return skip(f"base-not-main-unreadable:{base_ref_name}",
                    stack_state, stack_inc)
    # 5quater. PR empilee via convention body (depends on / blocked by /
    # stacked on) avec baseRefName == main. Le cas Origami 2026-10-08 :
    # 6 PRs empilees logiquement, baseRefName = main sur chacune (la
    # convention GitHub est de rebrancher chaque PR sur main apres un
    # update-branch), 5 d'entre elles sans CI complete parce que la
    # racine n'avait pas ete mergee. base_ref_liveness ne s'applique
    # pas (base = main), mais la parente empilee dans le body donne
    # l'info manquante. Refus tant que la parente n'est pas MERGED.
    # TOUTES les parentes declarees sont examinees, pas seulement la
    # premiere : un body « Depends on #A / Blocked by #B » dont #A est
    # MERGED ne doit pas repartir au nominal en laissant #B ouverte.
    for parent in find_stacked_parents(view.get("body")):
        if parent == pr:
            # Se declarer soi-meme parente est un body mal forme : etat
            # explicite plutot qu'ignorance silencieuse.
            return skip(f"stacked-on-main:{parent}:self-reference",
                        stack_state, stack_inc)
        pstate = stacked_parent_state(runner, parent, gh_env)
        if pstate != "MERGED":
            return skip(f"stacked-on-main:{parent}:{pstate}",
                        stack_state, stack_inc)
    # Prelecture REST bon marche : ne pas payer les tests d'arbre fusionne
    # pour une PR que l'etape 6 refuserait. L'etape 6 reste la garde finale
    # contre une evolution de l'etat ou de la tete pendant ces tests.
    pre_state, pre_live_head = mergeable_state_and_head(runner, pr, gh_env)
    if pre_state not in ("clean", "unstable"):
        return skip(f"mergeable-state:{pre_state or 'absent'}",
                    stack_state, stack_inc)
    if pre_live_head != view_head:
        return skip("head-moved", stack_state, stack_inc)
    # 5quinquies. tests d'integrite sur l'arbre fusionne main + tete. Place
    # apres tous les autres controles bon marche (il coute ~1 min) et avant le
    # REST final, qui reste le dernier pour garder la fenetre de course courte.
    reason = combined_tree_reason(runner, pr, view_head, gh_env)
    if reason is not None:
        return skip(reason, stack_state, stack_inc)
    # 6. REST : mergeable + tete.
    state, live_head = mergeable_state_and_head(runner, pr, gh_env)
    accepted_detail: str | None = None
    if state == "unstable":
        # 6bis (#25059) : `unstable` n'est pas un refus automatique. La chaine
        # v9 l'acceptait quand le pli latest-wins etait vert ; l'organe qui l'a
        # remplace ne l'a pas repris, et 13 PRs approuvees a la tete dormaient
        # la-dessus (mesure du coordinateur, 07/11 13:20Z). La decision est
        # prise SUR LES JAMBES, au pli du gate : un saut nomme, jamais un refus
        # muet.
        reason, detail = unstable_state_reason(
            runner, pr, live_head or view_head, gh_env
        )
        if reason is not None:
            return skip(reason, stack_state, stack_inc)
        accepted_detail = detail
    elif state != "clean":
        return skip(f"mergeable-state:{state or 'absent'}",
                    stack_state, stack_inc)
    if live_head != view_head:
        return skip("head-moved", stack_state, stack_inc)
    return PRVerdict(
        pr, view_head, "would-merge", accepted_detail, False,
        disposition, stack_state, stack_inc,
    )


# --- journal -------------------------------------------------------------------


def append_journal(path: Path, verdict: PRVerdict) -> None:
    """Une ligne JSON par PR evaluee ; repertoire cree si absent."""
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(verdict.journal_dict(), ensure_ascii=False) + "\n")
    except OSError as exc:
        raise UnexpectedError(f"ecriture du journal {path} impossible : {exc}") from exc


# --- sortie --------------------------------------------------------------------


def _stack_suffix(verdict: PRVerdict) -> str:
    """Mention de la porte STACK quand la mesure n'a pas abouti (#22066).

    La porte est fail-open : un incident de mesure ne fabrique aucun refus.
    Mais un READY dont la porte STACK n'a pas ete mesuree ne doit pas se
    lire comme un READY complet -- la mention le dit, sans rien changer a
    la decision.
    """
    if verdict.stack != "unmeasured":
        return ""
    incidents = verdict.stack_incidents or ()
    detail = f" ({'; '.join(incidents)})" if incidents else ""
    return f" [STACK non mesure{detail}]"


def _describe(verdict: PRVerdict) -> str:
    if verdict.verdict == "merged":
        return (
            f"PR #{verdict.pr} MERGED ({verdict.head}) [review: {verdict.review}]"
            f"{_stack_suffix(verdict)}"
        )
    if verdict.verdict == "would-merge":
        return (
            f"PR #{verdict.pr} WOULD MERGE ({verdict.head}) [dry-run] "
            f"[review: {verdict.review}]{_stack_suffix(verdict)}"
        )
    if verdict.verdict == "merge-failed":
        return f"PR #{verdict.pr} MERGE ECHOUE : {verdict.reason}"
    if verdict.verdict == "run-error":
        return f"PR #{verdict.pr} ERREUR INATTENDUE : {verdict.reason}"
    return f"PR #{verdict.pr} skip : {verdict.reason}"


def emit_output(
    args: argparse.Namespace,
    results: list[PRVerdict],
    stopped_reason: str | None,
    exit_code: int,
) -> None:
    """Resume humain sur stdout, ou payload machine unique en --json."""
    if args.json:
        payload = {
            "apply": args.apply,
            "max": args.max,
            "stopped_reason": stopped_reason,
            "exit_code": exit_code,
            "results": [v.journal_dict() for v in results],
        }
        print(json.dumps(payload, ensure_ascii=False))
        return
    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"== merge_ready ({mode}, max {args.max}) ==")
    for verdict in results:
        print(_describe(verdict))
    merged = sum(1 for v in results if v.merged)
    would = sum(1 for v in results if v.verdict == "would-merge")
    skipped = sum(1 for v in results if v.verdict == "skipped")
    errored = sum(1 for v in results if v.verdict == "run-error")
    # La disposition de review ne se compte que sur les candidates au merge :
    # c'est la que « approbation a la tete exacte » ou « ailleurs » decide.
    candidates = [v for v in results if v.verdict in ("merged", "would-merge")]
    at_head = sum(1 for v in candidates if v.review == APPROVED_EXACT_HEAD)
    off_head = sum(1 for v in candidates if v.review == APPROVAL_NOT_ON_HEAD)
    print(
        f"bilan : {len(results)} evaluee(s), {merged} merge(s), "
        f"{would} would-merge, {skipped} skip(s)"
        # Une erreur isolee ne s'annonce par aucune ligne « arret » : sans ce
        # compte, un run qui a continue malgre une PR en erreur se lirait comme
        # un run propre (#17672 point 3).
        + (f", {errored} erreur(s) isolee(s)" if errored else "")
        + (
            f", candidates : {at_head} approved-exact-head, "
            f"{off_head} approval-not-on-head"
            if candidates
            else ""
        )
    )
    if stopped_reason:
        print(f"arret : {stopped_reason}")


# --- boucle de run ---------------------------------------------------------------


def run(argv: list[str] | None = None, runner: Runner | None = None) -> int:
    """Point d'entree testable : parse les arguments, execute un run complet."""
    args = _parse_args(argv)
    active_runner = runner if runner is not None else SubprocessRunner()
    journal_path = (
        args.journal if args.journal is not None else default_journal_path()
    )
    hold_path = (
        args.hold_file if args.hold_file is not None else default_hold_path(journal_path)
    )
    if args.clear_main_red_hold:
        # Voie manuelle : aucune lecture GitHub, aucune PR evaluee. La ligne
        # de la sentinelle seule est retiree ; les retenues du coordinateur
        # restent intactes.
        try:
            removed = clear_main_red_hold(hold_path)
        except OSError as exc:
            print(
                f"merge_ready : fichier de retenues {hold_path} illisible -- {exc}",
                file=sys.stderr,
            )
            return 2
        if args.json:
            emit_output(
                args, [], "main-red-hold-cleared" if removed else "main-red-hold-absent", 0
            )
        else:
            print(
                "merge_ready : ligne de la sentinelle retiree"
                if removed else
                "merge_ready : aucune ligne de la sentinelle a retirer"
            )
        return 0
    try:
        holds = load_holds(hold_path)
        token = resolve_token(active_runner)
        refresh_main_red_hold(active_runner, {**os.environ, "GH_TOKEN": token}, hold_path)
        holds = load_holds(hold_path)
    except CannotRunError as exc:
        print(f"merge_ready : impossible de demarrer -- {exc}", file=sys.stderr)
        return 2
    gh_env = {**os.environ, "GH_TOKEN": token}

    results: list[PRVerdict] = []
    stopped_reason: str | None = None
    exit_code = 0
    try:
        prs = list_open_prs(active_runner, gh_env)
    except UnexpectedError as exc:
        # Echec avant la boucle : aucune PR evaluee, rien a journeler.
        print(f"merge_ready : ARRET sur erreur inattendue -- {exc}", file=sys.stderr)
        emit_output(args, results, f"unexpected-error:{exc}", 1)
        return 1

    merged_count = 0
    for pr in prs:
        # Disjoncteur --max : plafond de DECISIONS de merge du run (merges
        # reels en --apply, would-merge en dry-run : le dry-run doit refléter
        # ce que --apply ferait). Une fois le plafond atteint, les PRs
        # restantes ne sont pas evaluees (le journal ne couvre que l'evalue).
        if merged_count >= args.max:
            stopped_reason = "max-merges-reached"
            break
        if MAIN_RED_HOLD_NUMBER in holds or pr in holds:
            reason = holds.get(MAIN_RED_HOLD_NUMBER, holds.get(pr, "hold.txt"))
            held = PRVerdict(pr, None, "skipped", f"hold:{reason}", False)
            results.append(held)
            try:
                append_journal(journal_path, held)
            except UnexpectedError as exc:
                stopped_reason = f"unexpected-error:{exc}"
                exit_code = 1
                break
            continue
        try:
            view = fetch_pr_view(active_runner, pr, gh_env)
            decision = evaluate_pr(view, pr, active_runner, gh_env)
            if decision.verdict == "would-merge":
                if args.apply:
                    try:
                        merge_pr(active_runner, pr, decision.head or "", gh_env)
                    except MergeFailedError as exc:
                        failed = PRVerdict(
                            pr, decision.head, "merge-failed", str(exc), False,
                            decision.review, decision.stack,
                            decision.stack_incidents,
                        )
                        results.append(failed)
                        append_journal(journal_path, failed)
                        stopped_reason = f"merge-failed:PR-{pr}"
                        exit_code = 1
                        break
                    decision = PRVerdict(
                        pr, decision.head, "merged", decision.reason, True,
                        decision.review,
                        decision.stack, decision.stack_incidents,
                    )
                merged_count += 1
            results.append(decision)
            append_journal(journal_path, decision)
        except UnexpectedError as exc:
            errored = PRVerdict(pr, None, "run-error", str(exc), False)
            results.append(errored)
            append_journal(journal_path, errored)
            exit_code = 1
            if is_pass_wide(exc):
                # Toute la passe est touchee : repeter l'echec sur chacune des
                # PRs restantes ne dirait rien de plus.
                stopped_reason = f"unexpected-error:{exc}"
                break
            # Erreur attribuable a CETTE PR : elle est nommee et journalisee,
            # le balayage continue (#17672 point 3). `stopped_reason` reste
            # None -- le run ne s'est PAS arrete, l'ecrire ici serait un
            # constat faux (le bilan, lui, compte les erreurs isolees).
            continue

    emit_output(args, results, stopped_reason, exit_code)
    return exit_code


def _parse_args(argv: list[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="merger reellement (defaut : dry-run, aucun merge)",
    )
    parser.add_argument(
        "--max",
        type=int,
        default=MAX_MERGES_DEFAULT,
        metavar="N",
        help=f"plafond de merges par run, disjoncteur (defaut {MAX_MERGES_DEFAULT})",
    )
    parser.add_argument(
        "--journal",
        type=Path,
        default=None,
        help=(
            "chemin du journal JSONL (defaut "
            "%%LOCALAPPDATA%%/CoursIA/merge_ready/journal.jsonl)"
        ),
    )
    parser.add_argument(
        "--hold-file",
        type=Path,
        default=None,
        help="fichier de retenues (defaut : hold.txt a cote du journal)",
    )
    parser.add_argument(
        "--clear-main-red-hold",
        action="store_true",
        help=(
            "retire UNIQUEMENT la ligne de la sentinelle du fichier de "
            "retenues, puis sort (aucun appel gh, aucune PR evaluee). "
            "Sert au correctif d'un `main` rouge : la retenue globale saute "
            "aussi la PR qui le repare."
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="sortie machine (un seul objet JSON) sur stdout",
    )
    args = parser.parse_args(argv)
    if args.max < 0:
        parser.error("--max doit etre >= 0")
    return args


def main() -> int:
    return run()


if __name__ == "__main__":
    sys.exit(main())
