#!/usr/bin/env python3
r"""prune_merged_worktrees.py -- retire les worktrees de PRs mergées/fermées (#14195, dette #8924).

## Why this exists

`po-2026:Maintenance` mesure le 2026-09-02T01:20Z : **265 worktrees recréés en 36 h**
(178 CoursIA + 87 CoursIA-2, contre ~0 le 31/08). Cause première nommée par
l'auteur de la mesure : **chaque review de PR notebook / build Lean crée un
worktree ; rien ne les retire quand la PR est mergée.**

#8924 avait écrit le mécanisme (CLOSED le 2026-08-05 après un nettoyage
manuel, 131 worktrees retirés). Le nettoyage était bon ; l'organe n'a jamais
été construit. La classe est revenue, à quatre fois l'échelle, vingt-huit
jours plus tard. C'est le motif « une règle non appliquée demande un organe,
pas plus de vigilance ».

Ce script est cet organe.

## What it does

  $ python scripts/ci/prune_merged_worktrees.py
  # dry-run (default) : affiche les retraits prévus + les refus motivés
  WOULD REMOVE  <path>  branch=fix/X  pr=#14427(MERGED)
  REFUSE       <path>  branch=fix/Y  reason=pr_open    pr=#14433
  REFUSE       <path>  branch=fix/Z  reason=unpushed_commits  ahead=2
  REFUSE       <path>  branch=fix/W  reason=untolerated_untracked:1
                                                     ignored=.env
  REFUSE       <path>  branch=fix/V  reason=contains_submodules
  ---
  total=5  removable=1  refused=4

  $ python scripts/ci/prune_merged_worktrees.py --apply
  # applique les retraits ; les refus restent dans le rapport (exit 0,
  # cf #3895 : un refus est une decision de l'outil, pas une panne)

  $ python scripts/ci/prune_merged_worktrees.py --json
  {"scanned": 4, "removable": 1, "refused": 3, "actions": [...]}

  $ python scripts/ci/prune_merged_worktrees.py --path /c/dev/CoursIA-X
  # ne considere qu'un worktree (test)

  $ python scripts/ci/prune_merged_worktrees.py --warn-threshold 20
  # emet sur stderr une ligne [WARN][prune-task] prete a poster sur le
  # dashboard workspace des que refused > 20 (desactive par defaut)

Critères de retrait (cf issue #14195 acceptance) :

1. **Worktree avec commits non poussés** (`git rev-list --count @{u}..HEAD > 0`) :
   REFUSE, jamais d'exception. Aucune branche n'est mergee alors qu'elle a
   du travail non publie.
2. **Worktree avec une PR OPEN** : REFUSE. Le retrait casserait l'iteration
   en cours.
3. **Worktree avec une PR MERGED ou CLOSED (non-merged)** : REMOVE.
4. **Worktree sans branche (HEAD détaché)** : verdict par contenu. Si
   `git log origin/main --grep "<branch_topic>"` trouve un commit dont le
   sujet correspond (le squash a efface l'ascendance) : REMOVE ; sinon REFUSE.
   Un HEAD détaché **ancêtre de `origin/main`** n'a aucun commit propre,
   donc aucune PR : REFUSE (`reason=detached_on_main`, #17684). Seuls les
   sujets de `origin/main..HEAD` sont lus pour attribuer une PR.
5. **Worktree avec residu untracked non tolere** : REFUSE, cause nommee
   (`reason=untolerated_untracked:<n>`, #14619 point 2). Pouvoir de refus
   git (#14509) : `git worktree remove` sans `--force` refuse TOUT
   non-suivi au moment du retrait. Les artefacts toleres (bg_logs/, logs
   lake, tokens #8924) ne bloquent pas : l'apply les NETTOIE d'abord
   (`clean_tolerated_artifacts`), le remove s'execute ensuite sur un
   worktree que git acceptera. Tout residu hors liste toleree reste
   REFUSE -- c'est le complement fail-closed du couple
   classification/execution. Les fichiers SOURCE untracked non toleres
   et les tracked modifies refusent en amont
   (`reason=uncommitted_source_changes`).
6. **Worktree avec submodules initialisés** : REFUSE
   (`reason=contains_submodules`). `git worktree remove` refuse
   structurellement ces worktrees ("working trees containing submodules
   cannot be moved or removed") : le prononcer REFUSE evite un FAILED a
   chaque passe --apply. Les gitignorés **non-cache** (`.env` laissé, ...)
   sont signalés (`ignored=...`) sans bloquer le retrait.

Ancre PR : `gh pr list --state all --search "head:<branch>"` (autoritative,
cf matrice a 4 ancres de `.claude/rules/git-workflow.md` §orphan-branch-scan).
Ni `--is-ancestor` seul ni `commits/<oid>/pulls` ne suffisent : le premier
rate les squash-merges, le second a des faux negatifs mesures.

## Observabilite des refus (#3895, roo-extensions)

Mesure fondatrice (3 machines, 27/09/2026) : **86-100 % des worktrees vus
sont REFUSE** -- les worktrees de cycle naissent HEAD-detaches ou avec des
modifications non commitees par construction, le predicat « PR MERGED et
arbre propre » est insatisfaisable pour eux (po-2023 a sature ses deux
disques dessus). Les refus sont donc un RAPPORT, pas un echec :

- la sortie porte le decompte par classe de refus (`refusals: ...` en
  texte, `refusal_reasons` en JSON) ;
- quand un marqueur `.lane-owner` vit a la racine du worktree (une
  ligne : le nom de la lane proprietaire, posee par le spawn -- convention
  #3895), les refus sont attribues par lane (`lane=...` en texte,
  `lane_refusals` en JSON) ;
- `--warn-threshold N` emet sur stderr une ligne `[WARN][prune-task]`
  prete pour le dashboard workspace des que `refused > N`. La tache
  planifiee (`install_prune_task.py`, N=20 par defaut) la journalise
  chaque nuit ; le RELAIS dashboard reste aux agents de lane -- une
  tache planifiee n'a pas d'acces MCP (pattern heartbeat_sweep_emit,
  #12588).

## Design rules that matter

1. **Dry-run par defaut, --apply explicite.** Jamais de retrait silencieux.
2. **Journal de refus obligatoire.** Un outil de purge qui ne dit pas ce
   qu'il épargne est indiscernable d'un outil qui ne regarde pas.
3. **`--force` reserve aux enregistrements morts, jamais general.** Le
   retrait est `git worktree remove` sans --force ; si git refuse (worktree
   sale), on log la cause et on continue. C'est ce refus qui reste le
   dernier garde-fou quand la classification s'est trompee : le rendre
   inoperant par un --force inconditionnel oterait au dispositif sa seule
   verification externe. Depuis #14619 : avant le retrait, l'apply supprime
   exactement les artefacts untracked toleres (et eux seuls --
   clean_tolerated_artifacts), sinon git refuse sur tout non-suivi et un
   worktree classe REMOVE pour artefacts seulement ne part jamais. Un residu
   hors liste tolerree est classe REFUSE (untolerated_untracked), pas REMOVE,
   et un worktree a sous-modules REFUSE (contains_submodules).
   **Unique exception (#14195)** : un enregistrement dont le CHECKOUT a
   disparu (`dead_registration`, predicat 1bis) est retire avec --force --
   sans lui git refuse un arbre absent ("contains modified or untracked
   files") et l'organe annoncerait un REMOVE qu'il ne peut pas executer. Le
   drapeau est calcule par deux conditions conjonctives (toute modification
   est une suppression ET >= DEAD_TREE_RATIO de l'index a disparu), et
   `test_no_unconditional_force` pinne que le --force reste sous ce test.
4. **Mode `--json` parallele au mode texte.** Mêmes chiffres, même ordre ;
   le recipient downstream (dashboard sweep, DM ai-01) parse le JSON sans
   réinventer le rendu.
5. **Exit code : 0 si la passe s'est deroulee sans erreur (dry-run ou
   apply reussi), 2 si erreur gh/git infra ou echec d'application.** Un
   REFUS n'est plus un echec : a 86-100 % de refus (mesure #3895 sur 3
   machines), le « 1 si refus observe » d'avant rendait la tache planifiee
   rouge (LastResult 0x1) toutes les nuits en reussissant -- un vrai
   echec gh y etait indissociable du bruit. Depuis #3895, `1` n'est
   plus emis (reserve, non contractuel) ; le detail des refus vit dans
   le rapport, pas dans le code de sortie.
6. **Pas d'auto-retry.** Si `gh` echoue (auth, rate-limit, network), exit 2
   sans fallback silencieux.
7. **Worktree courant exclu.** On ne tente jamais `git worktree remove` sur
   le worktree depuis lequel le script est lance -- un retrait du repertoire
   de travail serait fatal.

## Run locally

    python scripts/ci/prune_merged_worktrees.py
    python scripts/ci/prune_merged_worktrees.py --apply
    python scripts/ci/prune_merged_worktrees.py --json
    python scripts/ci/prune_merged_worktrees.py --path /c/dev/CoursIA-X

Exit codes:
    0  OK (passe saine, refus compris -- un refus est une decision, pas un echec)
    1  Plus jamais emis (avant #3895 : « refus observes » ; rendait la tache
       planifiee rouge chaque nuit. Reserve, non contractuel)
    2  Erreur gh/git infra ou echec d'application (auth, rate-limit, etc.)

## Coupling with #14195 et #8924

#8924 est le precedent CLOSED : mecanisme nomme, organe non construit.
#14195 demande cet organe. Ce script ferme la dette.

## Acceptance criteria (depuis #14195)

- [x] `scripts/ci/prune_merged_worktrees.py` livre, dry-run par defaut,
      `--apply` explicite
- [x] Tests d'affaiblissement : commits non pousses refuses, PR open
      refusee, arbre sale edition source refuse, branche squash-mergee
      retiree (controle positif du predicat d'ascendance)
- [x] Journal nomme chaque refus avec sa cause
- [x] Ligne dans `.claude/rules/git-workflow.md` : commande canonique en
      fin de cycle
- [x] Mesure avant/apres sur machine reelle, posee en commentaire issue

## Acceptance criteria (depuis #14509, composes avec #14619 au merge)

- [x] Le predicat de salete rebranche sur la politique git reelle : les
      toleres sont NETTOYES a l'apply puis le remove s'execute sans
      --force (le REMOVE annonce reussit) ; tout residu non tolere ->
      REFUSE `untolerated_untracked:<n>` ; fichier source untracked non
      tolere ou tracked modifie -> REFUSE `uncommitted_source_changes`
- [x] Worktrees a submodules initialises classes REFUSE
      `contains_submodules` (git ne les retirera jamais)
- [x] Gitignores non-cache signales dans la sortie (`ignored=...`) sans
      bloquer le retrait (registre `ignored_extra`, passe porcelain
      `--ignored=matching`)
- [x] Registre `blocking_untracked` (untracked non-ignores NON toleres)
      expose sur chaque verdict pour la decision humaine
"""
from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import traceback
from pathlib import Path
from typing import Optional


# Categories d'artefacts (cf commentaire final de #8924). Depuis #14509
# elles ne servent PLUS a tolerer des untracked : `git worktree remove`
# (sans --force) refuse TOUT untracked non-ignore, quelle que soit son
# extension ou son absence d'extension (mesure 2026-09-04 : `bg_logs/`,
# `lake_7012.log.relaunch`, et un `node_modules/` non-ignore declenchent
# tous l'echec git). Ces tokens servent uniquement a NOYER le bruit de
# cache parmi les gitignores recenses (`!!`) : un gitignore qui matche un
# token n'est pas signale en `ignored_extra`.
# Tokens a matcher dans le chemin. Le matching est "contient" apres
# normalisation des separateurs Windows -> /. Cela permet de capturer
# `scripts/results/foo.json` (debut relatif) aussi bien que
# `foo/scripts/results/x.json` (interne). Pour eviter les faux positifs
# sur des fichiers source qui contiennent `scripts/results` dans leur nom
# (improbable mais prudent), chaque token est precede ou suivi d'un /
# virtuel par la logique de matching.
UNTRACKED_ARTIFACT_TOKENS = (
    "slides/images",
    "slides/pptx-reference",
    "scripts/results",
    ".claude/agent-memory",
    "_output.ipynb",
    "node_modules",
    ".cache",
    ".pytest_cache",
    "__pycache__",
    "_measurements",
    ".mypy_cache",
    ".ruff_cache",
    "/dist/",
    "/build/",
    ".eggs",
    ".tox",
    # #14619 : residus BG-prover constates sur les machines (un fichier de
    # log chacun bloquait le retrait de worktrees mergees).
    "bg_logs",
    ".log.relaunch",
    # #3895 : marqueur de propriete pose par le spawn (une ligne : nom de
    # lane). Tolere pour ne pas transformer l'attribution en blocage -- un
    # worktree refuse pour son propre marqueur ne serait jamais retire.
    ".lane-owner",
)

# Extensions/editions source : si du contenu untracked touche un fichier
# de ce type, c'est une edition de source non poussee, REFUSE obligatoire.
SOURCE_EXTENSIONS = (
    ".py", ".ipynb", ".md", ".cs", ".yml", ".yaml", ".json", ".toml",
    ".ini", ".cfg", ".sh", ".ps1", ".bat", ".txt", ".html", ".css", ".js",
    ".ts", ".tsx", ".jsx", ".lean", ".pyi",
)


@dataclasses.dataclass
class WorktreeStatus:
    """Résultat du diagnostic d'un worktree."""

    path: str
    branch: Optional[str]
    is_current: bool
    pr_state: Optional[str]      # "OPEN" / "MERGED" / "CLOSED" / None
    pr_number: Optional[int]
    pr_url: Optional[str]
    ahead_count: int             # commits non poussés
    has_source_dirty: bool       # untracked bloquant OU tracked modifie
    untracked_paths: list        # chemins untracked (info seulement)
    decision: str                # "REMOVE" / "REFUSE" / "SKIP_CURRENT"
    refusal_reason: Optional[str]
    # Champs #14509 (additifs, compat JSON amont) :
    has_submodules: bool = False          # submodule initialise present
    blocking_untracked: list = dataclasses.field(default_factory=list)
    ignored_extra: list = dataclasses.field(default_factory=list)
    # Champ #14195 (additif) : checkout disparu, enregistrement orphelin.
    # Porte la decision REMOVE *et* le passage a `--force` a l'apply.
    dead_registration: bool = False
    # Champ #17771 (additif) : REMOVE motive par contenu deja integre a
    # main (tete ancetre de origin/main), sans PR rattachable.
    content_on_main: bool = False
    # Champ #3895 (additif) : lane proprietaire lue dans le marqueur
    # `.lane-owner` a la racine du worktree (None si absent). Attribue les
    # refus pour le rapport -- jamais une autorite de decision.
    lane_owner: Optional[str] = None

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)


def run_git(cwd: str, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    """Lance une commande git avec capture stricte. cwd doit être un worktree."""
    return subprocess.run(
        ["git", "-C", cwd, *args],
        capture_output=True,
        text=True,
        check=check,
        encoding="utf-8",
        errors="replace",
    )


def current_repo_root() -> str:
    """Racine du repo CoursIA resolue depuis ce script.

    Les 3 appels `run_git(...)` (worktree list, cle de cache par remote
    origin, worktree remove) doivent operer sur le repo hebergeant ce
    script, independamment du cwd du processus appelant. Avant, ils
    passaient `"."` et resolvaient contre le cwd reel -- casse depuis une
    tache planifiee (#14473) ou tout autre cwd non-repo (#17904).

    La racine est le plus proche ancetre de `__file__` qui contient
    `.gitmodules` ou `.git/`. Cachee au premier appel (memoization
    legere, pas de cache disque).
    """
    cache_attr = "_coursia_root_cache"
    cached = getattr(current_repo_root, cache_attr, None)
    if cached is not None:
        return cached
    p = Path(__file__).resolve().parent
    while p != p.parent:
        if (p / ".gitmodules").is_file() or (p / ".git").exists():
            setattr(current_repo_root, cache_attr, str(p))
            return str(p)
        p = p.parent
    setattr(current_repo_root, cache_attr, os.getcwd())
    return os.getcwd()


def run_gh(*args: str, check: bool = True) -> subprocess.CompletedProcess:
    """Lance une commande gh avec capture stricte. cwd = CWD courant."""
    return subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        check=check,
        encoding="utf-8",
        errors="replace",
    )


def is_untracked_artifact(path: str) -> bool:
    """True si le chemin untracke correspond a un artefact tolere."""
    p = path.replace("\\", "/")
    # Encadre le chemin de / virtuels pour matcher correctement les tokens
    # qui peuvent apparaitre en debut (relatif) ou en milieu (interne).
    wrapped = f"/{p}"
    for token in UNTRACKED_ARTIFACT_TOKENS:
        if token in wrapped:
            return True
    return False


def parse_porcelain(stdout: str) -> dict:
    """Parse `git status --porcelain --ignored=matching` (#14509).

    Separe les untracked (`??`), les gitignores (`!!`) et les tracks
    modifies (tout autre XY non vide). TOUT untracked non-ignore est
    bloquant : `git worktree remove` (sans --force) refuse n'importe quel
    untracked non-ignore, quelle que soit son extension -- la politique
    git ignore nos categories d'artefact (mesure 2026-09-04 : `bg_logs/`,
    `lake_7012.log.relaunch`, et meme un `node_modules/` non-ignore
    declenchent l'echec chez git alors que l'ancien predicat decidait
    REMOVE). Les artefacts allowlistes (UNTRACKED_ARTIFACT_TOKENS) ne
    survivent donc QUE sous leur forme gitignoree (ils sortent en `!!`,
    jamais bloquants). Les gitignores qui matchent un token d'artefact de
    cache (node_modules, .cache, ...) sont NOYES dans le bruit de cache et
    non signales ; les autres (`.env` laisse, outputs de build) sont
    exposes en `ignored_extra` pour que la decision de retrait soit prise
    en les voyant -- ils n'empechent PAS le retrait (git les ignore
    aussi), l'information seul.
    """
    untracked: list[str] = []
    blocking: list[str] = []
    ignored_extra: list[str] = []
    tracked_modified: list[str] = []
    tracked_deleted: list[str] = []
    for line in stdout.splitlines():
        # Format porcelain : XY path (XY = 2 chars index/worktree)
        if len(line) < 4:
            continue
        xy = line[:2]
        path = line[3:].strip()
        # Renames : "R  old -> new" -> on prend la cible
        if " -> " in path:
            path = path.split(" -> ", 1)[1]
        if "??" in xy:
            # Tout untracked non-ignore bloque git worktree remove.
            untracked.append(path)
            blocking.append(path)
        elif "!!" in xy:
            # Gitignore : jamais bloquant ; signale seulement si
            # non-artefact de cache connu.
            if not is_untracked_artifact(path):
                ignored_extra.append(path)
        elif any(c != " " for c in xy):
            # Modification tracked non commitee = source sale
            tracked_modified.append(path)
            # Suppression cote arbre de travail (colonne worktree = 'D').
            # Comptee a part : un arbre ENTIEREMENT supprime n'est pas du
            # travail en cours, c'est un checkout disparu (cf #14195,
            # predicat `dead_registration`).
            if len(xy) > 1 and xy[1] == "D":
                tracked_deleted.append(path)
    return {
        "untracked": untracked,
        "blocking_untracked": blocking,
        "ignored_extra": ignored_extra,
        "tracked_modified": tracked_modified,
        "tracked_deleted": tracked_deleted,
    }


def worktree_has_initialized_submodules(wt_path: str) -> bool:
    """True si le worktree contient un submodule initialise (#14509).

    `git worktree remove` refuse structurellement les worktrees a
    submodules initialises ("working trees containing submodules cannot be
    moved or removed"). Detecte via `git submodule status` : une entree
    non vide qui ne commence pas par '-' denote un submodule dont le .git
    embarque existe (initialise, eventuellement a un sha different de
    l'index, marque '+').
    """
    proc = run_git(wt_path, "submodule", "status", check=False)
    if proc.returncode != 0:
        # Worktree illisible : pas de preuve de submodule initialise, on
        # ne REFUSE pas sur un etat qu'on ne peut pas lire ; le pire cas
        # est un FAILED git, etat d'avant-fix non regresse.
        return False
    return any(
        line.strip() and not line.startswith("-")
        for line in proc.stdout.splitlines()
    )


def is_source_dirty(path: str) -> bool:
    """True si le chemin untracked est une edition source non toleree."""
    p = path.replace("\\", "/")
    if is_untracked_artifact(p):
        return False
    return any(p.endswith(ext) for ext in SOURCE_EXTENSIONS)


def read_lane_owner(wt_path: str) -> Optional[str]:
    """Nom de lane pose par le spawn (#3895), ou None.

    Convention : fichier `.lane-owner` a la racine du worktree, premiere
    ligne non vide = nom de la lane proprietaire (ex. ``machine:workspace``).
    Le spawn qui le pose accepte que l'organe le lise ET le nettoie au
    retrait (token tolere). Absent, vide ou illisible : None, sans erreur --
    l'attribution est une economie de lecture, jamais une autorite : elle ne
    change AUCUNE decision, seulement le rapport.
    """
    try:
        text = (Path(wt_path) / ".lane-owner").read_text(
            encoding="utf-8", errors="replace")
    except OSError:
        return None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped[:64]
    return None


def same_worktree_path(a: str, b: str) -> bool:
    """Deux chemins de worktree designent-ils le meme repertoire ?

    Les deux cotes de la comparaison `is_current` viennent de sources qui
    n'ecrivent PAS les chemins de la meme facon :

    - `git worktree list --porcelain` rend toujours des slash avant
      (`D:/CoursIA/.worktrees/x`), y compris sur Windows ;
    - `Path(cwd).resolve()` rend la forme native, donc a antislash sur
      Windows (`D:` + separateur natif + `CoursIA` + ...).

    Une egalite de chaines entre ces deux formes est donc **toujours fausse
    sur Windows** : `SKIP_CURRENT` etait inatteignable. Mesure du 2026-09-03
    sur ai-01 (64 worktrees) : `skipped=0` meme en lancant le script depuis
    `.worktrees/ai01-gate-current`, dont la PR #14459 est MERGED -- ce
    worktree etait donc programme `WOULD REMOVE`, c'est-a-dire que `--apply`
    aurait tente `git worktree remove` sur le repertoire courant du process.

    Ce garde n'est pas fail-closed : il ne refuse pas trop, il ne refuse
    jamais. La comparaison se fait donc sur les chemins **resolus**, et
    `Path.__eq__` est insensible a la casse sous Windows (ce qui couvre au
    passage `d:/` vs `D:/`).
    """
    try:
        return Path(a).resolve() == Path(b).resolve()
    except OSError:
        # Chemin inaccessible (lecteur demonte, worktree efface a la main) :
        # on retombe sur une normalisation textuelle plutot que de rendre
        # False, qui reintroduirait exactement le defaut ci-dessus.
        return (a.replace("\\", "/").rstrip("/").lower()
                == b.replace("\\", "/").rstrip("/").lower())


def has_initialized_submodule(submodule_status_stdout: str) -> bool:
    """True si au moins un sous-module est INITIALISÉ dans ce worktree.

    `git submodule status` liste tous les sous-modules CONFIGURÉS du repo,
    y compris non-initialisés (préfixe '-') — et ce dans chaque worktree.
    Seuls les initialisés (matérialisés : un .git vit dans le chemin) font
    refuser `git worktree remove`. Mesuré firsthand 2026-09-04 (#14619) :
    ce repo porte des submodules configurés (MetaGeneticSharp…), tous en
    '-' dans les worktrees de feature — git les retire sans protester ;
    matcher sur la sortie brute aurait REFUSE les 55 worktrees d'un coup.
    Préfixes : '-' = non initialisé ; '' = initialisé au sha enregistré ;
    '+' = initialisé à un autre sha ; 'U' = conflit. Tout sauf '-' compte.
    """
    return any(
        line.strip() and not line.strip().startswith("-")
        for line in submodule_status_stdout.splitlines()
    )


# Fraction de l'index qui doit avoir disparu du disque pour qu'un
# enregistrement soit declare mort. 0.9 laisse deliberement de la marge :
# les cadavres mesures rendent 100 % (7355 a 8409 suppressions pour autant
# de fichiers tracks), et aucune suppression volontaire plausible n'atteint
# ce seuil SANS s'accompagner d'au moins une edition (condition (a)).
DEAD_TREE_RATIO = 0.9


def _is_dead_registration(wt_path: str, parsed: dict) -> bool:
    """Le checkout a-t-il disparu, laissant l'enregistrement orphelin ?

    Fail-CLOSED : au moindre doute (index illisible, index vide, une seule
    edition non-suppression), rend False -- le worktree repart alors dans
    les predicats de refus habituels.
    """
    deleted = parsed.get("tracked_deleted") or []
    modified = parsed.get("tracked_modified") or []
    if not deleted or len(deleted) != len(modified):
        # (a) une edition reelle coexiste avec les suppressions : c'est du
        # travail, pas un checkout disparu.
        return False
    ls_proc = run_git(wt_path, "ls-files", check=False)
    if ls_proc.returncode != 0:
        return False
    tracked_total = len([x for x in ls_proc.stdout.splitlines() if x.strip()])
    if tracked_total <= 0:
        return False
    return (len(deleted) / tracked_total) >= DEAD_TREE_RATIO


def get_worktree_info(wt_path: str, current_path: str) -> dict:
    """Recupere branch + ahead count + dirty status d'un worktree."""
    # Branche (peut etre None si HEAD detaché)
    branch_proc = run_git(wt_path, "rev-parse", "--abbrev-ref", "HEAD", check=False)
    branch_raw = branch_proc.stdout.strip()
    branch = None if branch_raw in ("HEAD", "") else branch_raw

    # Ahead count : commits non pousses vs @{u}. Si @{u} n'est pas
    # configure (branche feature sans `set-upstream-to`, frequente avec
    # `git worktree add -b`), @{u} retombe sur origin/main ce qui compare
    # la branche feature a main -- un faux positif massif. On verifie
    # d'abord la resolution explicite : si l'upstream specifique est la
    # branche elle-meme, on compte les commits en avance. Sinon (upstream
    # = main), on considere 0 unpushed et on laisse le verdict PR trancher.
    ahead_count = 0
    if branch:
        upstream_proc = run_git(
            wt_path, "rev-parse", "--abbrev-ref",
            f"{branch}@{{u}}", check=False,
        )
        if upstream_proc.returncode == 0:
            upstream = upstream_proc.stdout.strip()
            if upstream and not upstream.endswith("/main"):
                ahead_proc = run_git(
                    wt_path, "rev-list", "--count", "@{u}..HEAD", check=False
                )
                if ahead_proc.returncode == 0:
                    try:
                        ahead_count = int(ahead_proc.stdout.strip())
                    except ValueError:
                        ahead_count = 0

    # Untracked / gitignores / tracked-modifies : une seule passe, avec
    # --ignored=matching pour signaler les gitignores non-cache (#14509).
    status_proc = run_git(
        wt_path, "status", "--porcelain", "--ignored=matching", check=False
    )
    parsed = parse_porcelain(status_proc.stdout)
    # has_source suit la semantique #14619 : seuls les fichiers SOURCE non
    # toleres et les tracked modifies rendent le worktree sale -- les
    # artefacts toleres sont nettoyables a l'apply, ils ne comptent pas.
    has_source = bool(parsed["tracked_modified"]) or any(
        is_source_dirty(p) for p in parsed["blocking_untracked"]
    )
    # Registre actionnable : les untracked non-ignores NON toleres (ce que
    # le nettoyage n'emportera pas). Les toleres restent visibles dans
    # `untracked` pour la decision humaine.
    blocking_untracked = [
        p for p in parsed["blocking_untracked"] if not is_untracked_artifact(p)
    ]

    # Sous-modules : `git worktree remove` les refuse categoriquement
    # ("working trees containing submodules cannot be moved or removed"),
    # meme avec --force sur certains etats. #14619 : l'organe ne doit pas
    # annoncer REMOVE ce que git interdit par construction. Seuls les
    # sous-modules INITIALISÉS comptent (cf has_initialized_submodule).
    subm_proc = run_git(wt_path, "submodule", "status", check=False)
    has_submodules = has_initialized_submodule(subm_proc.stdout)

    # Enregistrement mort (#14195) : le checkout a disparu du disque alors
    # que `.git/worktrees/<nom>` subsiste. Cas mesure le 2026-09-05 : 26
    # des 51 worktrees enregistres, TOUS sous `C:\...\Temp`, vides par le
    # nettoyage disque de Windows. Git les voit comme des milliers de
    # fichiers tracks supprimes -- donc `tracked_modified` non vide, donc
    # `uncommitted_source_changes`, donc REFUSE a perpetuite : la preuve de
    # leur mort est exactement ce qui les rendait irreclamables.
    #
    # Le predicat exige les DEUX conditions, pour ne jamais confondre un
    # checkout disparu avec une lane qui supprime volontairement des
    # fichiers : (a) toute modification tracked est une suppression -- une
    # seule edition reelle disqualifie ; (b) la quasi-totalite de l'index
    # a disparu du disque (>= DEAD_TREE_RATIO). Une PR qui supprime 200
    # fichiers sur 9000 echoue (b) ; une PR qui en supprime 8900 et en
    # edite un echoue (a).
    dead_registration = _is_dead_registration(wt_path, parsed)

    # Attribution lane (#3895) : lue dans le marqueur `.lane-owner`, une
    # lecture de fichier par worktree, sans effet sur les decisions.
    lane_owner = read_lane_owner(wt_path)

    return {
        "branch": branch,
        "ahead_count": ahead_count,
        "untracked": parsed["untracked"],
        "blocking_untracked": blocking_untracked,
        "tracked_modified": parsed["tracked_modified"],
        "ignored_extra": parsed["ignored_extra"],
        "has_source_dirty": has_source,
        "has_submodules": has_submodules,
        "is_current": same_worktree_path(wt_path, current_path),
        "dead_registration": dead_registration,
        "lane_owner": lane_owner,
    }


# ----------------------------------------------------------------------------
# Resolution PR a trois etages (#15369)
# ----------------------------------------------------------------------------
# Mesure fondatrice (rapport fleet po-2023 du 09/09 04:27) : 4 fermes en
# « gh pr list failed » -- quota GraphQL du compte partage epuise, toutes
# les machines tirant en meme temps. La resolution d'ancre coutait UN
# appel search par worktree, sans aucun cache : lineaire en nombre de
# worktrees (265 sur po-2026, 103 sur ai-01), sur un budget horaire
# COMMUN a la flotte. Trois etages, du moins couteux au plus couteux :
#
# 1. cache disque par branche : verdicts MERGED uniquement, gardes par
#    headRefOid (un MERGED est definitif POUR CES commits ; une branche
#    re-poussee/re-PR porte un oid different -> miss -> etage suivant ;
#    CLOSED n'est jamais cache, reopen possible) ;
# 2. lot unique `--limit N` indexe par headRefName : une requete par
#    passe au lieu de N. La fenetre est cappee : une ABSENCE du lot
#    n'est jamais un verdict -- les branches absentes retombent sur
#    l'ancre. Une ERREUR gh au lot degrade aussi vers l'ancre : une
#    optimisation ne doit pas refuser des retraits legitimes ;
# 3. l'ancre historique `--state all --search "head:<branche>"` :
#    AUTHORITATIVE par decision ecrite (.claude/rules/git-workflow.md) --
#    inchangee. La remplacer par commits/<oid>/pulls (faux negatifs
#    mesures sur PRs OPEN) serait une regression, pas une optimisation.

PR_VERDICT_CACHE_VERSION = 1
PR_LISTING_WINDOW = 1000


def _pr_cache_path() -> Path:
    """Un fichier de verdicts par depot (cle = sha1 du remote origin)."""
    proc = run_git(current_repo_root(), "remote", "get-url", "origin", check=False)
    url = proc.stdout.strip() if proc.returncode == 0 else "unknown-repo"
    key = hashlib.sha1(url.encode("utf-8")).hexdigest()[:12]
    return Path.home() / ".cache" / "coursia" / "prune_pr_verdicts" / f"{key}.json"


class PrResolution:
    """Resolution PR a trois etages : cache disque -> lot -> ancre."""

    def __init__(self, cache_path: Optional[Path] = None,
                 listing_window: int = PR_LISTING_WINDOW):
        self.cache_path = cache_path
        self.listing_window = listing_window
        self._entries: dict = {}
        self._cache_dirty = False
        self._index: Optional[dict] = None
        self.stats = {
            "cache_hits": 0,
            "listing_calls": 0,
            "listing_hits": 0,
            "listing_degraded": 0,
            "anchor_calls": 0,
            "cache_writes": 0,
        }
        if self.cache_path is not None:
            self._load_cache()

    def _load_cache(self) -> None:
        """Le cache est une economie, jamais une autorite : illisible = vide."""
        try:
            data = json.loads(self.cache_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return
        if data.get("version") == PR_VERDICT_CACHE_VERSION:
            self._entries = data.get("entries", {})

    def flush(self) -> None:
        if not self._cache_dirty or self.cache_path is None:
            return
        payload = {
            "version": PR_VERDICT_CACHE_VERSION,
            "entries": self._entries,
        }
        tmp = self.cache_path.with_suffix(".tmp")
        try:
            self.cache_path.parent.mkdir(parents=True, exist_ok=True)
            tmp.write_text(json.dumps(payload), encoding="utf-8")
            os.replace(tmp, self.cache_path)
        except OSError:
            return
        self._cache_dirty = False

    def _cache_get(self, branch: str, head_sha: Optional[str]) -> Optional[dict]:
        entry = self._entries.get(branch)
        if not entry or entry.get("state") != "MERGED":
            return None
        # Garde oid : le verdict MERGED vaut pour ces commits exactement.
        if not head_sha or entry.get("headRefOid") != head_sha:
            return None
        return {
            "number": entry["number"],
            "state": "MERGED",
            "url": entry.get("url"),
            "headRefName": branch,
            "headRefOid": entry.get("headRefOid"),
        }

    def _cache_put(self, row: dict) -> None:
        if row.get("state") != "MERGED" or not row.get("headRefOid"):
            return
        self._entries[row["headRefName"]] = {
            "number": row["number"],
            "state": "MERGED",
            "url": row.get("url"),
            "headRefOid": row["headRefOid"],
        }
        self._cache_dirty = True
        self.stats["cache_writes"] += 1

    def _build_index(self) -> dict:
        if self._index is not None:
            return self._index
        self.stats["listing_calls"] += 1
        proc = run_gh(
            "pr", "list",
            "--state", "all",
            "--json", "number,state,url,headRefName,headRefOid",
            "--limit", str(self.listing_window),
            check=False,
        )
        rows = None
        if proc.returncode == 0:
            try:
                rows = json.loads(proc.stdout)
            except json.JSONDecodeError:
                rows = None
        if rows is None:
            # Echec du lot -> degradation vers l'ancre (comportement
            # d'avant #15369). L'index reste construit-vide : la
            # degradation ne se joue qu'une fois par passe.
            self._index = {}
            self.stats["listing_degraded"] += 1
            return self._index
        index: dict = {}
        for row in rows:
            name = row.get("headRefName")
            if not name:
                continue
            # Plusieurs PRs par nom de branche (close+reopen, re-PR) :
            # garder la plus recente = numero max, meme choix que le
            # rows[0] de l'ancre (retournee par date desc).
            if (name not in index
                    or row.get("number", 0) > index[name].get("number", 0)):
                index[name] = row
        self._index = index
        return index

    def resolve(self, branch: str,
                head_sha: Optional[str] = None) -> Optional[dict]:
        cached = self._cache_get(branch, head_sha)
        if cached is not None:
            self.stats["cache_hits"] += 1
            return cached
        index = self._build_index()
        if branch in index:
            row = index[branch]
            self._cache_put(row)
            self.stats["listing_hits"] += 1
            return row
        row = anchor_search_pr_for_branch(branch)
        self.stats["anchor_calls"] += 1
        if row:
            self._cache_put(row)
        return row


_RESOLUTION: Optional[PrResolution] = None


def get_pr_resolution() -> PrResolution:
    """Singleton de passe : une seule requete de lot, un seul flush."""
    global _RESOLUTION
    if _RESOLUTION is None:
        _RESOLUTION = PrResolution(cache_path=_pr_cache_path())
    return _RESOLUTION


def reset_pr_resolution() -> None:
    """Tests : detache le singleton (chaque passe doit reconstruire)."""
    global _RESOLUTION
    _RESOLUTION = None


def anchor_search_pr_for_branch(branch: str) -> Optional[dict]:
    """Cherche la PR dont le headRefName = branch.

    Ancre autoritative : `gh pr list --state all --search "head:<branch>"`.
    Pas de REST `commits/<oid>/pulls` (faux negatifs mesures, cf
    orphan-branch-scan dans .claude/rules/git-workflow.md).
    """
    proc = run_gh(
        "pr", "list",
        "--state", "all",
        "--search", f"head:{branch}",
        "--json", "number,state,url,headRefName,headRefOid",
        "--limit", "5",
        check=False,
    )
    if proc.returncode != 0:
        # gh erreur : on ne sait pas decider, REFUSE sec
        raise RuntimeError(f"gh pr list failed: {proc.stderr.strip()}")
    try:
        rows = json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"gh pr list returned non-JSON: {e}") from e
    if not rows:
        return None
    # Si plusieurs PRs ont partage le meme nom de branche (improbable mais
    # possible apres close+reopen), on prend la plus recente en premier
    # (gh retourne deja par date desc).
    return rows[0]


def lookup_pr_for_branch(branch: str,
                         head_sha: Optional[str] = None) -> Optional[dict]:
    """Resolution PR d'une branche via la couche a trois etages (#15369).

    L'ancre `--state all --search head:<branche>` reste la source
    autoritative ; les etages cache disque et lot unique ne font que
    l'EVITER quand le verdict est deja etabli (MERGED garde par oid) ou
    disponible dans la fenetre du lot. Une absence ou un echec des etages
    d'economie retombe TOUJOURS sur l'ancre.
    """
    return get_pr_resolution().resolve(branch, head_sha)


# Reference de l'integration : un HEAD detache qui en est ancetre n'a
# aucun commit propre, donc aucune PR attribuable (#17684).
MAIN_REF = "origin/main"


def head_is_ancestor_of_main(wt_path: str) -> bool:
    """Vrai si HEAD (attache ou detache) est un ancetre de ``origin/main``.

    Echec git (ref absente, depot sans remote) -> False : la voie de lookup,
    restreinte a ``origin/main..HEAD``, rend alors None, donc REFUSE.
    """
    proc = run_git(
        wt_path, "merge-base", "--is-ancestor", "HEAD", MAIN_REF, check=False
    )
    return proc.returncode == 0


def detached_head_is_on_main(wt_path: str) -> bool:
    """Vrai si le HEAD detache est un ancetre de ``origin/main`` (#17684).

    Un tel worktree ne porte aucun commit propre : c'est une extraction de
    main (demeure d'un organe planifie, lecture de review), pas le travail
    d'une PR. Les sujets ``(#N)`` de son historique sont ceux de main, et
    les resoudre attribue au worktree la PR d'un commit ancetre -- mesure :
    la demeure de la tache ``merge_ready`` classee REMOVE sur une PR MERGED
    qui n'avait rien a voir avec elle.
    """
    return head_is_ancestor_of_main(wt_path)


def remote_head_for_head(wt_path: str, branch: str,
                         head_sha: str) -> Optional[str]:
    """Nom court de la branche distante qui porte exactement HEAD (#17771).

    Cas mesure : un worktree branche localement sous un nom different de la
    tete de PR (checkout `pr-123`, renommage local). La resolution par le
    nom local echoue alors que la PR existe. Deux voies, de la plus precise
    a la plus large :

    1. l'upstream explicite ``<branche>@{u}`` (hors ``*/main``) : le lien
       de push est la preuve la plus directe que la branche distante porte
       la meme histoire ;
    2. une branche ``origin/*`` dont le TIP est exactement ``head_sha``
       (scan ``for-each-ref``, ``origin/main`` et ``origin/HEAD`` exclus) :
       apres un checkout detache re-branche, seul le contenu parle encore.

    Retourne None si aucune voie ne resolve : l'appelant retombe sur la
    REFUSE conservatrice (ou le predicat content_on_main).
    """
    upstream_proc = run_git(
        wt_path, "rev-parse", "--abbrev-ref", "--symbolic-full-name",
        f"{branch}@{{u}}", check=False,
    )
    if upstream_proc.returncode == 0:
        upstream = upstream_proc.stdout.strip()
        if upstream and not upstream.endswith("/main"):
            return upstream.split("/", 1)[1] if "/" in upstream else upstream
    refs_proc = run_git(
        wt_path, "for-each-ref", "refs/remotes/origin",
        "--format=%(refname:short) %(objectname)", check=False,
    )
    if refs_proc.returncode != 0:
        return None
    for line in refs_proc.stdout.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        name, tip = parts
        if name in ("origin/main", "origin/HEAD"):
            continue
        if tip == head_sha:
            return name.split("/", 1)[1] if "/" in name else name
    return None


def lookup_pr_for_detached_head(wt_path: str) -> Optional[dict]:
    """Verdict par contenu pour HEAD detaché (#14476) : PR exacte, ou rien.

    Le squash-merge efface l'ascendance, donc `git merge-base --is-ancestor`
    ne marche pas. On cherche un match EXACT entre les sujets de commit du
    HEAD et une PR reelle, en deux voies :

    1. **Resolution directe par numero** : un squash-commit sur ce depot a
       pour sujet ``<titre de la PR> (#N)``. On extrait N via
       ``re.search(r"\\(#(\\d+)\\)\\s*$", subj)`` et on resout la PR par
       ``gh pr view N --json ...`` -- pas de liste, pas d'ambiguite.
       C'est la voie nominale (squash-merge preserve le numero de PR
       dans le sujet du commit, et c'est le seul invariant mesurable).

    2. **Egalite normalisee du sujet** : a defaut de numero extractible,
       le sujet integral (apres normalisation casse + espaces) doit etre
       egal a un titre PR normalise. Toute intersection par jetons est
       un faux positif structurel sur ce depot (notebook, guard,
       training, slides sont des mots partout) et on l'interdit.

    3. **Sinon None** : aucun match = aucun verdict. Le fail-CLOSED est
       deja le bon defaut (REFUSE downstream).

    Les sujets lus sont ceux des commits PROPRES au HEAD
    (``origin/main..HEAD``), jamais son historique entier : les 20 derniers
    sujets de ``HEAD`` traversent main des le premier commit partage, et la
    voie 1 resolvait alors la PR d'un commit ancetre (#17684 -- une branche
    de revert attribuee a la PR qu'elle revertait, MERGED, donc REMOVE,
    alors que sa propre PR etait OPEN).
    """
    log_proc = run_git(
        wt_path, "log", f"{MAIN_REF}..HEAD", "--format=%s", "-n", "20",
        check=False,
    )
    if log_proc.returncode != 0:
        return None
    subjects = [s.strip() for s in log_proc.stdout.splitlines() if s.strip()]
    if not subjects:
        return None

    # Voie 1 : resolution directe par numero extractible du sujet
    # (squash-commit preserve "(#N)" a la fin du sujet).
    pr_num_re = re.compile(r"\(#(\d+)\)\s*$")
    direct_attempted = False
    for subj in subjects:
        m = pr_num_re.search(subj)
        if not m:
            continue
        direct_attempted = True
        pr_num = int(m.group(1))
        view_proc = run_gh(
            "pr", "view", str(pr_num),
            "--json", "number,state,url,title",
            check=False,
        )
        if view_proc.returncode != 0:
            continue
        try:
            data = json.loads(view_proc.stdout)
        except json.JSONDecodeError:
            continue
        if not data or "state" not in data:
            continue
        return data
    # Si des sujets portaient (#N) mais qu'aucun n'a resolu, c'est un
    # defaut d'autorite gh -- on n'invente rien, pas de fallback liste.
    if direct_attempted:
        return None

    # Voie 2 : egalite normalisee du sujet contre titres PR recents.
    # Garde-fou : `limit 50` uniquement pour borner le cout d'appel.
    list_proc = run_gh(
        "pr", "list", "--state", "all", "--limit", "50",
        "--json", "number,state,url,title",
        check=False,
    )
    if list_proc.returncode != 0:
        return None
    try:
        prs = json.loads(list_proc.stdout)
    except json.JSONDecodeError:
        return None

    def _normalize(s: str) -> str:
        # strip + lower + collapse whitespace ; retire ponctuation terminale
        s = s.strip().lower()
        s = re.sub(r"\s+", " ", s)
        return s.rstrip(".!?")

    subj_norm_set = {_normalize(s) for s in subjects}
    for pr in prs:
        if _normalize(pr["title"]) in subj_norm_set:
            return pr
    return None


def diagnose_worktree(wt_path: str, current_path: str,
                      head_sha: Optional[str] = None) -> WorktreeStatus:
    """Diagnostic complet d'un worktree.

    `head_sha` (fourni par `list_worktrees`, porcelain) sert uniquement a
    la garde oid du cache de verdicts MERGED (#15369) : sans lui, l'etage
    cache est saute, jamais consulte a l'aveugle.
    """
    info = get_worktree_info(wt_path, current_path)

    # Worktree courant : on ne tente JAMAIS de le retirer
    if info["is_current"]:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=True,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="SKIP_CURRENT",
            refusal_reason="current_worktree_not_removable",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Branche main : JAMAIS retirer (le worktree de travail principal).
    # Une PR fermee qui pointe sur `main` ne doit pas faire conclure au
    # retrait : main est la branche de travail vivante, pas une feature
    # terminee.
    if info["branch"] in ("main", "master"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="protected_branch:main",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Sous-modules : git interdit le retrait par construction -> REFUSE sans
    # meme annoncer REMOVE (#14619 point 4).
    if info.get("has_submodules"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="contains_submodules",
            lane_owner=info.get("lane_owner"),
        )

    # Predicat 1 : commits non poussés -> REFUSE inconditionnel
    if info["branch"] and info["ahead_count"] > 0:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason=f"unpushed_commits:{info['ahead_count']}",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Predicat 1bis : enregistrement mort (#14195). DOIT preceder les
    # predicats de salete : un checkout disparu se presente comme des
    # milliers de fichiers tracks supprimes, donc `has_source_dirty`, donc
    # REFUSE -- c'est ce masquage qui laissait 26 enregistrements morts au
    # registre. L'etat PR n'est pas interroge : il n'y a plus d'arbre a
    # proteger, quel que soit le sort de la branche (que `git worktree
    # remove` ne supprime jamais).
    if info.get("dead_registration"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REMOVE",
            refusal_reason=None,
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
            dead_registration=True,
        )

    # Predicat 2a : source sale (fichier source untracked non tolere, ou
    # tracked modifie) -> REFUSE (#14509 : pouvoir de refus git reel ;
    # #14619 : les toleres sont nettoyables a l'apply et ne comptent plus).
    if info["has_source_dirty"]:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=True,
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="uncommitted_source_changes",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Predicat 2b : residu untracked NON tolere -> REFUSE (#14619 point 2).
    # `git worktree remove` sans --force refuse sur TOUT fichier non suivi,
    # tolere ou non : un worktree qui porte un residu hors liste toleree ne
    # pourra jamais etre retire, il ne doit donc pas etre compte removable.
    # Le nettoyage a l'apply (clean_tolerated_artifacts) ne touche que la
    # liste toleree -- ce REFUSE est le complement fail-closed du couple
    # classification/execution.
    untolerated = [
        p for p in info["untracked"] if not is_untracked_artifact(p)
    ]
    if untolerated:
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason=f"untolerated_untracked:{len(untolerated)}",
            lane_owner=info.get("lane_owner"),
        )

    # Resolution PR
    pr = None
    if info["branch"]:
        pr = lookup_pr_for_branch(info["branch"], head_sha=head_sha)
        if pr is None:
            # #17771 predicat 1 : la branche locale porte un nom different
            # de la tete de PR. On resout la PR par la branche distante qui
            # porte exactement HEAD (upstream explicite, puis tip exact
            # origin/*). Pas de PR de ce cote non plus -> on continue.
            remote_head = remote_head_for_head(wt_path, info["branch"], head_sha)
            if remote_head:
                pr = lookup_pr_for_branch(remote_head, head_sha=head_sha)
    elif detached_head_is_on_main(wt_path):
        # Extraction de main (demeure d'organe, lecture de review) : aucune
        # PR ne la porte, le critere « PR MERGED » ne s'y applique pas.
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason="detached_on_main",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )
    else:
        pr = lookup_pr_for_detached_head(wt_path)

    pr_state = pr.get("state") if pr else None
    pr_number = pr.get("number") if pr else None
    pr_url = pr.get("url") if pr else None

    # Predicat 3 : PR OPEN -> REFUSE
    if pr_state == "OPEN":
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=pr_state,
            pr_number=pr_number,
            pr_url=pr_url,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REFUSE",
            refusal_reason=f"pr_open:#{pr_number}",
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Predicat 4 : PR MERGED ou CLOSED -> REMOVE
    if pr_state in ("MERGED", "CLOSED"):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=pr_state,
            pr_number=pr_number,
            pr_url=pr_url,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REMOVE",
            refusal_reason=None,
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
        )

    # Predicat 5 (#17771) : contenu deja integre a main. Aucune PR
    # rattachable (ni par nom local, ni par tete distante), mais HEAD est
    # un ancetre de origin/main : chaque commit du worktree est deja sur
    # main. Les gardes en amont garantissent deja les deux autres
    # conditions de l'issue -- 0 commit non pousse (sinon
    # ``unpushed_commits`` serait sorti) et aucune edition source non
    # committee ni untracked non tolere (sinon ``uncommitted_source_changes``
    # / ``untolerated_untracked`` seraient sortis). Le worktree ne porte
    # plus rien que main ne contienne deja.
    if info["branch"] and head_is_ancestor_of_main(wt_path):
        return WorktreeStatus(
            path=wt_path,
            branch=info["branch"],
            is_current=False,
            pr_state=None,
            pr_number=None,
            pr_url=None,
            ahead_count=info["ahead_count"],
            has_source_dirty=info["has_source_dirty"],
            untracked_paths=info["untracked"],
            decision="REMOVE",
            refusal_reason=None,
            has_submodules=info["has_submodules"],
            blocking_untracked=info.get("blocking_untracked", []),
            ignored_extra=info.get("ignored_extra", []),
            lane_owner=info.get("lane_owner"),
            content_on_main=True,
        )

    # Pas de PR trouvee : HEAD detaché sans correspondance, ou branche
    # non pushée qu'on ne peut pas relier. REFUSE conservatrice.
    return WorktreeStatus(
        path=wt_path,
        branch=info["branch"],
        is_current=False,
        pr_state=None,
        pr_number=None,
        pr_url=None,
        ahead_count=info["ahead_count"],
        has_source_dirty=info["has_source_dirty"],
        untracked_paths=info["untracked"],
        decision="REFUSE",
        refusal_reason="no_pr_match" if info["branch"] else "detached_no_match",
        has_submodules=info["has_submodules"],
        blocking_untracked=info.get("blocking_untracked", []),
        ignored_extra=info.get("ignored_extra", []),
        lane_owner=info.get("lane_owner"),
    )


def list_worktrees() -> list[dict]:
    """Retourne les worktrees sous forme [{path, head_sha}, ...]."""
    proc = run_git(current_repo_root(), "worktree", "list", "--porcelain", check=False)
    if proc.returncode != 0:
        raise RuntimeError(f"git worktree list failed: {proc.stderr.strip()}")
    out: list[dict] = []
    cur: dict = {}
    for line in proc.stdout.splitlines():
        if line.startswith("worktree "):
            if cur:
                out.append(cur)
            cur = {"path": line[len("worktree "):].strip()}
        elif line.startswith("HEAD "):
            cur["head_sha"] = line[len("HEAD "):].strip()
        elif line.startswith("branch "):
            cur["branch"] = line[len("branch "):].strip()
    if cur:
        out.append(cur)
    return out


def clean_tolerated_artifacts(wt: WorktreeStatus) -> list[str]:
    """Supprime les SEULS artefacts tolérés du worktree, avant retrait.

    #14619 : la liste tolérée encode déjà le jugement « ces fichiers ne
    valent rien » (caches, logs BG, résultats). `git worktree remove` sans
    --force refuse sur TOUT fichier non suivi, toléré ou non : sans ce
    nettoyage, un worktree classé REMOVE pour artefacts seulement ne peut
    jamais être retiré (removable n'est alors pas une prévision de applied).

    Garde-fous :
    - seuls les chemins untracked qui matchent la liste tolérée sont visés ;
    - chaque cible doit résoudre DANS le worktree (défense en profondeur
      contre une entrée porcelain inattendue) ;
    - jamais de `--force` : le retrait reste `git worktree remove` nu. Si un
      résidu hors liste survient entre le diagnostic et l'apply, git refuse
      et le statut FAILED rend la cause (fail-closed).
    """
    removed: list[str] = []
    root = Path(wt.path)
    try:
        root_resolved = root.resolve()
    except OSError:
        return removed
    for rel in wt.untracked_paths:
        if not is_untracked_artifact(rel):
            continue
        target = root / rel.rstrip("/\\")
        try:
            if not target.resolve().is_relative_to(root_resolved):
                continue
        except OSError:
            continue
        if target.is_symlink():
            # rmtree sur un lien symbolique leve OSError ; unlink est le
            # geste correct et ne touche pas la cible.
            try:
                target.unlink()
                removed.append(rel)
            except OSError:
                continue
        elif target.is_dir():
            shutil.rmtree(target, ignore_errors=True)
            if not target.exists():
                removed.append(rel)
        elif target.exists():
            try:
                target.unlink()
                removed.append(rel)
            except OSError:
                continue
    return removed


def apply_removal(wt: WorktreeStatus) -> tuple[bool, str]:
    """Tente `git worktree remove`. Retourne (success, stderr).

    `--force` est reserve aux enregistrements morts (#14195) : sans lui,
    git refuse de retirer un worktree dont l'arbre a disparu ("contains
    modified or untracked files"), et l'organe annoncerait un REMOVE qu'il
    ne peut pas executer. Pour tout autre worktree, l'absence de `--force`
    reste le garde-fou : c'est git qui refuse en dernier ressort si la
    classification s'est trompee.
    """
    args = ["worktree", "remove"]
    if wt.dead_registration:
        args.append("--force")
    args.append(wt.path)
    proc = run_git(current_repo_root(), *args, check=False)
    if proc.returncode == 0:
        return True, ""
    return False, proc.stderr.strip()


def render_text(
    statuses: list[WorktreeStatus],
    dry_run: bool,
    apply_results: Optional[list[dict]] = None,
) -> str:
    """Rendu texte canonique (lisible humain) (#14476).

    `apply_results` est la liste exacte retournee par `apply_removal` :
    `[{path, branch, pr_number, applied, stderr}, ...]`. En mode `--apply`,
    on imprime `REMOVED` UNIQUEMENT pour les entrees dont `applied=True`.
    Si `git worktree remove` a echoue (worktree sale par exemple), on
    imprime `FAILED` avec le stderr -- c'est lisible, factuel, et JAMAIS
    mensonger sur ce qui a effectivement quitte le disque.
    """
    # Indexation par path pour une reconciliation O(1)
    applied_by_path = {}
    if apply_results is not None:
        for r in apply_results:
            applied_by_path[r["path"]] = r

    lines: list[str] = []
    counts = {"REMOVE": 0, "REFUSE": 0, "SKIP_CURRENT": 0, "FAILED": 0}
    for s in statuses:
        counts[s.decision] = counts.get(s.decision, 0) + 1
        branch_part = f"branch={s.branch}" if s.branch else "no_branch"
        # Gitignores non-cache signales (#14509) : informatifs, jamais
        # bloquants (git les ignore aussi lors du retrait).
        ignored_part = ""
        if s.ignored_extra:
            shown = ", ".join(s.ignored_extra[:3])
            if len(s.ignored_extra) > 3:
                shown += ", ..."
            ignored_part = f"  ignored={shown}"
        if s.decision == "REMOVE":
            pr_part = (
                f"pr=#{s.pr_number}({s.pr_state})"
                if s.pr_state and s.pr_number else ""
            )
            if not pr_part and s.content_on_main:
                pr_part = "content_on_main"
            if dry_run:
                lines.append(
                    f"WOULD REMOVE {s.path}  {branch_part}  {pr_part}"
                    f"{ignored_part}".rstrip()
                )
            else:
                # Mode --apply : vraie realite du disque.
                result = applied_by_path.get(s.path)
                if result is None or result.get("applied"):
                    lines.append(
                        f"REMOVED     {s.path}  {branch_part}  {pr_part}"
                        f"{ignored_part}".rstrip()
                    )
                else:
                    # `git worktree remove` a echoue : on dit FAILED + cause.
                    # Counts['FAILED'] n'est pas une decision de WorktreeStatus,
                    # c'est un evenement d'application ; ne s'ajoute pas a
                    # refused qui reste REFUSE semantique.
                    stderr = result.get("stderr") or "unknown error"
                    lines.append(
                        f"FAILED      {s.path}  {branch_part}  {pr_part}"
                        f"{ignored_part}  apply_error={stderr[:120]}"
                    )
                    counts["FAILED"] = counts.get("FAILED", 0) + 1
        elif s.decision == "REFUSE":
            # Attribution lane (#3895) quand le marqueur .lane-owner existe.
            lane_part = f"  lane={s.lane_owner}" if s.lane_owner else ""
            lines.append(
                f"REFUSE      {s.path}  {branch_part}  reason={s.refusal_reason}"
                f"{lane_part}{ignored_part}"
            )
        elif s.decision == "SKIP_CURRENT":
            lines.append(f"SKIP        {s.path}  reason=current_worktree")
    lines.append("---")
    lines.append(
        f"total={len(statuses)}  "
        f"removable={counts.get('REMOVE', 0)}  "
        f"refused={counts.get('REFUSE', 0)}  "
        f"failed={counts.get('FAILED', 0)}  "
        f"skipped={counts.get('SKIP_CURRENT', 0)}"
    )
    # Decompte par classe de refus (#3895) : la donnee qui rend un taux de
    # refus actionnable (quelle classe domine, par lane attribuee).
    refused_classes = refusal_reason_breakdown(statuses)
    if refused_classes:
        lines.append(
            "refusals: "
            + "  ".join(f"{cls}={n}" for cls, n in refused_classes.items())
        )
    return "\n".join(lines)


# ----------------------------------------------------------------------------
# Observabilite des refus (#3895, roo-extensions)
# ----------------------------------------------------------------------------

def refusal_reason_breakdown(statuses: list) -> dict:
    """Compte les refus par CLASSE de raison (avant le ':' de detail).

    `unpushed_commits:2` et `untolerated_untracked:3` portent un detail
    variable par worktree ; seule la classe s'aggregate. Tri : compte
    decroissant puis cle alphabetique -- rendu texte stable, JSON
    deterministe (un meme etat rend toujours la meme sortie).
    """
    counts: dict = {}
    for s in statuses:
        if s.decision != "REFUSE" or not s.refusal_reason:
            continue
        cls = s.refusal_reason.split(":", 1)[0]
        counts[cls] = counts.get(cls, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def lane_refusal_breakdown(statuses: list) -> dict:
    """Refus attribues par lane (marqueur .lane-owner, #3895), meme tri.

    Les refus sans marqueur tombent dans ``unattributed`` : distinguer
    « lane X refuse 40 worktrees » de « 40 worktrees non revendiques » est
    precisement la question posee par le post-mortem po-2023.
    """
    counts: dict = {}
    for s in statuses:
        if s.decision != "REFUSE" or not s.refusal_reason:
            continue
        key = s.lane_owner or "unattributed"
        counts[key] = counts.get(key, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def build_warn_line(statuses: list,
                    host: Optional[str] = None) -> Optional[str]:
    """Ligne [WARN] prete pour le dashboard workspace (#3895).

    La saturation par worktrees refuses est le signal qui a fait tomber
    po-2023 (27/09) : au-dela du seuil, la ligne agrege totals + classes
    dominantes + attribution lane (quand les marqueurs existent), prete a
    etre relevee telle quelle. Rend None si aucun refus (rien a signaler).

    Emise sur stderr par l'appelant : stdout reste le rapport (en --json il
    doit rester pur pour `json.loads`).
    """
    refused = sum(1 for s in statuses if s.decision == "REFUSE")
    if refused <= 0:
        return None
    host = host or os.environ.get("COMPUTERNAME") or "unknown-host"
    classes = refusal_reason_breakdown(statuses)
    top_classes = " ".join(f"{k}={v}" for k, v in list(classes.items())[:3])
    parts = [
        f"[WARN][prune-task] {host} refused={refused}/{len(statuses)}",
        f"top: {top_classes}",
    ]
    lanes = lane_refusal_breakdown(statuses)
    if lanes:
        top_lanes = " ".join(f"{k}={v}" for k, v in list(lanes.items())[:3])
        parts.append(f"lanes: {top_lanes}")
    return " — ".join(parts)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument(
        "--apply",
        action="store_true",
        help="Applique les retraits. Dry-run par defaut.",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON structuree (parallele au mode texte).",
    )
    p.add_argument(
        "--path",
        default=None,
        help="Cwd pour `git worktree list`. Default = CWD.",
    )
    p.add_argument(
        "--warn-threshold",
        type=int,
        default=None,
        metavar="N",
        help="Emet sur stderr une ligne [WARN][prune-task] prete a poster "
             "sur le dashboard workspace si refused > N (#3895). Desactive "
             "par defaut ; la tache planifiee passe 20.",
    )
    args = p.parse_args()

    cwd = args.path or "."

    # Resolution du chemin canonique de l'analyse (pour comparaison is_current).
    # Mesuree AVANT le chdir ci-dessous : un --path relatif se resout contre le
    # cwd d'appel, pas contre lui-meme.
    try:
        current_path = str(Path(cwd).resolve())
    except OSError:
        current_path = cwd

    # `--path` est le cwd de l'ANALYSE, pas un filtre -- contrat porte par
    # l'en-tete (`--path /c/dev/CoursIA-X`) et par le help ci-dessus. Les
    # trois appels `run_git(...)` (worktree list, cle de cache par remote
    # origin, worktree remove) resolvent le cwd en PREMIER argument, pas via
    # le cwd reel du processus : depuis un autre dossier -- le cas de la
    # tache planifiee (#14473), dont le cwd est System32 -- il fallait que
    # les 3 sites voient `current_path`, pas `"."`. Avant, le garde
    # `os.chdir(current_path)` faisait l'office ; il mutait l'etat du
    # process appelant et restait fragile sur les retrait refuses. On
    # passe maintenant `current_path` directement a run_git (#17904).
    if args.path:
        try:
            os.chdir(current_path)
        except OSError as e:
            print(f"ERROR: --path inutilisable ({args.path}): {e}", file=sys.stderr)
            return 2

    try:
        worktrees = list_worktrees()
    except RuntimeError as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 2

    statuses: list[WorktreeStatus] = []
    for wt in worktrees:
        try:
            statuses.append(
                diagnose_worktree(
                    wt["path"], current_path, head_sha=wt.get("head_sha")
                )
            )
        except RuntimeError as e:
            print(f"ERROR diagnosing {wt['path']}: {e}", file=sys.stderr)
            return 2

    # Les verdicts MERGED etablis pendant la passe survivent a la passe :
    # persistance du cache de verdicts (#15369).
    get_pr_resolution().flush()

    # Application
    apply_results: list[dict] = []
    refused_count = 0
    removal_count = 0
    error_count = 0
    if args.apply:
        for s in statuses:
            if s.decision != "REMOVE":
                if s.decision == "REFUSE":
                    refused_count += 1
                continue
            # #14619 : nettoyer exactement les artefacts tolérés AVANT le
            # retrait sans force, sinon git refuse sur tout untracked.
            cleaned = clean_tolerated_artifacts(s)
            ok, stderr = apply_removal(s)
            apply_results.append({
                "path": s.path,
                "branch": s.branch,
                "pr_number": s.pr_number,
                "applied": ok,
                "stderr": stderr,
                "cleaned_artifacts": cleaned,
            })
            if ok:
                removal_count += 1
            else:
                error_count += 1

    refused_count = sum(1 for s in statuses if s.decision == "REFUSE")

    # Sortie
    if args.json:
        out = {
            "scanned": len(statuses),
            "removable": sum(1 for s in statuses if s.decision == "REMOVE"),
            "refused": refused_count,
            "refusal_reasons": refusal_reason_breakdown(statuses),
            "lane_refusals": lane_refusal_breakdown(statuses),
            "skipped_current": sum(
                1 for s in statuses if s.decision == "SKIP_CURRENT"
            ),
            "dry_run": not args.apply,
            "api_stats": get_pr_resolution().stats,
            "statuses": [s.to_dict() for s in statuses],
        }
        if args.apply:
            out["apply_results"] = apply_results
            out["applied"] = removal_count
            out["apply_errors"] = error_count
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        # Texte
        if args.apply:
            print(render_text(statuses, dry_run=False, apply_results=apply_results))
            print()
            print(f"applied={removal_count}  errors={error_count}")
        else:
            print(render_text(statuses, dry_run=True))
        # Budget API de la passe (#15369) : la mesure est un livrable, pas
        # un side-effect silencieux.
        st = get_pr_resolution().stats
        print(
            f"api: cache={st['cache_hits']} lot={st['listing_calls']}"
            f" hits_lot={st['listing_hits']} ancre={st['anchor_calls']}"
            f" degrade={st['listing_degraded']}"
        )

    # Seuil d'alerte (#3895) : stderr, jamais stdout -- en --json le stdout
    # doit rester pur pour `json.loads` ; la tache planifiee fusionne les
    # deux flux dans son journal.
    if (args.warn_threshold is not None
            and refused_count > args.warn_threshold):
        warn = build_warn_line(statuses)
        if warn:
            print(warn, file=sys.stderr)

    # Exit code (#3895) : un REFUS est une decision de l'outil, pas une
    # panne. La tache planifiee reste verte (LastResult 0) quand la passe
    # s'est deroulee ; seuls les echecs d'infrastructure gh/git et les
    # echecs d'application sortent en 2. Le detail des refus vit dans le
    # rapport (decompte par classe, lane_refusals, WARN au-dela du seuil).
    if error_count > 0:
        return 2
    return 0


def run() -> int:
    """`main()` avec le contrat d'erreur garanti (#17292, reworded #3895).

    `main()` ne rattrape que `RuntimeError` : toute autre exception
    s'echappait, et Python rend alors **1** en n'ecrivant rien sur stdout --
    un code que l'appelant ne pouvait distinguer ni d'une decision de refus
    (avant #3895), ni d'une panne nommee. Mesure : c'est exactement le couple
    (`rc ∈ {0,1}`, stdout vide) qui a rougi `Scripts Tests (CPU)` sur des PRs
    de plusieurs lanes le 2026-09-21, et que l'E2E lisait comme un
    `JSONDecodeError: Expecting value: line 1 column 1`.

    Ici une panne inattendue sort par le code d'erreur **documente** du script
    (2), traceback sur stderr. Depuis #3895 (refus = decision, plus un code
    de sortie), `1` n'est plus emis par l'organe : tout code != 0 est une
    panne, sans zone grise.
    """
    try:
        return main()
    except BrokenPipeError:
        # Le consommateur a ferme le pipe (`| head`, `| jq -e` qui sort tot) :
        # ce n'est PAS un echec de l'outil, et l'ecrire sur stderr serait un
        # diagnostic faux. On ferme stdout pour que l'interpreteur ne re-tente
        # pas d'y ecrire au shutdown, puis on sort sans code d'erreur.
        try:
            sys.stdout.close()
        except OSError:
            pass
        return 0
    except Exception:
        traceback.print_exc()
        print(
            "ERROR: echec inattendu, pas une decision de l'outil "
            "(voir le traceback ci-dessus)",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    sys.exit(run())
