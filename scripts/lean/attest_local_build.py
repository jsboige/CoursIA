#!/usr/bin/env python3
"""Atteste un `lake build` **local** d'une PR qui touche du Lean (#24989).

Pourquoi cet organe existe
--------------------------
La regle HARD `lean-merge-discipline.md` §1 exige un `lake build` local par
ai-01 avant tout merge d'une PR Lean : le vert de la CI ne le remplace pas
(incident #866, revert #885). Depuis le retrait du dossier (2026-11-05),
l'APPROVE du coordinateur est la seule porte de `merge_ready` -- la regle ne
tenait plus que par sa vigilance. La garde
`scripts/coordination/merge_ready.py` (`lean:no-local-build-attestation`)
exige desormais une **preuve** ; cet organe la produit.

Il n'ecrit jamais l'attestation a la main : le format est partage avec la
garde via `scripts/lean/lean_build_attestation.py` (un seul lecteur du
format).

Ce que fait l'organe, dans cet ordre
------------------------------------
1. verifie que le login gh courant est `myia-ai-01` -- l'attestation est un
   acte du **coordinateur** ; une lane ne s'atteste pas elle-meme ;
2. resout les lakes touches par le diff (manifeste `scripts/lean/ci_lakes.json`,
   dispatcher `lake_matrix_dispatch.py`) ;
3. cree un **worktree detache** a la tete de la PR ;
4. pour chaque lake : verifie que `lean-toolchain` est identique a celui du
   cache chaud et que `lake-manifest.json` decrit le **meme graphe** de
   dependances (comparaison par graphe depuis #25370 : le `name` racine et
   les `inputRev` ne decrivent pas le graphe), puis **jonctionne**
   `.lake/packages` sur le cache (le cache est deja chaud : un
   `lake exe cache get` borne a 60 s suffirait a le remplacer, cf. incident
   2026-07-24/29) ;
5. lance `lake build` via `scripts/lean/lean_exec.py` -- l'organe de build
   borne (admission machine-wide, Job Object kill-on-close, budget, controle
   d'orphelins). L'organe **ne reimplementait** pas la discipline de build ;
   depuis #26699, le build est **cible** (`--modules auto`) : les modules
   touches, leurs jumeaux `_en` et leurs dependants, et le `.lake/build` du
   projet est **conserve** entre deux essais ;
6. nettoie : jonction **seule** (`cmd /c rmdir`, qui ne touche jamais la
   cible), puis `.lake`, puis `git worktree remove` **sans `--force`** ;
7. **sur SUCCESS seulement**, poste sous `myia-ai-01` un commentaire dont la
   premiere ligne est `[ACTION] lake build local` et qui cite le SHA complet
   de la tete, les lakes et le nombre de jobs.

Sur echec (build en echec, timeout, orphelins, cache incompatible), l'organe
ne poste **rien** : une attestation absente vaut mieux qu'une attestation
fausse. Le refus est explicite dans la sortie et dans le code de retour.

Budget et parallélisme
----------------------
`lean_exec` distingue deux grandeurs qu'il ne faut pas confondre : le
**budget** (les places reservees dans le cap machine-wide, qui compte des
PROCESSUS) et la **parallelisme accordee** (les compilations concurrentes,
qui borne `LEAN_NUM_THREADS` -- le seul levier mesure qui agit sur la
concurrence reelle, cf. #26480). Ses defauts se contredisent : `budget = 2`
places reservees, `jobs = cpu // 4` (8 sur un hote a 32 coeurs). L'organe
passe donc les deux explicitement et les aligne : le budget couvre les
compilations **et** le scheduler `lake`, sinon il sous-compte l'occupation
reelle et la supervision tue un run qui utilise exactement le parallélisme
qu'on lui a accorde.

Usage
-----
    python scripts/lean/attest_local_build.py <PR> [--repo jsboige/CoursIA]
                                              [--dry-run] [--json]
                                              [--jobs N] [--budget N]
                                              [--modules auto|all]
                                              [--cache-root DIR]

Portee du build (#26699)
------------------------
`--modules auto` (defaut) ne construit que les modules **touches** par le
diff, leurs **jumeaux `_en`** et leurs **dependants** dans le lac ; le lac
entier (`--modules all`) reste disponible. Le `.lake/build` du projet est
**conserve** entre deux essais (`--cache-root`, par defaut a cote du
depot) : un timeout ne jette plus une heure de compilation.

Sortie : JSON sur stdout avec le verdict, les lakes, les cibles construites,
la duree, le SHA atteste et l'identifiant du commentaire poste (vide si rien
n'a ete poste).
"""

from __future__ import annotations

import argparse
import base64
import fnmatch
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_DIR = REPO_ROOT / "scripts"
LEAN_DIR = SCRIPTS_DIR / "lean"
if str(LEAN_DIR) not in sys.path:
    sys.path.insert(0, str(LEAN_DIR))

import lake_matrix_dispatch  # noqa: E402
import lean_build_attestation as attestation  # noqa: E402

import attest_build_targets  # noqa: E402

DEFAULT_REPO = "jsboige/CoursIA"
MANIFEST_PATH = LEAN_DIR / "ci_lakes.json"
LEAN_EXEC = LEAN_DIR / "lean_exec.py"

# --------------------------------------------------------------------------
# #26630 -- le cache chaud se RESOUT par toolchain, il n'est plus fige.
#
# Un seul pivot (`JeuDeLaVie/conway_lean`, toolchain v4.33.0) rendait trois lakes
# INMERGEABLES PAR CONSTRUCTION : `formal_logic` (v4.33.1),
# `socialchoicepeters` (v4.32.1) et `conwaycgt` (v4.33.0-rc1) ne peuvent pas
# emprunter le cache d'une autre toolchain -- le build est produit par la
# toolchain du lake. Instance : #25236, dont `formal_logic` etait refuse
# AVANT tout build, alors que les trois autres lakes de la meme PR etaient
# verts en local.
#
# Le pivot n'est donc plus un CHEMIN FIGE : c'est le lac du clone courant dont
# le `lean-toolchain` porte la toolchain du lake atteste ET dont le
# `.lake/packages` est chaud. La table se resout a l'EXECUTION : un lake
# prechauffe devient pivot de sa toolchain, sans table a maintenir.
#
# Un lake dont la toolchain n'a aucun cache chaud n'est pas un echec de build :
# l'organe sort avec le motif distinct `no-warm-cache-for-toolchain` et la
# commande de prechauffage.
# --------------------------------------------------------------------------

#: Motif distinct rendu quand la toolchain du lake n'a aucun cache chaud.
NO_WARM_CACHE = "no-warm-cache-for-toolchain"
LAKE_NOT_IN_CLONE = "lake-absent-du-clone"

#: Sous-dossier qui porte le checkout Mathlib chaud (cible de la junction).
WARM_PACKAGES = Path(".lake") / "packages"

#: Variable d'environnement qui designates la RACINE des pivots prechauffes
#: hors clone principal.
PIVOT_ROOT_ENV = "COURSIA_LEAN_PIVOT_ROOT"

#: Nom du manifeste des lakes, DANS un depot (il sert aussi a decrire les
#: lakes d'un pivot : un worktree detache est un depot, donc il porte le
#: meme manifeste).
LAKES_MANIFEST_RELATIVE = Path("scripts") / "lean" / "ci_lakes.json"

#: Timeout du build, en secondes. Deux modules a cache chaud prennent ~90 s
#: (mesure du coordinateur) ; le budget laisse une marge large sans devenir
#: une attente non bornee.
DEFAULT_TIMEOUT = 1800.0

#: Timeout du `lake build` par lake.
DEFAULT_LAKE_TIMEOUT = 900.0

#: Timeout **par lake**, en secondes. Un lake dont le build complet depasse
#: le defaut general a besoin d'un budget propre : coupe a 900 s, il rend
#: `exit 124` **sans** que le code soit en faute, et l'attestation echoue
#: alors qu'aucune compilation n'a echoue.
#:
#: Mesure du 15/11 (dispatch du coordinateur, sur ai-01) :
#:
#: - #25585 : `exit 124` a **904 s**, 8 752 / 8 802 modules construits ;
#: - #26282 : `exit 124` a **903 s**, 8 773 / 8 804 modules construits.
#:
#: Les deux lakes concernes sont `conway` (celui de `JeuDeLaVie/conway_lean`,
#: dont le build entraine Mathlib). Le budget porte a 2 400 s laisse la
#: marge mesuree (le build complet deborde de ~1 100 modules, soit ~10 % du
#: budget restant) sans devenir une attente non bornee. Tous les autres
#: lakes gardent le defaut general.
LAKE_TIMEOUTS: dict[str, float] = {
    "conway": 2400.0,
}

#: Parallélisme accordé a `lake build` : nombre de compilations concurrentes.
#: La valeur implicite de `lean_exec` est `cpu // 4` (8 sur un hote a 32
#: coeurs), ce qui contredit son budget implicite (2 places) : les deux
#: grandeurs sont passees explicitement par l'organe (#26480).
DEFAULT_BUILD_JOBS = 3

#: Places reservees dans le cap machine-wide. Le cap compte des PROCESSUS :
#: un run qui heberge `jobs` compilations concurrentes heberge en plus le
#: scheduler `lake`. Le budget doit donc couvrir les deux, sans quoi il
#: sous-compte l'occupation reelle (#26480).
DEFAULT_BUILD_BUDGET = DEFAULT_BUILD_JOBS + 1

# --------------------------------------------------------------------------
# #26699 -- le build CIBLE, et le cache de build du projet conserve.
#
# L'organe construisait le lac ENTIER : sur `conway`, 8 802 cibles et
# plusieurs heures (trois essais du coordinateur le 15/11, tous expires),
# pour une PR qui ne touchait que trois fichiers `.lean`. La cause est la
# PORTEE du build, pas le parallélisme.
#
# Deux leviers, donc deux modes :
#   `auto` -- le build se limite aux modules touches, a leurs jumeaux `_en`
#             et a leurs dependants dans le lac (`attest_build_targets`) ;
#   `all`  -- le lac entier, comme avant (le mode historique reste
#             disponible, et le repli quand la resolution echoue).
#
# Le cache de build du PROJET (`.lake/build`, les oleans du lac lui-meme --
# ceux de Mathlib vivent dans `.lake/packages`, hors de ce cache) est
# conserve entre deux essais : un timeout ne jette plus une heure de
# compilation. Le chemin du worktree est DETERMINISTE (par PR) pour que les
# traces de lake restent valides d'un essai a l'autre.
# --------------------------------------------------------------------------

#: Mode de resolution des cibles : `auto` (cible) ou `all` (lac entier).
MODULES_AUTO = "auto"
MODULES_ALL = "all"

#: Repertoire du cache de build du projet. Par defaut, a cote du depot ( meme
#: volume que les worktrees : le deplacement du cache est un renommage, pas
#: une copie) et HORS du depot -- un cache n'est jamais commite.
DEFAULT_CACHE_DIRNAME = "attest-lean-cache"


class OrganError(RuntimeError):
    """L'organe n'a pas pu produire d'attestation."""


def _run(cmd: list[str], *, cwd: Path | None = None, timeout: float | None = None,
         env: dict[str, str] | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        env=env,
    )


def raison_alignement_budget(jobs: int, budget: int) -> str:
    """Raison pour laquelle le couple (jobs, budget) est incoherent.

    Vide = couple aligne. Deux fautes distinctes sont nommees :

    - **budget < jobs + 1** : le cap machine-wide compte des processus, et un
      run qui heberge `jobs` compilations heberge en plus le scheduler
      `lake`. Un budget inferieur sous-compte l'occupation reelle -- et la
      supervision compare le seuil a la **parallelisme accordee**
      (`effective_granted`), pas au budget : un budget trop petit tue le run
      qui utilise exactement le parallélisme qu'on lui a accorde (#26480) ;
    - **budget > jobs + 1** : le cap reserve des places que le run
      n'occupera pas, ce qui refuse des runs a tort sous un cap serre.

    Fonction **pure** : elle se teste sans Windows, sans Lake, sans
    toolchain.
    """
    if jobs < 1:
        return "parallélisme accordé {} : il doit valoir au moins 1".format(jobs)
    if budget < jobs + 1:
        return (
            "budget {} : il doit couvrir les {} compilations ET le scheduler "
            "`lake` (soit au moins {})".format(budget, jobs, jobs + 1)
        )
    if budget > jobs + 1:
        return (
            "budget {} : il reserve {} places pour un run qui n'occupe que "
            "{} compilations et un scheduler (soit {})".format(
                budget, budget, jobs, jobs + 1
            )
        )
    return ""


def lake_timeout(lake: dict | str, timeout: float | None = None) -> float:
    """Timeout effectif du build d'un lake, en secondes.

    `timeout` non nul est une **surcharge explicite** (ligne de commande) :
    elle prime toujours, y compris sur le budget propre du lake. Sinon le
    defaut general s'applique, sauf pour les lakes de `LAKE_TIMEOUTS` dont le
    build complet le depasse.

    Fonction **pure** : elle se teste sans Windows, sans Lake, sans
    toolchain.
    """
    if timeout is not None:
        return float(timeout)
    nom = lake if isinstance(lake, str) else (lake or {}).get("lake", "")
    return float(LAKE_TIMEOUTS.get(nom, DEFAULT_LAKE_TIMEOUT))


def build_failure_reason(payload: dict, violation: str | None = None) -> str:
    """Raison de l'echec d'un build de lake.

    Un **timeout** n'est pas un **echec de compilation**. Les deux se
    lisaient jusqu'ici de la meme facon ("lake build a echoue (exit_code=)"),
    alors que `builds[].status` dit bien `timeout` : le diagnostic
    renvoyait a une faute de code la ou le defaut etait un **budget de
    temps** (mesure du 15/11 : #25585 `exit 124` a 904 s, 8 752 / 8 802
    modules construits ; #26282 `exit 124` a 903 s, 8 773 / 8 804).

    Fonction **pure** : elle se teste sans Windows, sans Lake, sans
    toolchain.
    """
    if violation:
        return "violation du budget de concurrence : {}".format(violation)
    exit_code = payload.get("exit_code")
    if (payload.get("status") or "").lower() == "timeout":
        return "timeout du lake build (exit_code={})".format(exit_code)
    return "lake build a echoue (exit_code={})".format(exit_code)


def is_pure_timeout(build: dict) -> bool:
    """Vrai si un build est un **timeout pur**.

    Un timeout pur est un build **tue au minuteur** (`status == "timeout"`),
    **sans** violation du budget de concurrence et **sans** erreur de
    compilation nommee : c'est un depassement du **budget de temps**, pas une
    faute de code. La CI compile le meme lac en vert (cache Lake chaud), donc
    un timeout pur ne refuse pas la PR : il est atteste comme deferral CI
    (#27516 volet 3).

    Les deux exclusions sont portees par des champs DISTINCTS du status :
    une violation de budget de concurrence (`budget_violation`) est une
    cause de depassement qui se re-essaye (pas un timeout pur), et une
    erreur de compilation nommee (`errors`) est une faute de code, jamais un
    timeout. Fonction **pure** : elle se teste sans Windows ni Lake.
    """
    if (build.get("status") or "").lower() != "timeout":
        return False
    if build.get("budget_violation"):
        return False
    if build.get("errors"):
        return False
    return True


def gh_json(repo: str, path: str) -> object:
    """Lecture REST via ``gh`` (le jeton du processus courant)."""
    proc = _run(["gh", "api", path])
    if proc.returncode != 0:
        raise OrganError(
            "gh api {} a echoue (rc={}) : {}".format(
                path, proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
            )
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise OrganError("gh api {} : reponse non-JSON".format(path)) from exc


def current_login() -> str:
    """Login gh actif (l'attestation n'est valable que sous le coordinateur)."""
    proc = _run(["gh", "api", "user", "--jq", ".login"])
    if proc.returncode != 0:
        raise OrganError(
            "gh api user a echoue (rc={}) : {}".format(
                proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
            )
        )
    return (proc.stdout or "").strip()


def pr_files(repo: str, pr: int) -> list[str]:
    """Chemins du diff de la PR (lecture paginee)."""
    files: list[str] = []
    for page in range(1, 31):
        payload = gh_json(
            repo, "repos/{}/pulls/{}/files?per_page=100&page={}".format(repo, pr, page)
        )
        if not isinstance(payload, list):
            raise OrganError("liste de fichiers illisible pour #{}".format(pr))
        for row in payload:
            if not isinstance(row, dict) or not isinstance(row.get("filename"), str) or not row["filename"]:
                raise OrganError("fichier sans filename pour #{}".format(pr))
            files.append(row["filename"])
            previous = row.get("previous_filename")
            if row.get("status") == "renamed":
                if not isinstance(previous, str) or not previous:
                    raise OrganError("renommage sans previous_filename pour #{}".format(pr))
                files.append(previous)
        if len(payload) < 100:
            return files
    raise OrganError("liste de fichiers potentiellement tronquee pour #{}".format(pr))


def pr_head(repo: str, pr: int) -> str:
    payload = gh_json(repo, "repos/{}/pulls/{}".format(repo, pr))
    if not isinstance(payload, dict):
        raise OrganError("PR #{} illisible".format(pr))
    head = ((payload.get("head") or {}).get("sha")) or ""
    if not head:
        raise OrganError("PR #{} : tete absente".format(pr))
    return str(head)


def lakes_for(files: list[str]) -> list[dict]:
    """Lakes touches par le diff, selon le manifeste de la matrice CI.

    Un diff qui touche un `.lean` hors lake connu n'est pas ignore : il est
    signale par l'appelant (la garde le bloque de toute facon) ; ici, on ne
    construit que ce que le manifeste sait construire.
    """
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    return lake_matrix_dispatch.changed_lakes(files, manifest)


def _read_if_present(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None


def _same_file(a: Path, b: Path) -> bool:
    """Deux fichiers d'outillage identiques au sens du contenu."""
    left = _read_if_present(a)
    right = _read_if_present(b)
    if left is None or right is None:
        return False
    return left.strip() == right.strip()


def _toolchain_of(lake_dir: Path) -> str | None:
    """Toolchain d'un lake (contenu de `lean-toolchain`), ou `None`."""
    raw = _read_if_present(lake_dir / "lean-toolchain")
    return raw.strip() if raw is not None else None


def cache_pivot_candidates(manifest: dict) -> list[Path]:
    """Repertoires du clone courant susceptibles de porter un cache chaud.

    Tous les lakes du manifeste sont candidats : la table de pivots se resout
    a l'EXECUTION, un lake prechauffe devient pivot de sa toolchain sans
    qu'une table soit a maintenir dans le code (#26630).

    S'y ajoutent les pivots **prechauffes hors clone** (#26889) : le plan de
    prechauffage travaille dans un worktree detache, donc HORS du clone
    principal, et le resolveur ne regardait que le clone -- un prechauffage
    fait comme le plan le prescrit n'etait jamais vu, et le lake continuait
    de rendre `no-warm-cache-for-toolchain`.
    """
    out: list[Path] = []
    for entry in manifest.get("lakes") or []:
        if not isinstance(entry, dict):
            continue
        project_path = entry.get("project-path")
        if isinstance(project_path, str) and project_path:
            out.append(REPO_ROOT / project_path)
    vus = {p.resolve() for p in out if p.exists()}
    for extra in prewarmed_pivot_candidates():
        if extra.resolve() not in vus:
            vus.add(extra.resolve())
            out.append(extra)
    return out


def pivot_root() -> Path:
    """RACINE des pivots prechauffes, hors du clone principal.

    Le plan de prechauffage travaille dans un worktree detache : le cache
    chaud atterrit HORS du clone de travail, ce qui evite que `lake`
    re-resolve et lance git dans le depot englobant (#26630). Il faut donc
    une racine **conventionnelle** : le resolveur doit pouvoir retrouver
    les pivots sans qu'on les declare a la main.

    La racine est surchargeable par `COURSIA_LEAN_PIVOT_ROOT` (les clones
    de travail et les clones de production ne sont pas forcement voisins).
    """
    raw = os.environ.get(PIVOT_ROOT_ENV, "").strip()
    if raw:
        return Path(raw).expanduser()
    return REPO_ROOT.parent / "coursia-lean-pivots"


def prewarmed_pivot_candidates(root: Path | None = None) -> list[Path]:
    """Lakes prechauffes **hors clone**, decouverts dans la racine des pivots.

    Un pivot est un WORKTREE detache (un depot) ; les lakes qu'il porte sont
    ceux de son manifeste (`scripts/lean/ci_lakes.json`), a la tete qui a
    ete prechauffee. Seuls sont retenus les lakes qui portent DEJA un
    `.lake/packages` : les autres n'ont pas ete prechauffes, et les lister
    comme candidats ne ferait que bruire dans les motifs de rejet.
    """
    base = root if root is not None else pivot_root()
    if not base.is_dir():
        return []
    out: list[Path] = []
    for worktree in sorted(base.iterdir()):
        if not worktree.is_dir():
            continue
        manifest_path = worktree / LAKES_MANIFEST_RELATIVE
        if not manifest_path.is_file():
            continue
        try:
            payload = json.loads(manifest_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            continue
        if not isinstance(payload, dict):
            continue
        for entry in payload.get("lakes") or []:
            if not isinstance(entry, dict):
                continue
            project_path = entry.get("project-path")
            if not isinstance(project_path, str) or not project_path:
                continue
            lake_dir = worktree / project_path
            if (lake_dir / WARM_PACKAGES).is_dir():
                out.append(lake_dir)
    return out


def _toolchain_at_head(repo: str, head: str, project_path: str) -> str:
    """Toolchain du lake TELLE QU'ELLE EST a la tete de la PR.

    Un lake AJOUTE par la PR n'existe pas dans le clone courant : sa
    toolchain se lit sur le contenu de la tete (le fichier
    `lean-toolchain` est un chemin declare par le manifeste).
    """
    try:
        payload = gh_json(
            repo,
            "repos/{}/contents/{}/lean-toolchain?ref={}".format(repo, project_path, head),
        )
    except OrganError:
        # Contenu illisible : la toolchain reste INCONNUE, l'appelant decide.
        return ""
    if not isinstance(payload, dict):
        return ""
    content = payload.get("content")
    if not isinstance(content, str):
        return ""
    try:
        return base64.b64decode(content).decode("utf-8").strip()
    except (ValueError, UnicodeDecodeError):
        return ""


def _pivot_candidates(base_manifest: dict, head_manifest: dict | None) -> list[Path]:
    """Candidats-pivot : les lakes de `main` PLUS ceux declares par la tete.

    Un lake AJOUTE par la PR peut avoir ete prechauffe dans le clone courant
    ; il est alors un pivot legitime pour sa toolchain. Le candidat qui n'a
    pas de repertoire dans le clone est ignore a la resolution (pas de
    `lean-toolchain` lisible).
    """
    out = list(cache_pivot_candidates(base_manifest))
    vus = {p.resolve() for p in out if p.exists()}
    for extra in cache_pivot_candidates(head_manifest or {}):
        if extra.exists() and extra.resolve() not in vus:
            vus.add(extra.resolve())
            out.append(extra)
    return out


#: Type de paquet lake qui vit a SON `dir` : il ne se materialise jamais
#: sous `.lake/packages/<nom>`, donc l'exiger la rendra toujours absent.
#:
#: Mesure du 22/11 sur ai-01, lac `busybeaver_lean` : le manifeste declare
#: `Foundation` en `type: path`, `dir: .lake/packages/pa196/PA196/vendor/Foundation`
#: (paquet herite du `git` `pa196`). Le repertoire EXISTE dans le pivot
#: prechauffe, mais `_packages_absent` le cherchait sous
#: `.lake/packages/Foundation` -- absent -- et le lac entier etait ecarte avec
#: le motif `packages incomplets : Foundation absent`. Instance : issue
#: #27923 (bloque #27658 puis #27587).
PATH_PACKAGE_TYPE = "path"


def _declared_packages(lake_dir: Path) -> list[dict]:
    """Paquets declares par le `lake-manifest.json` d'un lake.

    Chaque entree porte `name`, `type` et `dir` (`dir` vaut `None` pour un
    paquet de type `git`).

    Manifeste absent, illisible ou sans tableau `packages` : la liste est
    VIDE. L'exigence porte alors sur le critere general (`.lake/packages`
    non vide) -- on n'invente pas de paquet a exiger.
    """
    manifest = lake_dir / "lake-manifest.json"
    try:
        payload = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    if not isinstance(payload, dict):
        return []
    packages = payload.get("packages")
    if not isinstance(packages, list):
        return []
    entries: list[dict] = []
    for entry in packages:
        if not isinstance(entry, dict):
            continue
        name = entry.get("name")
        if not isinstance(name, str) or not name:
            continue
        ptype = entry.get("type")
        pdir = entry.get("dir")
        entries.append({
            "name": name,
            "type": ptype if isinstance(ptype, str) and ptype else "git",
            "dir": pdir if isinstance(pdir, str) and pdir else None,
        })
    return entries


#: Lake ecrit un nom de paquet entre guillemets quand le nom nu n'est pas
#: ecritable dans le DSL (un tiret, par exemple) : `«axiom-audit»`. Le
#: REPERTOIRE, sous `.lake/packages/`, porte le nom NU.
#:
#: Comparer les deux chaines sans normaliser rend le verdict de completude
#: structurellement faux : un cache chaud COMPLET est declare absent, puis
#: le lac entier est refuse avec le motif `no-warm-cache-for-toolchain`.
#: Mesure du 20/11 sur ai-01, lac `formal_logic` (toolchain `v4.33.1`) :
#: `axiom-audit` et `doc-gen4` etaient presents ET resolus dans le pivot
#: (`.git`, sources, `.lake` pour le second), et le pivot a quand meme ete
#: ecarte -- motif : « packages incomplets : «axiom-audit» absent,
#: «doc-gen4» absent ». Instance : PR #25236.
QUOTE_GUILLEMETS = ("«", "»")


def _package_dir_name(name: str) -> str:
    """Nom du REPERTOIRE du paquet, sans la citation de lake.

    `«axiom-audit»` -> `axiom-audit`. Un nom sans guillemets est rendu tel
    quel : la normalisation n'introduit aucune hypothese.
    """
    raw = name.strip()
    if (
        len(raw) >= 2
        and raw.startswith(QUOTE_GUILLEMETS[0])
        and raw.endswith(QUOTE_GUILLEMETS[1])
    ):
        raw = raw[1:-1].strip()
    return raw


def _package_is_resolved(package_dir: Path, name: str) -> bool:
    """Le paquet `name` est-il reellement RESOLU sous `.lake/packages/` ?

    Un repertoire vide traine (lac ouvert puis abandonne, `cache get`
    interrompu, paquet supprime) : lake le voit comme un paquet et va le
    re-resoudre -- donc le re-telecharger, donc lancer git DANS le depot
    englobant. C'est l'incident mesure le 14/11 sur ai-01 (fetch et checkout
    tentes dans `D:/CoursIA`).

    La preuve de resolution :
    - un paquet `git` a son `.git` (le checkout) ou son `lakefile.*` ;
    - Mathlib se COMPILE : le build deja fait se lit a
      `.lake/packages/mathlib/.lake/build`. Sans lui, le paquet est present
      mais incomplet -- et c'est precisement lui qu'il faut recompiler.
    """
    if not package_dir.is_dir():
        return False
    if name == "mathlib":
        return (package_dir / ".lake" / "build").is_dir()
    if (package_dir / ".git").exists():
        return True
    return any(package_dir.glob("lakefile.*"))


def _path_package_served(owner: Path, packages_dir: Path, dir_rel: str) -> Path:
    """Repertoire EFFECTIVEMENT servi pour un paquet de type `path`.

    Un paquet `path` vit a son `dir`, relatif au lake qui le declare -- il
    ne se materialise JAMAIS sous `.lake/packages/<nom>`. Deux cas :

    - `dir` SOUS `.lake/packages` : le contenu servi est celui du cache
      chaud, parce que la jonction `<lake>/.lake/packages` ->
      `<pivot>/.lake/packages` sert exactement ce repertoire -> on regarde
      dans `packages_dir` ;
    - `dir` AILLEURS (paquet frere dans l'arbre du depot) : le contenu
      servi est celui du proprietaire lui-meme -> on regarde dans `owner`.
    """
    rel = Path(dir_rel.replace("\\", "/"))
    try:
        under = rel.relative_to(WARM_PACKAGES)
    except ValueError:
        return owner / rel
    return packages_dir / under


def _packages_absent(manifest_owner: Path, packages_dir: Path) -> list[str]:
    """Paquets declares par `manifest_owner` et NON materialises dans
    `packages_dir`.

    Le manifeste peut venir d'un lake et le dossier de paquets d'un autre :
    c'est la question qui compte -- « le pivot sait-il servir les paquets
    que le lake demande ? ». Liste VIDE = rien ne manque.

    Un paquet de type `path` se verifie a SON `dir` (relatif au lake qui le
    declare), pas sous `.lake/packages/<nom>` : exiger la materialisation
    d'un paquet `path` la declare TOUJOURS absent, quel que soit son
    prechauffage (#27923).
    """
    missing: list[str] = []
    for entry in _declared_packages(manifest_owner):
        name = entry["name"]
        if entry["type"] == PATH_PACKAGE_TYPE and entry["dir"]:
            served = _path_package_served(manifest_owner, packages_dir, entry["dir"])
            if not served.is_dir():
                missing.append("{} absent (dir {})".format(name, entry["dir"]))
            continue
        dir_name = _package_dir_name(name)
        package_dir = packages_dir / dir_name
        if not package_dir.is_dir():
            missing.append("{} absent".format(name))
        elif not _package_is_resolved(package_dir, dir_name):
            missing.append("{} incomplet".format(name))
    return missing


def _pivot_is_warm(candidate: Path, lake_dir: Path) -> tuple[bool, str]:
    """Le cache du candidat est-il chaud ET complet ?

    Renvoie (ok, motif). Le motif nomme le paquet qui manque : sans lui, un
    verdict « aucun cache chaud » ne dit pas POURQUOI aucun pivot n'a ete
    retenu.
    """
    packages_dir = candidate / WARM_PACKAGES
    if not packages_dir.is_dir():
        return False, ".lake/packages absent"
    materialises = [
        p for p in packages_dir.iterdir()
        if p.is_dir() and not p.name.startswith(".")
    ]
    if not materialises:
        return False, "packages vides"
    # Ce que le CANDIDAT declare doit etre la, resolu.
    missing = _packages_absent(candidate, packages_dir)
    if missing:
        return False, "packages incomplets : {}".format(", ".join(missing))
    # Ce que le LAKE DEMANDE doit etre la aussi : sinon lake va chercher
    # le paquet manquant -- et l'ecrire dans le repertoire vers lequel la
    # junction pointe, c'est-a-dire DANS le clone principal.
    missing = _packages_absent(lake_dir, packages_dir)
    if missing:
        return False, "packages du lake non servis : {}".format(", ".join(missing))
    return True, ""


def resolve_cache_pivot(lake_dir: Path, candidates: list[Path]) -> dict:
    """Pivot de cache chaud applicable a `lake_dir`, resolu a l'execution.

    Un pivot vaut si sa toolchain est la MEME que celle du lake ET si son
    `.lake/packages` est chaud **et complet** dans le clone courant. La
    comparaison de GRAPHE (#25370) reste faite ensuite, par
    `check_cache_compatibility` : la toolchain est une condition
    NECESSAIRE, pas suffisante.

    « Chaud » se MESURE : un `.lake/packages` vide ou partiel passe pour
    un cache chaud, et lake va alors re-resoudre les paquets manquants --
    donc lancer git dans le depot englobant et ecrire dans le clone
    principal a travers la junction (incident mesure le 14/11 sur ai-01).
    Un candidat incomplet est donc ECARTE, avec son motif.

    Un lake sans pivot applicable n'est pas un echec de build : le motif
    distinct `no-warm-cache-for-toolchain` est rendu, avec la commande de
    prechauffage (#26630).
    """
    toolchain = _toolchain_of(lake_dir)
    if not toolchain:
        return {"ok": False, "reason": "lean-toolchain absent du lake"}
    warm = []
    rejects: list[str] = []
    for candidate in candidates:
        if candidate == lake_dir:
            continue
        if _toolchain_of(candidate) != toolchain:
            continue
        ok, why = _pivot_is_warm(candidate, lake_dir)
        if not ok:
            rejects.append("{} ecarte : {}".format(candidate.name, why))
            continue
        warm.append(candidate)
    if not warm:
        return {
            "ok": False,
            "reason": NO_WARM_CACHE,
            "toolchain": toolchain,
            "detail": "aucun cache chaud pour la toolchain {} dans le clone courant{}".format(
                toolchain,
                " ; " + " | ".join(rejects) if rejects else "",
            ),
            "rejects": rejects,
        }
    # Parmi les pivots chauds de la meme toolchain, celui de MEME GRAPHE
    # passe en tete. Retenir le premier chaud dans l'ordre du manifeste
    # faisait echouer un lake des qu'un pivot plus haut dans la liste
    # portait un paquet de plus : mesure du 22/11 sur ai-01, `knot` resolu
    # sur `discrepancy_lean` (qui sert `learning_theory_lean`) alors que
    # `game_theory_lean` et `hecke_lean`, chauds et de meme graphe, etaient
    # la -- deux PRs Knots refusees. Le verdict reste celui de
    # `check_cache_compatibility` : sans pivot compatible, l'ordre ne change
    # pas, et le motif d'incompatibilite du premier est rendu comme avant.
    compatibles = [
        p for p in warm if check_cache_compatibility(lake_dir, p).get("ok")
    ]
    ordered = compatibles + [p for p in warm if p not in compatibles]
    return {
        "ok": True,
        "pivot": str(ordered[0]),
        "toolchain": toolchain,
        "pivots": [str(p) for p in ordered],
        "rejects": rejects,
    }


def prewarm_plan(lake: dict, *, head: str, timeout: float) -> dict:
    """Commande de prechauffage du cache chaud d'un lake (#26630).

    Le prechauffage se fait dans un WORKTREE DETACHE a la tete de la PR : sur
    un lac au paquet vide, `lake` re-resout et lance git dans le depot
    ENCLOSANT -- dans le clone principal, le geste polluerait le clone de
    travail de la lane et concurrence les autres gestes de la machine.

    Les commandes passent par `lean_exec.py` (budget machine-wide, une lake a
    la fois, plafond memoire) : ce fichier ne lance aucun processus lake lui
    meme. Les marqueurs `<stdout>` / `<stderr>` sont a remplacer par des
    chemins reels.

    Le worktree est cree dans la RACINE DES PIVOTS (`pivot_root()`), pas
    dans un `<worktree-detache>` sans adresse : c'est cette racine que le
    resolveur de pivot parcourt (#26889). Un prechauffage fait dans un
    worktree hors de cette racine produirait un cache chaud que le
    resolveur ne voit pas -- l'echec etait muet (le lake rendait
    `no-warm-cache-for-toolchain` apres un prechauffage pourtant fait).
    """
    worktree = str(pivot_root() / (lake.get("lake") or "pivot"))
    lake_dir = "{}/{}".format(worktree, lake.get("project-path") or "")

    def _cmd(payload: list[str]) -> list[str]:
        return _lean_exec_argv(
            payload,
            lake_dir=Path(lake_dir),
            timeout=timeout,
            stdout_file=Path("<stdout>"),
            stderr_file=Path("<stderr>"),
        )

    return {
        "pivot_root": str(pivot_root()),
        "prepare": ["mkdir", "-p", str(pivot_root())],
        "worktree": [
            "git",
            "-C",
            str(REPO_ROOT),
            "worktree",
            "add",
            "--detach",
            worktree,
            head,
        ],
        "cache_get": _cmd(["lake", "exe", "cache", "get"]),
        "build": _cmd(["lake", "build"]),
        "note": (
            "prechauffage dans un worktree DETACHE sous la racine des pivots "
            "({}), via lean_exec.py ; sur un lac au paquet vide, lake "
            "re-resout et lance git dans le depot englobant ; le resolveur "
            "retrouve ce pivot dans la meme racine"
        ).format(pivot_root()),
    }


def manifest_at_head(repo: str, head: str) -> dict | None:
    """Manifeste `ci_lakes.json` tel qu'il est a la TETE de la PR.

    Le manifeste lu doit etre celui de la tete : une PR qui AJOUTE un lake
    (#26399) ne l'atteste jamais si l'organe lit celui de `main` -- le lake
    neuf est precisement le seul que la PR construit (#26630). `None` si le
    manifeste est absent ou illisible a la tete : l'appelant refute.
    """
    payload = gh_json(
        repo,
        "repos/{}/contents/scripts/lean/ci_lakes.json?ref={}".format(repo, head),
    )
    # Le decodage de la payload REST est PORTÉ par le module partage
    # (`lean_build_attestation`) : la garde lit le meme manifeste par le meme
    # decodeur -- une seule definition du "contenu illisible".
    return attestation.manifest_from_api_payload(payload)


def select_lakes(files: list[str], head_manifest: dict, base_manifest: dict | None) -> list[dict]:
    """Lakes a attester : ceux que la PR touche, plus ceux qu'elle AJOUTE.

    Deux corrections par rapport a `lake_matrix_dispatch.changed_lakes` :

    1. le manifeste est celui de la TETE -- un lake ajoute par la PR y est
       declare ;
    2. l'expansion « un fichier du gate -> TOUS les lakes » du dispatcher CI
       ne s'applique PAS a l'attestation : toucher `ci_lakes.json` ou le
       workflow doit attester les lakes TOUCHES et les lakes AJOUTES, pas les
       36 lakes du manifeste. Mesure : dry-run de #26399, qui echouait sur
       onze lakes que la PR ne touche pas, faute de cache (#26630).
    """
    entries = [e for e in (head_manifest.get("lakes") or []) if isinstance(e, dict)]
    base_names = set()
    for entry in (base_manifest or {}).get("lakes") or []:
        if isinstance(entry, dict) and entry.get("lake"):
            base_names.add(str(entry["lake"]))
    selected: dict[str, dict] = {}
    for entry in entries:
        name = str(entry.get("lake") or "")
        for pattern in entry.get("paths") or []:
            if any(fnmatch.fnmatch(f, pattern) for f in files):
                if name:
                    selected[name] = entry
                break
    for entry in entries:
        name = str(entry.get("lake") or "")
        if name and name not in base_names:
            selected[name] = entry
    return [e for e in entries if str(e.get("lake")) in selected]


# --------------------------------------------------------------------------
# #25370 -- le cache chaud se juge PAR GRAPHE, pas octet pour octet.
#
# Deux manifestes de lakes differents decrivent le meme graphe de
# dependances alors que le fichier differe sur deux champs qui ne le
# decrivent pas :
#
# - le `name` racine : il differe PAR CONSTRUCTION d'un lake a l'autre
#   (`"conway"` contre `"decision_theory_lean"`) ;
# - l'`inputRev` d'un paquet : c'est la revision DEMANDEE (le tag
#   `v4.33.0`), pas le commit resolu (`rev`). Deux lakes qui demandent le
#   tag et le SHA qui le resout decrivent le meme graphe.
#
# Comparer le fichier octet pour octet rendait donc le cache chaud
# inapplicable a tout lake hors du pivot, et bloquait toute PR `.lean`
# qui ne touche pas le pivot (#24894, #25262, #25359).
# --------------------------------------------------------------------------

#: Champs du manifeste qui decrivent le graphe lui-meme.
_MANIFEST_GRAPH_FIELDS = ("version", "packagesDir")

#: Champs d'un paquet qui decrivent le graphe lui-meme. `inputRev` en est
#: volontairement exclu : c'est la revision demandee, pas le commit resolu.
_MANIFEST_PACKAGE_FIELDS = ("url", "rev", "subDir")


def _read_manifest(path: Path) -> dict | None:
    """Lit un `lake-manifest.json` ; `None` s'il est absent ou illisible.

    `None` n'est jamais un accord : l'appelant doit refuser (fail-closed).
    """
    raw = _read_if_present(path)
    if raw is None:
        return None
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError:
        return None
    return payload if isinstance(payload, dict) else None


def _manifest_packages(manifest: dict) -> dict[str, dict]:
    """Les paquets d'un manifeste, indexes par nom.

    Une entree malformee (pas un objet, sans nom) est ignoree : elle ne
    decrit aucun paquet identifiable, et le refus doit nommer un paquet.
    """
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        return {}
    out: dict[str, dict] = {}
    for entry in packages:
        if not isinstance(entry, dict):
            continue
        name = str(entry.get("name") or "")
        if name:
            out[name] = entry
    return out


def manifest_graph_difference(mine: dict, theirs: dict) -> str | None:
    """Raison du refus, ou `None` quand les deux manifestes decrivent le
    meme graphe de dependances.

    Compare `version`, `packagesDir`, puis l'ensemble des paquets par
    `(name, url, rev, subDir)`. Le `name` racine et les `inputRev` sont
    ignores : ils ne decrivent pas le graphe (cf. le commentaire de bloc
    ci-dessus). Le refus nomme le paquet et les deux valeurs divergentes.
    """
    for field in _MANIFEST_GRAPH_FIELDS:
        left = str(mine.get(field) or "")
        right = str(theirs.get(field) or "")
        if left != right:
            return "{} different -- lake={!r}, cache={!r}".format(field, left, right)
    mine_packages = _manifest_packages(mine)
    cache_packages = _manifest_packages(theirs)
    absent = sorted(set(mine_packages) - set(cache_packages))
    if absent:
        return "paquet(s) absent(s) du cache chaud : {}".format(", ".join(absent))
    surplus = sorted(set(cache_packages) - set(mine_packages))
    if surplus:
        return "paquet(s) present(s) dans le cache chaud et absent(s) du lake : {}".format(
            ", ".join(surplus)
        )
    for name in sorted(mine_packages):
        left = mine_packages[name]
        right = cache_packages[name]
        for field in _MANIFEST_PACKAGE_FIELDS:
            left_value = str(left.get(field) or "")
            right_value = str(right.get(field) or "")
            if left_value != right_value:
                return "paquet {} : {} different -- lake={!r}, cache={!r}".format(
                    name, field, left_value, right_value
                )
    return None


def check_cache_compatibility(lake_dir: Path, cache_root: Path) -> dict:
    """Le cache chaud s'applique-t-il a ce lake ? Verdict, SANS mutation.

    Aucun fichier n'est touche ici : la jonction est posee par
    `prepare_lake`, apres ce verdict. Ce decoupage permet au mode
    `--dry-run` de rendre le verdict de cache sans construire ni
    modifier quoi que ce soit.
    """
    for name in ("lean-toolchain", "lake-manifest.json"):
        if not (lake_dir / name).is_file():
            return {"ok": False, "reason": "{} absent du lake".format(name)}
        if not (cache_root / name).is_file():
            return {"ok": False, "reason": "{} absent du cache".format(name)}

    # `lean-toolchain` : comparaison au CONTENU. La toolchain est le
    # contenu du build ; elle doit etre la meme, au caractere pres.
    if not _same_file(lake_dir / "lean-toolchain", cache_root / "lean-toolchain"):
        return {
            "ok": False,
            "reason": "lean-toolchain different du cache -- cache chaud non applicable",
        }

    # `lake-manifest.json` : comparaison PAR GRAPHE (#25370).
    mine = _read_manifest(lake_dir / "lake-manifest.json")
    if mine is None:
        return {
            "ok": False,
            "reason": "lake-manifest.json illisible (JSON invalide) -- cache chaud non applicable",
        }
    theirs = _read_manifest(cache_root / "lake-manifest.json")
    if theirs is None:
        return {
            "ok": False,
            "reason": "lake-manifest.json du cache illisible (JSON invalide)",
        }
    difference = manifest_graph_difference(mine, theirs)
    if difference is not None:
        return {
            "ok": False,
            "reason": "lake-manifest.json different du cache -- {} -- "
            "cache chaud non applicable".format(difference),
        }

    return {"ok": True, "checks": ["lean-toolchain", "lake-manifest.json"]}


def _is_junction(path: Path) -> bool:
    """Vrai si `path` est une jonction/reparse point NTFS."""
    try:
        if not path.exists() and not os.path.lexists(str(path)):
            return False
    except OSError:
        return False
    if os.name != "nt":
        return os.path.islink(str(path))
    # `os.path.islink` est Faux sur une junction Windows : c'est la
    # divergence entre le chemin et sa resolution reelle qui la revele
    # (cf. scripts/lean/check_mathlib_cache.py, memes primitives).
    try:
        return os.path.realpath(str(path)) != str(Path(path).resolve(strict=False))
    except OSError:
        return False


def _make_junction(link: Path, target: Path) -> None:
    """Jonction NTFS vers `target` (pas de privilege admin requis)."""
    link.parent.mkdir(parents=True, exist_ok=True)
    if os.name == "nt":
        proc = _run(["cmd", "/c", "mklink", "/J", str(link), str(target)])
        if proc.returncode != 0:
            raise OrganError(
                "mklink /J a echoue (rc={}) : {}".format(
                    proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
                )
            )
        return
    link.symlink_to(target, target_is_directory=True)


def _remove_junction(link: Path) -> None:
    """Retire le lien seul (`rmdir` sur une junction ne touche pas la cible)."""
    if os.name == "nt":
        proc = _run(["cmd", "/c", "rmdir", str(link)])
        if proc.returncode != 0:
            raise OrganError(
                "rmdir de la jonction a echoue (rc={}) : {}".format(
                    proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
                )
            )
        return
    if link.is_symlink():
        link.unlink()


def prepare_lake(lake_dir: Path, cache_root: Path) -> dict:
    """Prepare le cache chaud d'un lake : verifie l'outillage, junctionne.

    Refuse (fail-closed) si la toolchain differe du cache, ou si le
    manifeste decrit un graphe de dependances different : le cache chaud ne
    vaut que pour la meme toolchain et le meme graphe (cf.
    `setup_shared_mathlib.ps1` : le build a travers la junction est un pur
    replay a cette condition). Le manifeste est compare PAR GRAPHE depuis
    #25370 -- le `name` racine et les `inputRev` ne decrivent pas le graphe.
    """
    verdict = check_cache_compatibility(lake_dir, cache_root)
    if not verdict["ok"]:
        return verdict
    checks = verdict["checks"]

    packages = lake_dir / ".lake" / "packages"
    if packages.exists() or os.path.lexists(str(packages)):
        # Un `.lake/packages` deja present (checkout reel) : on ne le remplace
        # pas, on ne mesure pas -- le lake sera construit tel quel.
        return {"ok": True, "checks": checks, "junction": False}

    target = cache_root / ".lake" / "packages"
    if not target.is_dir():
        return {"ok": False, "reason": "cache chaud absent : {}".format(target)}
    _make_junction(packages, target)
    return {"ok": True, "checks": checks, "junction": True}


def _lean_exec_argv(payload: list[str], *, lake_dir: Path, timeout: float,
                    stdout_file: Path, stderr_file: Path,
                    budget: int = DEFAULT_BUILD_BUDGET) -> list[str]:
    """Charge de l'organe canonique `lean_exec.py`, avec la commande en payload.

    Le `payload` est ce que l'ORGANE lancera sous le budget commun
    (admission machine-wide, Job Object kill-on-close) : ce fichier ne lance
    aucun processus lake lui-meme. C'est precisement la distinction que fait
    le garde `check_lake_direct_invocation.py` -- un conducteur de l'organe
    peut nommer sa commande de charge dans un payload, jamais dans un argv
    qu'il execute.

    Le `budget` (places reservees dans le cap machine-wide) est passe
    EXPLICITEMENT : la valeur implicite de `lean_exec` (2) ne couvre pas le
    parallélisme qu'il accorde par defaut (`cpu // 4`), et c'est cette
    contradiction qui a fait tuer des lake builds multi-modules (#26480).
    """
    organ = "lean_exec.py"
    return [
        sys.executable,
        str(LEAN_DIR / organ),
        "run",
        "--backend",
        "native",
        "--timeout",
        str(timeout),
        "--budget",
        str(budget),
        "--caller",
        "attest_local_build",
        "--cwd",
        str(lake_dir),
        "--stdout-file",
        str(stdout_file),
        "--stderr-file",
        str(stderr_file),
        "--json",
        "--",
    ] + list(payload)


#: Une ligne d'erreur Lean (`error: 'x' has type ...`).
ERROR_MARKER = "error:"
#: Nombre de lignes de contexte conservees apres chaque ligne d'erreur : le
#: detail du diagnostic Lean est sur les lignes SUIVANTES, pas sur la ligne
#: `error:` elle-meme.
ERROR_CONTEXT_LINES = 3
#: Plafond du nombre d'erreurs extraites (une sortie de build peut en contenir
#: des centaines ; le champ doit rester lisible).
ERROR_MAX = 50


def extract_errors(text: str, *, context_lines: int = ERROR_CONTEXT_LINES,
                   limit: int = ERROR_MAX) -> list[dict]:
    """Les lignes d'erreur d'une sortie de build, avec leur contexte.

    `lake build` ecrit ses diagnostics sur stderr, et l'organe ne capture
    qu'une QUEUE de 4000 caracteres : une erreur nommee y etait noyee, et
    l'organe ne pouvait dire QUE « le build a echoue ». Ici chaque ligne
    `error:` est extraite avec les lignes qui la completent, et le champ
    `errors[]` porte la liste.

    L'extraction est une LECTURE : le texte n'est jamais reecrit.
    """
    lines = (text or "").splitlines()
    found: list[dict] = []
    for index, line in enumerate(lines):
        if ERROR_MARKER not in line:
            continue
        found.append({
            "text": line.strip(),
            "line_number": index + 1,
            "context": [item.rstrip() for item in
                        lines[index + 1: index + 1 + context_lines]],
        })
        if len(found) >= limit:
            break
    return found


def run_lake_build(lake_dir: Path, timeout: float,
                   jobs: int = DEFAULT_BUILD_JOBS,
                   budget: int = DEFAULT_BUILD_BUDGET,
                   targets: list[str] | None = None) -> dict:
    """`lake build` borne via `lean_exec.py` (l'organe de build existant).

    Le payload `lake build` est un **PAYLOAD** : il est passe a l'organe
    canonique, qui le lance sous le budget commun. Ce fichier ne lance
    aucun processus lake lui-meme.

    `targets` limite la construction aux modules nommes (#26699) ; une liste
    vide ou `None` construit le lac entier (mode `all`).

    Le parallélisme demande (`LEAN_EXEC_JOBS`) est pose dans l'environnement
    de l'enfant : `lean_exec` le lit de la, et sa valeur implicite
    (`cpu // 4`) contredit son budget implicite (2). `lean_exec` reborne
    encore ce parallelisme par les ressources mesurees (RAM, commit, CPU) :
    la valeur demandee ici est un plafond, pas une consommation forcee.
    """
    with tempfile.TemporaryDirectory(prefix="attest-lean-") as tmp:
        stdout_file = Path(tmp) / "stdout.txt"
        stderr_file = Path(tmp) / "stderr.txt"
        cmd = _lean_exec_argv(
            # PAYLOAD remis a l'organe : la commande est decrite ICI, au
            # point de la remise, jamais dans une liste de commande posee
            # ailleurs (le garde `check_lake_direct_invocation.py` refuse
            # qu'un argv de lake existe hors de la main de l'organe).
            ["lake", "build"] + list(targets or []),
            lake_dir=lake_dir,
            timeout=timeout,
            stdout_file=stdout_file,
            stderr_file=stderr_file,
            budget=budget,
        )
        env = {**os.environ, "LEAN_EXEC_JOBS": str(jobs)}
        proc = _run(cmd, timeout=timeout + 120.0, env=env)
        # Review #25002 (Hermes, 2026-11-06, prouve par execution) : les deux
        # fichiers doivent etre lus DANS le bloc `with` -- _read_if_present en
        # dehors lisait un dossier temporaire deja detruit et rendait des
        # queues vides a chaque appel, y compris sur echec de build, la ou le
        # JSON est la seule trace diagnostique. result["ok"] restait gouverne
        # par exit_code : defaut de diagnostic, pas de verdict.
        stdout_text = _read_if_present(stdout_file) or ""
        stderr_text = _read_if_present(stderr_file) or ""
    payload = {}
    try:
        payload = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        payload = {}
    payload["stdout_tail"] = stdout_text[-4000:]
    payload["stderr_tail"] = stderr_text[-4000:]
    # Les erreurs nommees, hors de la queue : c'est ce que l'organe peut
    # dire du build qui a echoue, au-dela de « le build a echoue ».
    payload["errors"] = (
        extract_errors(stdout_text) + extract_errors(stderr_text)
    )[:ERROR_MAX]
    payload["organ_rc"] = proc.returncode
    return payload


# --------------------------------------------------------------------------
# #26699 -- le cache de build du PROJET, conserve entre deux essais.
#
# Ce qui est conserve est le `.lake/build` du lac -- les oleans des modules
# DU LAC. Les oleans de Mathlib vivent dans `.lake/packages` (la jonction
# vers le cache chaud), donc hors de ce cache : ce que l'on conserve, c'est
# exactement le travail que le lac a produit et qu'un timeout aurait jete.
#
# Le cache est invalide si la toolchain ou le graphe de dependances change :
# il est alors **ecrase**, jamais reutilise (fail-closed).
# --------------------------------------------------------------------------


def build_cache_root(explicit: Path | None = None) -> Path:
    """Repertoire du cache de build. Hors du depot, par defaut.

    Il est place a cote du depot (meme volume que les worktrees) : le
    deplacement du cache est alors un renommage, pas une copie.
    """
    if explicit is not None:
        return explicit
    return REPO_ROOT.parent / DEFAULT_CACHE_DIRNAME


def build_cache_dir(root: Path, pr: int, lake: str) -> Path:
    """Repertoire du cache pour le couple (PR, lake)."""
    return root / ("pr-%d" % pr) / lake


def _cache_fingerprint(lake_dir: Path) -> dict:
    """Empreinte du contexte de build : toolchain + manifeste du lake."""
    toolchain = _toolchain_of(lake_dir) or ""
    manifest = _read_if_present(lake_dir / "lake-manifest.json") or ""
    return {
        "toolchain": toolchain,
        "manifest_sha256": hashlib.sha256(manifest.encode("utf-8")).hexdigest(),
    }


def restore_project_build(cache_dir: Path, lake_dir: Path) -> dict:
    """Remet le `.lake/build` du cache dans le worktree -- si le cache vaut."""
    build = cache_dir / "build"
    if not build.is_dir():
        return {"restored": False, "reason": "aucun cache de build conserve"}
    try:
        meta = json.loads((cache_dir / "meta.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        meta = {}
    if meta != _cache_fingerprint(lake_dir):
        shutil.rmtree(cache_dir, ignore_errors=True)
        return {
            "restored": False,
            "reason": "cache ecrase (toolchain ou manifeste different du build)",
        }
    target = lake_dir / ".lake" / "build"
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        shutil.rmtree(target, ignore_errors=True)
    shutil.move(str(build), str(target))
    return {"restored": True, "reason": "cache de build du projet restaure"}


def seed_project_build_from_pivot(pivot_dir: Path, lake_dir: Path) -> dict:
    """Reseme le `.lake/build` du lac depuis le pivot prechauffe (#27516).

    Le pivot est deja valide par `prepare_lake` (meme toolchain, meme graphe
    de dependances) : ses oleans des modules du projet sont le point d'appui
    que la CI tire de son cache Actions. Sans ce semis, la premiere
    attestation d'une PR repart de zero sur les modules herites de `main` --
    dont `Knots.AlexanderTrivial_en` (olean de 95,7 Mo, elaboration au-dela
    du budget local, mesure #27516) -- et se fait tuer au minuteur.

    COPIE, jamais deplacement ni jonction : le pivot garde son build pour
    les PRs suivantes, et `preserve_project_build` (qui DEPLACE le
    `.lake/build` du worktree vers le cache par-PR) n'arrache jamais rien au
    pivot. Les traces Lake font le reste : seuls les modules dont la source
    differe a la tete de la PR sont re-elabores.
    """
    source = pivot_dir / ".lake" / "build"
    if not source.is_dir():
        return {"seeded": False, "reason": "aucun build de projet dans le pivot"}
    target = lake_dir / ".lake" / "build"
    if target.exists():
        return {"seeded": False, "reason": "build deja present dans le worktree"}
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(source, target)
    return {"seeded": True, "reason": "build du projet reseme depuis le pivot"}


def preserve_project_build(cache_dir: Path, lake_dir: Path) -> dict:
    """Conserve le `.lake/build` du worktree dans le cache du projet.

    Appele meme sur un build en echec : c'est precisement le cas qu'un
    timeout rend cher (une heure de compilation jetee pour rien).
    """
    build = lake_dir / ".lake" / "build"
    if not build.is_dir():
        return {"preserved": False, "reason": "aucun build a conserver"}
    cache_dir.mkdir(parents=True, exist_ok=True)
    meta = _cache_fingerprint(lake_dir)
    (cache_dir / "meta.json").write_text(
        json.dumps(meta, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    target = cache_dir / "build"
    if target.exists():
        shutil.rmtree(target, ignore_errors=True)
    shutil.move(str(build), str(target))
    return {"preserved": True, "reason": "cache de build du projet conserve"}


def build_lake(lake: dict, worktree: Path, cache_root: Path, timeout: float,
               jobs: int = DEFAULT_BUILD_JOBS,
               budget: int = DEFAULT_BUILD_BUDGET,
               targets: list[str] | None = None,
               project_cache_dir: Path | None = None) -> dict:
    """Prepare + build d'un lake dans le worktree. Ne leve pas : le verdict
    est rendu dans le resultat.

    `targets` limite la construction aux modules nommes (#26699) ; `None`
    construit le lac entier.

    `project_cache_dir` est le repertoire du cache de build du PROJET pour ce
    lake : le `.lake/build` est **remis** dans le worktree avant le build et
    **reconserve** apres -- un timeout ne jette plus la compilation deja
    faite. Quand ce cache par-PR n'a rien restaure (premier essai de la
    PR), le `.lake/build` du pivot `cache_root` -- deja valide par
    `prepare_lake` -- est **reseme par copie** : meme point d'appui que le
    cache Lake d'Actions en CI (#27516).
    """
    lake_dir = worktree / lake["project-path"]
    if not lake_dir.is_dir():
        return {"lake": lake["lake"], "ok": False, "reason": "lake absent du worktree"}
    prepared = prepare_lake(lake_dir, cache_root)
    if not prepared["ok"]:
        return {"lake": lake["lake"], "ok": False, "reason": prepared["reason"]}
    result = {"lake": lake["lake"], "ok": False, "targets": list(targets or [])}
    cache_state: dict = {"restored": False, "preserved": False}
    if project_cache_dir is not None:
        cache_state.update(restore_project_build(project_cache_dir, lake_dir))
    if not cache_state.get("restored"):
        # #27516 : premier essai de la PR (cache par-PR vide ou ecrase). Le
        # pivot -- cache_root, deja valide par prepare_lake (meme toolchain,
        # meme graphe de dependances) -- fournit le point d'appui que la CI
        # tire de son cache Actions. Sans lui, chaque premiere attestation
        # re-elabore les modules herites de main et se fait tuer au minuteur.
        cache_state.update(seed_project_build_from_pivot(cache_root, lake_dir))
    try:
        payload = run_lake_build(lake_dir, timeout, jobs=jobs, budget=budget, targets=targets)
    finally:
        if prepared.get("junction"):
            try:
                _remove_junction(lake_dir / ".lake" / "packages")
            except OrganError:
                pass
        if project_cache_dir is not None:
            cache_state.update(preserve_project_build(project_cache_dir, lake_dir))
    result["cache"] = cache_state
    result.update(
        {
            "exit_code": payload.get("exit_code"),
            "status": payload.get("status"),
            "jobs": payload.get("jobs"),
            "duration_s": payload.get("duration_s"),
            "orphans": payload.get("orphans") or [],
            "stdout_tail": payload.get("stdout_tail", "")[-2000:],
            "stderr_tail": payload.get("stderr_tail", "")[-2000:],
            # Les erreurs nommees du build (3a du dispatch) : elles voyagent
            # avec le verdict du lake, pas seulement avec la queue.
            "errors": payload.get("errors") or [],
            # La violation de budget est la **cause** d'un echec que
            # `lean_exec` presente comme un `timeout` : la propager, sinon le
            # diagnostic se perd et l'echec se lit comme un probleme de
            # temps (#26480, dispatch coordinateur du 14/11).
            "budget_violation": payload.get("budget_violation"),
            "granted_jobs": payload.get("granted_jobs"),
            "budget": payload.get("budget"),
        }
    )
    result["ok"] = payload.get("exit_code") == 0
    violation = payload.get("budget_violation")
    if violation:
        result["reason"] = build_failure_reason(payload, violation)
    elif not result["ok"]:
        result["reason"] = build_failure_reason(payload)
    return result


def post_attestation(repo: str, pr: int, body: str) -> str:
    """Poste le commentaire d'attestation. Retourne son identifiant.

    Le corps part par `--input -` (JSON `{"body": ...}`) et non par
    `-f body=@fichier` : avec `-f`, GitHub recoit le litteral `@...`
    (cf. `gh-posting-hygiene`). Le corps passe par stdin, jamais par une
    chaine shell : un backtick y serait interprete.
    """
    payload = json.dumps({"body": body}, ensure_ascii=False)
    proc = subprocess.run(
        [
            "gh",
            "api",
            "repos/{}/issues/{}/comments".format(repo, pr),
            "--method",
            "POST",
            "--input",
            "-",
        ],
        input=payload,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120.0,
    )
    if proc.returncode != 0:
        raise OrganError(
            "posting de l'attestation a echoue (rc={}) : {}".format(
                proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
            )
        )
    try:
        data = json.loads(proc.stdout or "{}")
    except json.JSONDecodeError:
        data = {}
    return str((data or {}).get("id") or "")


def cleanup_worktree(worktree: Path) -> None:
    """Retire le worktree **sans** `--force` : un worktree sale est un
    signal, jamais une raison de forcer."""
    proc = _run(["git", "-C", str(REPO_ROOT), "worktree", "remove", str(worktree)])
    if proc.returncode != 0:
        proc = _run(
            ["git", "-C", str(REPO_ROOT), "worktree", "remove", str(worktree)]
        )
        if proc.returncode != 0:
            raise OrganError(
                "git worktree remove a echoue (rc={}) : {}".format(
                    proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
                )
            )


def _attestation_extra(
    builds: list[dict], modules_mode: str, pure_timeouts: list[dict] | None = None
) -> str:
    """La partie libre du corps d'attestation : ce qui a ete CONSTRUIT.

    Un build cible n'atteste que ce qu'il a construit : les cibles sont donc
    nommees, et les agregateurs ecartes aussi (une borne invisible est une
    attestation quiSUR-declare sa portee).

    Quand un ou plusieurs builds sont des **timeouts purs** (#27516 volet 3),
    le texte est honnete : le build local n'a PAS acheve (budget de temps),
    ce n'est ni un echec de compilation ni une preuve de vert local ;
    l'autorite de compilation est la CI (cache chaud). Le texte ne dit plus
    alors « reussi ».
    """
    timed_lakes = {b.get("lake") for b in (pure_timeouts or [])}
    if timed_lakes:
        lines = [
            "`lake build` local **non acheve** sur le worktree detache a la "
            "tete citee : timeout du budget local pour {} -- ce n'est ni un "
            "echec de compilation ni une preuve de vert local. L'autorite de "
            "compilation est la CI (cache Lake chaud), qui compile le meme lac "
            "(#27516).".format(
                ", ".join("`{}`".format(l) for l in sorted(timed_lakes))
            )
        ]
    else:
        lines = [
            "`lake build` local reussi sur le worktree detache a la tete citee "
            "(cache Mathlib chaud par jonction). "
            "Preuve : sortie de `scripts/lean/lean_exec.py`."
        ]
    for build in builds:
        lake = build.get("lake")
        if lake in timed_lakes:
            lines.append(
                "Lake `{}` : **timeout du budget local** (exit 124) -- "
                "deferral CI.".format(lake)
            )
            continue
        targets = build.get("targets") or []
        scope = build.get("scope") or {}
        if not targets:
            lines.append(
                "Lake `{}` : **lac entier** (mode `{}`, aucune cible resolue).".format(
                    lake, modules_mode
                )
            )
            continue
        lines.append(
            "Lake `{}` : **build cible**, {} module(s) : {}.".format(
                lake, len(targets), ", ".join("`{}`".format(t) for t in targets)
            )
        )
        dependents = scope.get("dependents") or []
        if dependents:
            lines.append(
                "Dependants inclus : {}.".format(
                    ", ".join("`{}`".format(d) for d in dependents)
                )
            )
        skipped = scope.get("skipped_aggregators") or []
        if skipped:
            lines.append(
                "Agregateurs ecartes (imports seuls, sans commande) : {}.".format(
                    ", ".join("`{}`".format(s) for s in skipped)
                )
            )
    return "\n".join(lines)


def _worktree_path(pr: int) -> Path:
    """Chemin DETERMINISTE du worktree d'attestation, par PR.

    Le determinisme n'est pas un caprice : les traces de `lake` sont
    attachees aux chemins absolus des sources. Reconstruire le worktree
    ailleurs invaliderait le cache de build conserve, et l'on retomberait
    dans le piege que #26699 veut lever (une compilation jetee a chaque
    essai).
    """
    return REPO_ROOT.parent / ("attest-lean-wt-pr-%d" % pr)


def _clear_stale_worktree(worktree: Path) -> None:
    """Retire un worktree d'un essai precedent, s'il en reste un.

    Le retrait se fait **sans** `--force` : un worktree sale est un signal.
    Si le retrait refuse (worktree enregistre mais absent du disque,
    parasite), `git worktree prune` nettoie l'enregistrement ; le reste du
    chemin n'est touche que s'il porte la marque d'un worktree (`.git`).
    """
    if not worktree.exists():
        return
    proc = _run(["git", "-C", str(REPO_ROOT), "worktree", "remove", str(worktree)])
    if proc.returncode != 0:
        _run(["git", "-C", str(REPO_ROOT), "worktree", "prune"])
    if worktree.exists():
        if not (worktree / ".git").is_file():
            raise OrganError(
                "chemin de worktree occupe par autre chose : {}".format(worktree)
            )
        shutil.rmtree(worktree, ignore_errors=True)


def attest(pr: int, repo: str, timeout: float | None, dry_run: bool,
            jobs: int = DEFAULT_BUILD_JOBS,
            budget: int = DEFAULT_BUILD_BUDGET,
            modules_mode: str = MODULES_AUTO,
            cache_root: Path | None = None) -> dict:
    """Certifie la PR : worktree, builds bornes, attestation postee sur
    SUCCESS."""
    started = time.time()
    login = current_login()
    if login != attestation.ATTESTATION_AUTHOR:
        raise OrganError(
            "l'attestation n'est valable que sous {} (login courant : {})".format(
                attestation.ATTESTATION_AUTHOR, login
            )
        )
    # Couple (jobs, budget) aligne AVANT toute construction : le budget
    # reserve doit couvrir le parallelisme accorde et le scheduler `lake`
    # (#26480). Un couple incoherent est refuse, pas corrige en silence.
    incoherence = raison_alignement_budget(jobs, budget)
    if incoherence:
        raise OrganError(
            "couple (jobs={}, budget={}) incoherent : {}".format(
                jobs, budget, incoherence
            )
        )
    head = pr_head(repo, pr)
    files = pr_files(repo, pr)
    # Le manifeste de BASE est celui du clone (main) ; le manifeste de la PR
    # est celui de sa TETE : c'est lui qui declare les lakes ajoutes (#26630).
    base_manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    head_manifest = manifest_at_head(repo, head)
    manifest_source = "tete"
    if head_manifest is None:
        head_manifest = base_manifest
        manifest_source = "clone"
    lakes = select_lakes(files, head_manifest, base_manifest)
    result = {
        "pr": pr,
        "repo": repo,
        "head": head,
        "files": len(files),
        "manifest_source": manifest_source,
        "lakes": [lake["lake"] for lake in lakes],
        "posted": False,
        "comment_id": "",
        "jobs": jobs,
        "budget": budget,
        "modules_mode": modules_mode,
        # Le budget de temps applique a CHAQUE lake : le verdict doit dire
        # quel temps a ete accorde, pas seulement que le build a echoue.
        "lake_timeouts": {
            lake["lake"]: lake_timeout(lake, timeout) for lake in lakes
        },
    }
    if not lakes:
        # #27875 : le cas frequent est un lake INTRODUIT par la PR et non
        # declare au manifeste (l'entree arrive dans une PR empilee). Le
        # message nomme le lake et le geste : sans cela, le blocage rendu
        # par la garde est muet.
        undeclared = attestation.undeclared_lakes(files, head_manifest)
        if undeclared:
            raise OrganError(
                "le diff de #{} INTRODUIT le lake {} mais le manifeste "
                "`scripts/lean/ci_lakes.json` ne le declare pas a la tete : "
                "declarez-le (dans cette PR, ou dans une PR empilee mergee "
                "d'abord), puis relancez l'attestation -- aucune attestation "
                "ne peut couvrir un lake non declare.".format(
                    pr, ", ".join(undeclared)
                )
            )
        raise OrganError(
            "aucun lake connu n'est touche par le diff de #{} -- rien a "
            "construire ; la garde Lean attend une attestation, qui ne peut "
            "pas etre produite tant qu'aucun lake declare ne porte le "
            "diff".format(pr)
        )
    if dry_run:
        result["dry_run"] = True
        # Les CIBLES du build (#26699) : le dry-run les rend SANS rien
        # construire. C'est le moyen de verifier la portee avant de lancer
        # une heure de compilation, et de nommer ce qui ne sera pas construit.
        result["scope"] = []
        for lake in lakes:
            lake_dir = REPO_ROOT / lake["project-path"]
            scope = attest_build_targets.resolve_targets(
                lake_dir,
                files,
                lake_prefix=str(lake["project-path"]).replace("\\", "/").rstrip("/") + "/",
            )
            entry = {"lake": lake["lake"]}
            entry.update(scope)
            result["scope"].append(entry)
        # Le dry-run rend le verdict de cache SANS construire ni modifier
        # quoi que ce soit : c'est ce qui prouve, avant meme le build, que
        # le cache chaud s'applique a ce lake (ou nomme le paquet fautif).
        # Il lit les lakes du CHECKPOINT COURANT (le cache chaud est un
        # etat de la machine, pas de la PR) ; le MANIFESTE, lui, est celui
        # de la tete de la PR (#26630).
        result["cache_check"] = []
        candidates = _pivot_candidates(base_manifest, head_manifest)
        for lake in lakes:
            lake_dir = REPO_ROOT / lake["project-path"]
            pivot = resolve_cache_pivot(lake_dir, candidates)
            if not pivot.get("ok"):
                reason = pivot.get("reason", "")
                entry = {
                    "lake": lake["lake"],
                    "ok": False,
                    "reason": reason,
                    "checks": [],
                }
                if reason == NO_WARM_CACHE:
                    entry["toolchain"] = pivot.get("toolchain", "")
                    entry["prewarm"] = prewarm_plan(
                        lake, head=head, timeout=lake_timeout(lake, timeout)
                    )
                elif not lake_dir.is_dir() and "lean-toolchain absent" in reason:
                    # Lake AJOUTE par la PR : il n'existe pas dans le clone
                    # courant. Le verdict de cache ne peut pas etre rendu
                    # ici -- il le sera sur le worktree de la tete, ou le
                    # lake existe. On le dit distinctement, avec la commande
                    # de prechauffage (#26630).
                    entry["reason"] = LAKE_NOT_IN_CLONE
                    entry["toolchain"] = _toolchain_at_head(
                        repo, head, lake.get("project-path") or ""
                    )
                    entry["detail"] = (
                        "le lake est declare par la PR et n'existe pas dans le "
                        "clone courant : le verdict de cache se rendra sur le "
                        "worktree de la tete"
                    )
                    entry["prewarm"] = prewarm_plan(
                        lake, head=head, timeout=lake_timeout(lake, timeout)
                    )
                result["cache_check"].append(entry)
                continue
            verdict = check_cache_compatibility(lake_dir, Path(pivot["pivot"]))
            result["cache_check"].append(
                {
                    "lake": lake["lake"],
                    "ok": bool(verdict.get("ok")),
                    "reason": verdict.get("reason", ""),
                    "checks": verdict.get("checks", []),
                    "pivot": pivot["pivot"],
                    "toolchain": pivot.get("toolchain", ""),
                }
            )
        # Le verdict est explicite : `ok` et `reason` sont TOUJOURS poses.
        # Sans eux, `main()` ne pouvait qu'afficher « raison inconnue » et
        # rendre rc=1 -- un dry-run reussi se lisait comme un echec
        # (dispatch coordinateur du 14/11).
        mauvais = [c for c in result["cache_check"] if not c["ok"]]
        if mauvais:
            result["ok"] = False
            sans_cache = [
                c for c in mauvais
                if c.get("reason") in (NO_WARM_CACHE, LAKE_NOT_IN_CLONE)
            ]
            if sans_cache:
                # Motif DISTINCT : la toolchain du lake n'a aucun cache chaud.
                # L'organe ne conclut pas, il donne la commande de
                # prechauffage (#26630).
                result["reason"] = "cache chaud indisponible pour la toolchain : {}".format(
                    ", ".join(
                        "{} ({})".format(c["lake"], c.get("toolchain") or "?")
                        for c in sans_cache
                    )
                )
                result["prewarm"] = [c["prewarm"] for c in sans_cache if c.get("prewarm")]
            else:
                result["reason"] = "cache chaud non applicable : {}".format(
                    ", ".join(
                        "{} ({})".format(c["lake"], c["reason"] or "raison non nommee")
                        for c in mauvais
                    )
                )
        else:
            result["ok"] = True
            result["reason"] = "cache chaud applicable : {}".format(
                ", ".join(c["lake"] for c in result["cache_check"])
            )
        return result

    worktree = _worktree_path(pr)
    _clear_stale_worktree(worktree)
    created = False
    try:
        proc = _run(
            [
                "git",
                "-C",
                str(REPO_ROOT),
                "worktree",
                "add",
                "--detach",
                str(worktree),
                head,
            ],
            timeout=600.0,
        )
        if proc.returncode != 0:
            raise OrganError(
                "git worktree add a echoue (rc={}) : {}".format(
                    proc.returncode, (proc.stderr or proc.stdout or "").strip()[:200]
                )
            )
        created = True
        builds = []
        candidates = _pivot_candidates(base_manifest, head_manifest)
        cache_root_dir = build_cache_root(cache_root)
        for lake in lakes:
            lake_dir = worktree / lake["project-path"]
            pivot = resolve_cache_pivot(lake_dir, candidates)
            if not pivot.get("ok"):
                entry = {
                    "lake": lake["lake"],
                    "ok": False,
                    "reason": pivot.get("reason", ""),
                    "errors": [],
                }
                if pivot.get("reason") == NO_WARM_CACHE:
                    entry["toolchain"] = pivot.get("toolchain", "")
                    entry["prewarm"] = prewarm_plan(
                        lake, head=head, timeout=lake_timeout(lake, timeout)
                    )
                builds.append(entry)
                continue
            # Les cibles du build (#26699) : les modules touches, leurs
            # jumeaux `_en` et leurs dependants dans le lake. La resolution
            # se fait sur le lake de la TETE (le worktree), pas sur celui du
            # clone : c'est la tete qui est attestee.
            targets: list[str] | None = None
            scope = {}
            if modules_mode == MODULES_AUTO:
                scope = attest_build_targets.resolve_targets(
                    lake_dir,
                    files,
                    lake_prefix=str(lake["project-path"]).replace("\\", "/").rstrip("/") + "/",
                )
                if scope.get("ok"):
                    targets = list(scope.get("targets") or [])
                else:
                    # Repli explicite : le lac entier. La raison est rendue
                    # dans le verdict -- jamais un build restreint en silence.
                    targets = None
                    scope = {"ok": False, "reason": scope.get("reason", "")}
            builds.append(
                build_lake(
                    lake,
                    worktree,
                    Path(pivot["pivot"]),
                    lake_timeout(lake, timeout),
                    jobs=jobs,
                    budget=budget,
                    targets=targets,
                    project_cache_dir=build_cache_dir(
                        cache_root_dir, pr, lake["lake"]
                    ),
                )
            )
            builds[-1]["scope"] = scope
        result["builds"] = builds
        # Les erreurs nommees de tous les builds : le diagnostic du build
        # qui a echoue, hors de la queue de 4000 caracteres.
        result["errors"] = [e for b in builds for e in (b.get("errors") or [])]
        failed = [b for b in builds if not b.get("ok")]
        # #27516 volet 3 : un timeout pur (tue au minuteur, sans violation du
        # budget de concurrence ni erreur de compilation) n'est PAS un echec
        # de build : la CI compile le meme lac en vert (cache chaud). Il ne
        # refuse pas la PR ; il est atteste comme deferral CI. Seuls les
        # echecs qui ne sont PAS des timeouts purs bloquent le merge.
        pure_timeouts = [b for b in failed if is_pure_timeout(b)]
        blocking = [b for b in failed if not is_pure_timeout(b)]
        if blocking:
            result["ok"] = False
            failed = blocking
            sans_cache = [
                b for b in failed
                if b.get("reason") in (NO_WARM_CACHE, LAKE_NOT_IN_CLONE)
            ]
            if sans_cache:
                # Ce n'est pas un echec de build : la toolchain du lake n'a
                # aucun cache chaud. L'organe ne conclut pas, il nomme la
                # commande de prechauffage (#26630).
                result["reason"] = "cache chaud indisponible pour la toolchain : {}".format(
                    ", ".join(
                        "{} ({})".format(b.get("lake"), b.get("toolchain") or "?")
                        for b in sans_cache
                    )
                )
                result["prewarm"] = [b["prewarm"] for b in sans_cache if b.get("prewarm")]
                return result
            violations = [
                "{} : {}".format(b.get("lake"), b.get("budget_violation"))
                for b in failed
                if b.get("budget_violation")
            ]
            if violations:
                # La cause est un depassement de concurrence, pas un
                # depassement de temps : le nommer evite qu'un diagnostic
                # conclue « lent » (#26480).
                result["reason"] = "violation du budget de concurrence : {}".format(
                    " ; ".join(violations)
                )
            else:
                # La raison nomme la PREMIERE erreur : « le build a echoue »
                # sans elle ne dit pas quoi corriger.
                first = (result["errors"] or [{}])[0].get("text", "")
                result["reason"] = "build en echec : {}{}".format(
                    ", ".join(str(b.get("lake")) for b in failed),
                    " -- {}".format(first[:160]) if first else "",
                )
            return result
        jobs = 0
        for build in builds:
            try:
                jobs += int(build.get("jobs") or 0)
            except (TypeError, ValueError):
                pass
        # Aucun echec bloquant : attestation. Les timeouts purs (le cas
        # knot_lean, #27516) y sont marques `timeout: defer` -- l'attestation
        # est honnete (build local non acheve) mais ne bloque pas la PR : la
        # garde merge_ready la lit par la tete, comme toute attestation.
        body = attestation.render_attestation(
            sha=head,
            lakes=[lake["lake"] for lake in lakes],
            jobs=jobs or None,
            pr=pr,
            duration_s=time.time() - started,
            extra=_attestation_extra(builds, modules_mode, pure_timeouts),
            timeout=bool(pure_timeouts),
        )
        comment_id = post_attestation(repo, pr, body)
        result["ok"] = True
        result["posted"] = True
        result["comment_id"] = comment_id
        result["jobs"] = jobs
    finally:
        if created:
            # Nettoyage : jonction(s) deja retirees par build_lake ; `.lake`
            # puis worktree, dans cet ordre.
            shutil.rmtree(worktree / ".lake", ignore_errors=True)
            for lake in lakes:
                lake_dir = worktree / lake["project-path"]
                if lake_dir.is_dir():
                    # La jonction `.lake/packages` est retiree ICI aussi :
                    # un `shutil.rmtree` sur un repertoire qui contient une
                    # jonction peut detruire la CIBLE (le cache Mathlib
                    # partage). Le retrait se fait par `rmdir`, qui ne
                    # touche que le lien.
                    packages = lake_dir / ".lake" / "packages"
                    if _is_junction(packages):
                        try:
                            _remove_junction(packages)
                        except OrganError:
                            pass
                    shutil.rmtree(lake_dir / ".lake", ignore_errors=True)
            try:
                cleanup_worktree(worktree)
            except OrganError as exc:
                result["cleanup_error"] = str(exc)
    result["duration_s"] = round(time.time() - started, 2)
    return result


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("pr", type=int, help="numero de la PR")
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument(
        "--timeout",
        type=float,
        default=None,
        help=(
            "timeout du lake build, en secondes (defaut : {} ; conway : {}) "
            "-- une valeur explicite prime sur le budget propre du lake".format(
                int(DEFAULT_LAKE_TIMEOUT),
                int(LAKE_TIMEOUTS.get("conway", DEFAULT_LAKE_TIMEOUT)),
            )
        ),
    )
    ap.add_argument("--dry-run", action="store_true", help="ne construit rien")
    ap.add_argument(
        "--jobs",
        type=int,
        default=DEFAULT_BUILD_JOBS,
        help="parallélisme accordé à lake build (compilations concurrentes)",
    )
    ap.add_argument(
        "--budget",
        type=int,
        default=DEFAULT_BUILD_BUDGET,
        help="places réservées dans le cap machine-wide (jobs + scheduler lake)",
    )
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    ap.add_argument(
        "--modules",
        choices=[MODULES_AUTO, MODULES_ALL],
        default=MODULES_AUTO,
        help=(
            "portee du build : `auto` construit les modules touches, leurs "
            "jumeaux `_en` et leurs dependants dans le lac ; `all` construit "
            "le lac entier"
        ),
    )
    ap.add_argument(
        "--cache-root",
        default=None,
        help=(
            "repertoire du cache de build du projet (defaut : a cote du "
            "depot). Le cache est conserve entre deux essais."
        ),
    )
    args = ap.parse_args(argv)

    try:
        result = attest(
            args.pr,
            args.repo,
            args.timeout,
            args.dry_run,
            jobs=args.jobs,
            budget=args.budget,
            modules_mode=args.modules,
            cache_root=Path(args.cache_root) if args.cache_root else None,
        )
    except OrganError as exc:
        payload = {"pr": args.pr, "ok": False, "posted": False, "reason": str(exc)}
        if args.json:
            json.dump(payload, sys.stdout, ensure_ascii=False)
            sys.stdout.write("\n")
        else:
            print("[ATTEST] refus : {}".format(exc))
        return 2
    if args.json:
        json.dump(result, sys.stdout, ensure_ascii=False, indent=1)
        sys.stdout.write("\n")
    else:
        if result.get("dry_run"):
            print(
                "[ATTEST] #{} dry-run (rien n'a ete construit) : {}".format(
                    result["pr"], result.get("reason", "verdict non rendu")
                )
            )
        elif result.get("posted"):
            print(
                "[ATTEST] #{} atteste (tete {}) -- lakes {} -- jobs {}".format(
                    result["pr"],
                    result["head"][:12],
                    ", ".join(result.get("lakes") or []),
                    result.get("jobs"),
                )
            )
        else:
            print(
                "[ATTEST] #{} non atteste : {}".format(
                    result["pr"], result.get("reason", "raison inconnue")
                )
            )
        # La commande de prechauffage est PARTIE du verdict : un motif
        # « pas de cache chaud » sans la commande qui le remedie laisse
        # l'interlocuteur sans geste (#26630).
        for plan in result.get("prewarm") or []:
            print("[ATTEST] prechauffage : {}".format(plan.get("note", "")))
            for cle in ("worktree", "cache_get", "build"):
                argv = plan.get(cle) or []
                if argv:
                    print("  {} : {}".format(cle, " ".join(str(a) for a in argv)))
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
