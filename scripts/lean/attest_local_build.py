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

Sortie : JSON sur stdout avec le verdict, les lakes, la duree, le SHA atteste
et l'identifiant du commentaire poste (vide si rien n'a ete poste).
"""

from __future__ import annotations

import argparse
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

DEFAULT_REPO = "jsboige/CoursIA"
MANIFEST_PATH = LEAN_DIR / "ci_lakes.json"
LEAN_EXEC = LEAN_DIR / "lean_exec.py"

#: Cache chaud de reference : le lake-pivot qui porte le checkout Mathlib
#: partage par junction (cf `docs/lean/coordinator-workflow.md`).
CACHE_PIVOT = (
    REPO_ROOT
    / "MyIA.AI.Notebooks"
    / "SymbolicAI"
    / "Lean"
    / "GOL"
    / "conway_lean"
)

#: Timeout du build, en secondes. Deux modules a cache chaud prennent ~90 s
#: (mesure du coordinateur) ; le budget laisse une marge large sans devenir
#: une attente non bornee.
DEFAULT_TIMEOUT = 1800.0

#: Timeout du `lake build` par lake.
DEFAULT_LAKE_TIMEOUT = 900.0

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
                   budget: int = DEFAULT_BUILD_BUDGET) -> dict:
    """`lake build` borne via `lean_exec.py` (l'organe de build existant).

    Le payload `lake build` est un **PAYLOAD** : il est passe a l'organe
    canonique, qui le lance sous le budget commun. Ce fichier ne lance
    aucun processus lake lui-meme.

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
            ["lake", "build"],
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


def build_lake(lake: dict, worktree: Path, cache_root: Path, timeout: float,
               jobs: int = DEFAULT_BUILD_JOBS,
               budget: int = DEFAULT_BUILD_BUDGET) -> dict:
    """Prepare + build d'un lake dans le worktree. Ne leve pas : le verdict
    est rendu dans le resultat."""
    lake_dir = worktree / lake["project-path"]
    if not lake_dir.is_dir():
        return {"lake": lake["lake"], "ok": False, "reason": "lake absent du worktree"}
    prepared = prepare_lake(lake_dir, cache_root)
    if not prepared["ok"]:
        return {"lake": lake["lake"], "ok": False, "reason": prepared["reason"]}
    result = {"lake": lake["lake"], "ok": False}
    try:
        payload = run_lake_build(lake_dir, timeout, jobs=jobs, budget=budget)
    finally:
        if prepared.get("junction"):
            try:
                _remove_junction(lake_dir / ".lake" / "packages")
            except OrganError:
                pass
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
        result["reason"] = "violation du budget de concurrence : {}".format(violation)
    elif not result["ok"]:
        result["reason"] = "lake build a echoue (exit_code={})".format(
            payload.get("exit_code")
        )
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


def attest(pr: int, repo: str, timeout: float, dry_run: bool,
            jobs: int = DEFAULT_BUILD_JOBS,
            budget: int = DEFAULT_BUILD_BUDGET) -> dict:
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
    lakes = lakes_for(files)
    result = {
        "pr": pr,
        "repo": repo,
        "head": head,
        "files": len(files),
        "lakes": [lake["lake"] for lake in lakes],
        "posted": False,
        "comment_id": "",
        "jobs": jobs,
        "budget": budget,
    }
    if not lakes:
        raise OrganError(
            "aucun lake connu n'est touche par le diff de #{} -- rien a "
            "construire (la garde ne bloquera pas cette PR)".format(pr)
        )
    if dry_run:
        result["dry_run"] = True
        # Le dry-run rend le verdict de cache SANS construire ni modifier
        # quoi que ce soit : c'est ce qui prouve, avant meme le build, que
        # le cache chaud s'applique a ce lake (ou nomme le paquet fautif).
        # Il lit les lakes du CHECKPOINT COURANT, pas de la tete de la PR :
        # un diff `.lean` ne change ni la toolchain ni le manifeste.
        result["cache_check"] = []
        for lake in lakes:
            verdict = check_cache_compatibility(
                REPO_ROOT / lake["project-path"], CACHE_PIVOT
            )
            result["cache_check"].append(
                {
                    "lake": lake["lake"],
                    "ok": bool(verdict.get("ok")),
                    "reason": verdict.get("reason", ""),
                    "checks": verdict.get("checks", []),
                }
            )
        # Le verdict est explicite : `ok` et `reason` sont TOUJOURS poses.
        # Sans eux, `main()` ne pouvait qu'afficher « raison inconnue » et
        # rendre rc=1 -- un dry-run reussi se lisait comme un echec
        # (dispatch coordinateur du 14/11).
        mauvais = [c for c in result["cache_check"] if not c["ok"]]
        if mauvais:
            result["ok"] = False
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

    worktree = Path(
        tempfile.mkdtemp(prefix="attest-lean-wt-", dir=str(REPO_ROOT.parent))
    )
    worktree.rmdir()
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
        for lake in lakes:
            builds.append(
                build_lake(lake, worktree, CACHE_PIVOT, timeout, jobs=jobs, budget=budget)
            )
        result["builds"] = builds
        # Les erreurs nommees de tous les builds : le diagnostic du build
        # qui a echoue, hors de la queue de 4000 caracteres.
        result["errors"] = [e for b in builds for e in (b.get("errors") or [])]
        failed = [b for b in builds if not b.get("ok")]
        if failed:
            result["ok"] = False
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
        body = attestation.render_attestation(
            sha=head,
            lakes=[lake["lake"] for lake in lakes],
            jobs=jobs or None,
            pr=pr,
            duration_s=time.time() - started,
            extra=(
                "`lake build` local reussi sur le worktree detache a la tete "
                "citee (cache Mathlib chaud par jonction). "
                "Preuve : sortie de `scripts/lean/lean_exec.py`."
            ),
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
        default=DEFAULT_LAKE_TIMEOUT,
        help="timeout du lake build, en secondes",
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
    args = ap.parse_args(argv)

    try:
        result = attest(
            args.pr,
            args.repo,
            args.timeout,
            args.dry_run,
            jobs=args.jobs,
            budget=args.budget,
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
    return 0 if result.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
