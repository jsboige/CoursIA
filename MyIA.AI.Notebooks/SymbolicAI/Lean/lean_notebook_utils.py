"""
lean_notebook_utils - Cross-platform utilities for Lean 4 notebook execution

Provides a unified interface for running Lean 4 code from Jupyter notebooks
on Windows (via WSL), Linux, and macOS (native lake/lean via elan).

Usage:
    from lean_notebook_utils import (
        find_lean_project, get_lean_project_path,
        run_lake, run_lean_snippet, count_sorry,
        display_lean_module, read_lean_module,
        is_native_platform
    )

    # Find and build a Lean project
    project_path = get_lean_project_path("grothendieck_lean")
    rc, out, err = run_lake(project_path, "build Grothendieck", timeout=1500)

    # Run a Lean snippet
    result = run_lean_snippet(project_path, "#eval 2 + 2")

    # Count sorry in .lean files
    n = count_sorry(project_path, "Grothendieck/")

Epic #2314, Issue #2315.
"""

import json
import subprocess
import tempfile
import platform
import shutil
import os
import re
import sys
import textwrap
from pathlib import Path
from typing import Optional, Tuple


# ---------------------------------------------------------------------------
# Input validation (degenerate-input guards, c.703 pattern)
# ---------------------------------------------------------------------------

def _require_str(name, value):
    """Reject None / non-str at the boundary with a clear, actionable error.

    Without this guard, ``str.split`` / ``Path / value`` / ``os.path.join``
    crash deeper with an opaque ``TypeError`` or ``AttributeError`` that points
    at an implementation line rather than the caller's bad argument.
    """
    if not isinstance(value, str):
        raise TypeError(
            f"{name} must be a non-empty string, got "
            f"{type(value).__name__}: {value!r}"
        )
    if not value.strip():
        raise ValueError(f"{name} must be a non-empty string, got {value!r}")
    return value


# ---------------------------------------------------------------------------
# Platform detection
# ---------------------------------------------------------------------------

def is_native_platform() -> bool:
    """True on Linux/macOS where lake/lean run natively (no WSL needed)."""
    return platform.system() in ("Linux", "Darwin")


def is_windows() -> bool:
    """True on Windows (WSL bridge required for Lean)."""
    return platform.system() == "Windows"

# NOTE migration #15666 : ``_find_lake()`` (resolution de l'executable lake
# natif) a ete RETIRE avec l'invocation directe qu'il servait — run_lake et
# run_lean_snippet passent desormais par l'organe confine lean_exec, qui
# resout le backend lui-meme (epinglage par lake, sonde de toolchain).


# ---------------------------------------------------------------------------
# Project discovery
# ---------------------------------------------------------------------------

def find_lean_project(project_name: str) -> Path:
    """Find a Lake project directory by walking parent directories.

    Searches from multiple starting points to handle both interactive use
    and Papermill execution (where CWD may differ from notebook location).

    Args:
        project_name: Directory name of the Lake project (e.g. "grothendieck_lean")

    Returns:
        Absolute Path to the project directory.

    Raises:
        FileNotFoundError: If the project cannot be found.
    """
    _require_str("project_name", project_name)
    starts = [Path.cwd().resolve()]

    # Papermill passes the notebook path as a parameter
    nb_file = os.environ.get("NB_FILE") or globals().get("__vsc_ipynb_file__")
    if nb_file:
        starts.append(Path(nb_file).resolve().parent)

    for start in starts:
        current = start
        for _ in range(12):
            candidate = current / project_name
            if candidate.exists() and (candidate / "lakefile.lean").exists():
                return candidate.resolve()
            current = current.parent
            if current == current.parent:
                break

    raise FileNotFoundError(
        f"{project_name}/ not found — check working directory. "
        f"Searched from: {starts}"
    )


def win_to_wsl(win_path: Path) -> str:
    """Convert a Windows path to a WSL mount path (C:\\x -> /mnt/c/x).

    On Linux/macOS, returns the path as-is (posix string).

    Args:
        win_path: A Windows Path object.

    Returns:
        WSL-compatible path string.
    """
    if not isinstance(win_path, (Path, str)):
        raise TypeError(
            f"win_path must be a Path or str, got {type(win_path).__name__}: "
            f"{win_path!r}"
        )
    p = Path(win_path).resolve()
    drive_letter = p.drive

    if not drive_letter or len(drive_letter) < 2:
        s = str(p)
        if s.startswith("/mnt/"):
            return s  # Already a WSL path
        # Fallback: try to detect from common mount points
        drive_letter = "C:"

    drive = drive_letter[0].lower()
    return f"/mnt/{drive}{p.as_posix()[2:]}"


def get_lean_project_path(project_name: str) -> str:
    """Get the appropriate path for a Lean project based on platform.

    On Windows: returns a WSL path (/mnt/c/...) for use in WSL commands.
    On Linux/macOS: returns the native absolute path.

    Args:
        project_name: Directory name of the Lake project.

    Returns:
        Path string suitable for the current platform.
    """
    win_path = find_lean_project(project_name)
    if is_native_platform():
        return str(win_path.resolve())
    return win_to_wsl(win_path)


def _run_capture(cmd, timeout, cwd=None):
    """Run ``cmd`` capturing stdout/stderr via temp files.

    Avoids ``subprocess.run(capture_output=True)`` whose per-stream
    ``_readerthread`` race on Windows can silently drop output when the process
    exits (the Lean-15/15b/Kochen-Specker C.2 defect: committed notebook outputs
    were only an ``Exception in thread (_readerthread)`` trace, with no real Lean
    output). Returns ``(returncode, stdout, stderr)``; raises
    ``subprocess.TimeoutExpired`` and ``FileNotFoundError`` like ``subprocess.run``.
    See PRs #3216 (Lean-15), #3222 (Lean-15b).
    """
    out_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.out')
    err_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.err')
    out_path, err_path = out_f.name, err_f.name
    out_f.close()
    err_f.close()
    try:
        with open(out_path, 'wb') as o, open(err_path, 'wb') as e:
            r = subprocess.run(cmd, stdout=o, stderr=e, cwd=cwd, timeout=timeout)
        out = Path(out_path).read_text(encoding='utf-8', errors='replace')
        err = Path(err_path).read_text(encoding='utf-8', errors='replace')
        return r.returncode, out, err
    finally:
        for p in (out_path, err_path):
            try:
                Path(p).unlink()
            except OSError:
                pass


# ---------------------------------------------------------------------------
# Lean command execution — migration vers l'organe confine lean_exec (#15666)
# ---------------------------------------------------------------------------
# run_lake / run_lean_snippet ne lancent PLUS lake directement : toute
# execution passe par ``scripts/lean/lean_exec.py run`` (admission
# machine-wide, budget, kill-tree, backend epingle). Les signatures restent
# inchangees — les ~10 carnets appelants et agent_tests/prover/tools.py ne
# changent pas, aucune re-execution due.

_ORGAN_CALLER = "lean_notebook_utils"

# Tete du verdict JSON de l'organe : objet ouvrant dont la premiere cle est
# run_id (ordre garanti par le dict literal de run_command).
_ORGAN_JSON_HEAD = re.compile(r'\{\s*"run_id"\s*:')

# Cache forme WSL -> forme hote (une sonde wslpath -w par projet et par
# session kernel ; les carnets appellent run_lake plusieurs fois par projet).
_HOST_CWD_CACHE: dict = {}


def _find_lean_exec() -> Path:
    """Locate l'organe canonique ``scripts/lean/lean_exec.py``.

    Marche des parents (meme strategie que ``find_lean_project``) depuis le
    cwd, le fichier notebook (papermill NB_FILE / VS Code) et le dossier du
    module : depuis un carnet de la serie Lean comme depuis les tests, la
    racine du depot est atteinte en <= 8 parents.
    """
    starts = [Path.cwd().resolve()]
    nb_file = os.environ.get("NB_FILE") or globals().get("__vsc_ipynb_file__")
    if nb_file:
        starts.append(Path(nb_file).resolve().parent)
    starts.append(Path(__file__).resolve().parent)
    for start in starts:
        current = start
        for _ in range(14):
            candidate = current / "scripts" / "lean" / "lean_exec.py"
            if candidate.exists():
                return candidate.resolve()
            current = current.parent
            if current == current.parent:
                break
    raise FileNotFoundError(
        "scripts/lean/lean_exec.py introuvable — organe d'execution confine "
        "requis par run_lake/run_lean_snippet (See #15666)"
    )


def _wsl_to_win(wsl_path: str) -> str:
    """Traduit ``/mnt/<drive>/...`` en forme Windows (``wslpath -w``).

    L'organe attend une forme HOTE pour ``--cwd`` (il re-traduit vers WSL
    via son ``wsl_path_of``) : les appelants passent la forme WSL rendue par
    ``get_lean_project_path``. Sonde bornee 10 s ; echec = valeur passee
    telle quelle (l'organe tranchera et rendra son refus nomme).
    """
    cached = _HOST_CWD_CACHE.get(wsl_path)
    if cached:
        return cached
    try:
        out = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--exec", "wslpath", "-w", wsl_path],
            capture_output=True, timeout=10,
        )
        if out.returncode == 0:
            host = out.stdout.decode("utf-8", errors="replace").strip()
            if host:
                _HOST_CWD_CACHE[wsl_path] = host
                return host
    except (OSError, subprocess.SubprocessError):
        pass
    return wsl_path


def _host_cwd_of(project_path: str) -> str:
    """Forme hote du chemin projet (passe-tout en natif, traduction WSL
    sous Windows — l'organe attend la forme hote, capacite #15666)."""
    if is_native_platform() or not str(project_path).startswith("/mnt/"):
        return project_path
    return _wsl_to_win(str(project_path))


def _split_organ_json(stdout: str) -> Tuple[Optional[dict], str]:
    """Separe le JSON final de l'organe (``run --json``) de la sortie enfant.

    ``_emit`` imprime le JSON APRES l'enfant (stdout herite) : le bloc
    cherche est le DERNIER objet parsable dont la premiere cle est
    ``run_id``. Le probe est une regex d'indentation-libre : l'organe emet
    ``indent=2`` aujourd'hui, verrouiller l'indentation dans le migrant
    casserait au premier reformatage de l'organe. Rend
    ``(payload | None, sortie_enfant)``.
    """
    for match in reversed(
            list(_ORGAN_JSON_HEAD.finditer(stdout))):
        probe = match.start()
        try:
            payload = json.loads(stdout[probe:])
        except ValueError:
            continue
        if isinstance(payload, dict) and "run_id" in payload:
            return payload, stdout[:probe]
    return None, stdout


def _organ_run(
    project_path: str, cmd_args: list, timeout: int
) -> Tuple[int, str, str]:
    """Execute ``cmd_args`` via l'organe confine depuis ``project_path``.

    La sortie de l'enfant passe par ``--stdout-file``/``--stderr-file`` :
    sous Windows, l'enfant confine (CREATE_NO_WINDOW + job) n'herite pas le
    stdout pipe du grand-parent — sans capture par fichier, sa sortie est
    perdue (mesure #15666 case 1, meme famille que la race _readerthread
    qui a fonde _run_capture). Rend le contrat historique de run_lake :
    ``(rc_enfant, out, err)`` avec Timeout -> ``(-1, "", "TIMEOUT after Ns")``
    et organe injoignable / refus -> ``(-2, ..., raison)``. Le ``tail``
    historique du mode WSL est applique PAR L'APPELANT.
    """
    _require_str("project_path", project_path)
    organ = _find_lean_exec()
    host_cwd = _host_cwd_of(project_path)
    out_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.out')
    err_f = tempfile.NamedTemporaryFile('wb', delete=False, suffix='.err')
    out_path, err_path = out_f.name, err_f.name
    out_f.close()
    err_f.close()
    argv = [
        sys.executable, str(organ), "run", "--json",
        "--timeout", str(timeout), "--caller", _ORGAN_CALLER,
        "--cwd", host_cwd,
        "--stdout-file", out_path, "--stderr-file", err_path,
        "--", *cmd_args,
    ]
    try:
        try:
            _rc, organ_out, organ_err = _run_capture(argv, timeout + 60)
        except subprocess.TimeoutExpired:
            return -1, "", f"TIMEOUT after {timeout}s"
        except FileNotFoundError:
            return -2, "", f"lean_exec introuvable: {organ}"

        child_out = Path(out_path).read_text(
            encoding='utf-8', errors='replace')
        child_err = Path(err_path).read_text(
            encoding='utf-8', errors='replace')
        payload, _ = _split_organ_json(organ_out)
        if payload is None:
            # L'organe n'a pas rendu son verdict JSON (crash interne 127,
            # environnement casse) : echec visible, jamais de faux succes.
            reason = organ_err.strip() or "lean_exec: aucun verdict JSON rendu"
            return -2, child_out, reason
        status = payload.get("status")
        if status == "timeout":
            return -1, child_out, f"TIMEOUT after {timeout}s"
        if payload.get("exit_code") == 125 or status == "refused":
            reason = payload.get("reason") or "refuse par lean_exec (admission)"
            return -2, child_out, reason
        rc_child = payload.get("child_exit_code")
        return (rc_child if rc_child is not None else 0), child_out, child_err
    finally:
        for p in (out_path, err_path):
            try:
                Path(p).unlink()
            except OSError:
                pass


def _tail_lines(text: str, tail: int) -> str:
    """Garde les ``tail`` dernieres lignes (equivalent ``| tail -N``)."""
    if not text:
        return text
    return "\n".join(text.splitlines()[-tail:])


def run_lake(
    project_path: str,
    args: str,
    timeout: int = 600,
    tail: int = 20,
) -> Tuple[int, str, str]:
    """Run a lake command in the specified project directory.

    Migre vers l'organe confine ``scripts/lean/lean_exec.py`` (admission
    machine-wide, budget, kill-tree — See #15666 case 1) : plus AUCUNE
    invocation directe de lake ici, WSL comme natif.

    Args:
        project_path: Path to the Lake project (from get_lean_project_path).
        args: Lake arguments (e.g. "build Grothendieck").
        timeout: Timeout in seconds (default 600).
        tail: Number of lines to keep from the end of output (WSL mode only,
            comme avant la migration : le mode natif rend la sortie complete).

    Returns:
        Tuple of (returncode, stdout, stderr). Le returncode est celui de
        l'enfant lake ; -1 = timeout, -2 = organe refuse/injoignable
        (raison dans stderr).
    """
    _require_str("args", args)
    rc, out, err = _organ_run(project_path, ["lake"] + args.split(), timeout)
    if rc < 0:
        return rc, out, err
    if is_native_platform():
        return rc, out, err
    # Mode WSL historique : out contenait stdout+stderr entrelaces (2>&1) et
    # err etait vide — on preserve ce que les carnets observent.
    return rc, _tail_lines((out or "") + (err or ""), tail), ""


def run_lean_snippet(
    project_path: str,
    snippet: str,
    timeout: int = 300,
    snippet_id: str = "snippet",
) -> str:
    """Run a Lean code snippet against a Lake project.

    Migre vers l'organe confine ``lean_exec`` (See #15666 case 1). Le
    snippet est ecrit dans un fichier temporaire DU PROJET : l'ancien
    ``/tmp/lean_{id}.lean`` se resolait en ``C:\\tmp\\...`` cote natif
    (bug mesure po-2026) — dans le projet, le chemin existe dans le dialecte
    du backend (hote en natif, ``/mnt/...`` en WSL).

    Args:
        project_path: Path to the Lake project.
        snippet: Lean source code to execute.
        timeout: Timeout in seconds.
        snippet_id: Identifier for the temp file (to avoid collisions).

    Returns:
        Combined stdout + stderr as a string.
    """
    _require_str("snippet", snippet)
    snippet = textwrap.dedent(snippet).strip() + "\n"

    host_cwd = _host_cwd_of(project_path)
    tmp_path = Path(host_cwd) / f".lean_snippet_{snippet_id}.lean"
    tmp_path.write_text(snippet, encoding="utf-8")
    try:
        # Les arguments passent tels quels au backend : le chemin du fichier
        # doit etre dans le dialecte d'execution (WSL /mnt/... sous Windows).
        file_arg = str(tmp_path)
        if not is_native_platform():
            file_arg = win_to_wsl(tmp_path)
        rc, out, err = _organ_run(
            project_path, ["lake", "env", "lean", file_arg], timeout)
        if rc == -1:
            return f"TIMEOUT after {timeout}s"
        return (out or "") + (err or "")
    finally:
        tmp_path.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Sorry counting
# ---------------------------------------------------------------------------

_SORRY_TOKEN_RE = re.compile(r"\bsorry\b")


def _strip_lean_comments(content: str) -> str:
    """Strip Lean line comments (``--``) and nested block comments (``/- -/``).

    Character-level scan handling nested block comments (Lean allows them).
    Byte-identical twin of the canonical ``strip_lean_comments`` in
    ``agent_tests/prover/lean_utils.py`` (FX-6 #1453): kept local here to avoid
    coupling the notebook utility to the prover harness package. If you edit
    one, edit the other to keep the two counters from drifting.

    No string-literal awareness: Lean proofs virtually never contain the token
    ``sorry`` inside a string literal, and over-stripping there cannot create a
    false token.
    """
    out = []
    i, n, depth = 0, len(content), 0
    while i < n:
        two = content[i:i + 2]
        if depth == 0 and two == "--":
            j = content.find("\n", i)
            i = n if j < 0 else j
            continue
        if two == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and two == "-/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(content[i])
        i += 1
    return "".join(out)


def count_sorry(project_path: str, subdir: str = "") -> int:
    """Count REAL ``sorry`` tactics in ``.lean`` source (cross-platform).

    Excludes ``sorry`` mentions in block comments (``/- ... -/``) and line
    comments (``-- ...``), and skips the ``.lake`` build/package cache so only
    authored source is tallied. Pure-Python (no ``grep``/WSL fork) so the count
    is identical on every platform.

    Mirrors the canonical ``count_real_sorries`` semantics
    (``agent_tests/prover/lean_utils.py``, FX-6 #1453): after stripping comments,
    the word-bounded token catches every real form (``exact sorry``,
    ``:= by sorry``, bare ``sorry``, ``sorry -- inline``) and ignores prose
    mentions in docstrings/comments. See issue #7414 for the docstring/impl
    mismatch this corrects: the previous bare ``grep -rc sorry`` counted every
    ``sorry`` token (including prose in docstrings/comments and vendored
    ``.lake`` source), inflating the tally on lakes with sorry-rich prose.

    Args:
        project_path: Path to the Lake project.
        subdir: Optional subdirectory to scan (e.g. "Grothendieck/").

    Returns:
        Number of real ``sorry`` tactics in production source, or ``-1`` if the
        project directory cannot be read. ``0`` if the directory exists but has
        no ``.lean`` source.
    """
    _require_str("project_path", project_path)
    search_dir = os.path.join(project_path, subdir) if subdir else project_path
    if not os.path.isdir(search_dir):
        return -1

    total = 0
    for root, dirs, files in os.walk(search_dir):
        # Skip the Lake build cache + vendored deps (compiled artifacts and
        # Mathlib source, not authored content).
        dirs[:] = [d for d in dirs if d != ".lake"]
        for name in files:
            if not name.endswith(".lean"):
                continue
            try:
                with open(os.path.join(root, name), encoding="utf-8") as f:
                    content = f.read()
            except OSError:
                continue
            total += len(_SORRY_TOKEN_RE.findall(_strip_lean_comments(content)))
    return total


# ---------------------------------------------------------------------------
# File reading (cross-platform, reads from native filesystem)
# ---------------------------------------------------------------------------

def read_lean_module(
    project_name: str,
    module_path: str,
) -> str:
    """Read a .lean source file from a Lake project.

    Works on all platforms by reading from the native filesystem
    (the project directory is accessible directly on Windows too).

    Args:
        project_name: Directory name of the Lake project.
        module_path: Relative path to the .lean file (e.g. "Grothendieck/CategoryAndSites.lean").

    Returns:
        File content as a string.
    """
    _require_str("module_path", module_path)
    project_dir = find_lean_project(project_name)
    path = project_dir / module_path
    if not path.exists():
        return f"[FICHIER INTROUVABLE] {path}"
    return path.read_text(encoding="utf-8")


def display_lean_module(
    project_name: str,
    module_path: str,
    max_lines: Optional[int] = None,
    highlight: Optional[list] = None,
):
    """Display a .lean source file with line numbers.

    Args:
        project_name: Directory name of the Lake project.
        module_path: Relative path to the .lean file.
        max_lines: If set, only show the first N lines.
        highlight: List of line numbers to mark with '>>>' (1-indexed).
    """
    if highlight is not None:
        # Accept any iterable of ints (list/tuple/set); reject non-iterables
        # (e.g. a bare int) which would crash opaquely inside ``set(highlight)``.
        try:
            iter(highlight)
        except TypeError:
            raise TypeError(
                f"highlight must be an iterable of ints (or None), got "
                f"{type(highlight).__name__}: {highlight!r}"
            )
    content = read_lean_module(project_name, module_path)
    if content.startswith("[FICHIER INTROUVABLE]"):
        print(content)
        return

    lines = content.splitlines()
    if max_lines:
        lines = lines[:max_lines]

    highlight = set(highlight or [])
    module_name = Path(module_path).stem
    print(f"--- {module_path} ---")
    for i, line in enumerate(lines, 1):
        marker = " >>>" if i in highlight else "    "
        print(f"{marker} {i:>3d} | {line}")

    total = len(content.splitlines())
    if max_lines and total > max_lines:
        print(f"    ... ({total - max_lines} lignes restantes sur {total} total)")
    print(f"--- fin ({total} lignes) ---")
