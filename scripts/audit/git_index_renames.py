"""Shared probe: files arriving in the git index as renames.

Extracted from ``scripts/check_subprocess_encoding.py`` (PR #24067, issue
#24039) so the four other path-keyed defect hooks can share it instead of
copying it (#24068): ``check_encoding_corruption``, ``check_null_exec``,
``check_cell_source_parses`` and ``check_knots_extracts`` all read staged
filenames (``pass_filenames: true``) and none of them knew that a file can
be merely *moved*. A consolidation-by-move (the #23553 case) re-passed each
moved notebook in front of those predicates, and a moved-but-untouched
notebook that already carried a defect came out red -- on a gesture that did
not introduce it. The only visible way out was ``SKIP=``, i.e. disabling the
guard rather than making it just.

One parser, four probes:

``staged_renames_with_old() -> dict[str, str]``
    Every index rename (any similarity), as ``destination -> source``. The
    #24066 delta ratchet uses it to compare a renamed-with-edits file
    against its previous blob and report only what is new.

``staged_pure_renames() -> set[str]``
    Destinations with similarity 100% (status ``R100``). A pure rename moves
    content without touching it, so it cannot introduce a defect site: the
    sites it carries predate the move. CI forms already agree
    (``--diff-filter=AM`` drops every ``R`` status); this is the pre-commit
    half. Renames with edits (``R<100``) stay scanned -- the lane did touch
    that content; its inherited-sites half is the #24066 delta.

``renames_between(base, head)`` / ``pure_renames_between(base, head)``
    The same two views over a **commit range** instead of the index: the CI
    half of the family (the checkout IS the head, there is no index). The
    ``--base`` mode of ``check_encoding_corruption`` and the ``--pr-diff``
    mode of ``check_cell_source_parses`` are path-keyed there too, and a
    pure move re-reported their inherited defects (measured, #24068).

Both return empty results when git cannot answer (not a repository, no
index, no ``git`` on PATH), which keeps callers scanning -- fail-open
toward scanning, exactly like the #24067 form. Importing scripts must keep
``from __future__ import annotations`` at the top (the py39 hook-import
guard follows this module through its import closure).
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Garde-fou anti-blocage : sur un clone PARTIEL (promisor/blob:none, le cas
# de ce dépôt sur les postes de la flotte), git peut avoir besoin d'un blob
# absent du store local -- il le va alors chercher sur le remote, et une
# recherche qui ne aboutit pas peut rester bloquée. Un hook pré-commit qui
# bloque un commit est pire qu'un hook qui perd un skip : au dépassement,
# la sonde rend None (fail-open) et les appelants continuent de scanner
# comme si aucun renommage n'avait été vu.
GIT_TIMEOUT = 60

# Racine du dépôt sur lequel le processus travaille, mise en cache par
# répertoire courant (le cache ne doit pas survivre à un changement de cwd :
# un test qui travaille dans un dépôt témoin verrait sinon l'index du dépôt
# principal).
_TOPLEVEL: dict[str, Path] = {}


def repo_root() -> Path:
    """Racine du dépôt sur lequel le processus travaille.

    Ancrage sur git lui-même (``rev-parse --show-toplevel`` depuis le
    répertoire courant) : le pré-commit et la CI tournent dans la racine du
    dépôt, et c'est la seule racine qui fait foi pour tous les appelants --
    la carte des renommages et la liste des fichiers changés doivent venir
    du MÊME dépôt, sinon un chemin se retrouve dans l'un et pas dans l'autre
    (le skip dégénère en « pas de skip », sans erreur).

    Hors de tout dépôt, la racine du module sert de repli.
    """
    cwd = str(Path.cwd())
    cached = _TOPLEVEL.get(cwd)
    if cached is not None:
        return cached
    out = git_out("rev-parse", "--show-toplevel")
    root = REPO_ROOT
    if out:
        candidate = out.strip()
        # `git rev-parse --show-toplevel` answers with a SINGLE directory
        # path: never a NUL byte, never a missing directory. An answer that
        # breaks that contract means the probe is not talking to git (a
        # stub, a corrupted stdout, a test double) -- and turning it into a
        # Path defers the failure to `Path(...).resolve()`, which raises
        # `ValueError: embedded null byte` on POSIX and takes the guard
        # DOWN instead of letting it scan. Such an answer is rejected, and
        # the probe falls back to the module's root: fail-open toward
        # scanning, never an exception.
        #
        # The rejection also protects the CACHE: an unusable root memoised
        # for a cwd would poison every later caller of that cwd (measured in
        # CI on #25032: the cache handed a NUL-laden path to a later test
        # that ran in the same working directory).
        if candidate and "\0" not in candidate:
            path = Path(candidate)
            if path.is_dir():
                root = path
    _TOPLEVEL[cwd] = root
    return root


def git_out(*args: str) -> str | None:
    """``git <args>`` from the current directory, stdout as text; None on any
    failure.

    ``encoding="utf-8", errors="replace"`` is mandatory: a ``text=True``
    without ``encoding=`` would decode with the host locale (cp1252 on the
    Windows workers) and crash on the very payloads this family of guards
    processes -- the defect class the sibling gate exists for (#12811).

    Le ``cwd`` est celui du processus (convention de git) : le hook
    pré-commit et la CI tournent dans la racine du dépôt, et un test peut
    ainsi travailler dans un dépôt témoin. Un sha qui n'appartient pas au
    dépôt courant déclenche sur un clone partiel une **recherche lazy** sur
    le remote : c'est pourquoi un appelant doit toujours ancrer git sur le
    dépôt qu'il veut interroger (cf. ``repo_root``).
    """
    try:
        proc = subprocess.run(
            ["git", *args], capture_output=True,
            encoding="utf-8", errors="replace", check=False,
            timeout=GIT_TIMEOUT,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    return proc.stdout if proc.returncode == 0 else None


def _parse_name_status_z(out: str) -> dict[str, tuple[str, str]]:
    """Parse a ``--name-status -z`` payload into ``destination -> (source, score)``.

    With no threshold argument, git emits the score verbatim in the status
    token (``R100``, ``R087``). Copy (``C``) entries are reported with score
    ``"C"`` -- a copy's destination content also comes from an existing blob,
    so the pure-rename caller treats it as not-pure (the source file still
    exists) while the delta caller gets the comparison it wants. Truncated
    payloads keep what was parsed; an empty payload yields ``{}``.
    """
    parts = out.split("\0")
    dest: dict[str, tuple[str, str]] = {}
    i = 0
    while i < len(parts):
        status = parts[i]
        if not status:
            i += 1
            continue
        if status[0] in ("R", "C"):
            if i + 2 >= len(parts):
                break  # truncated payload: keep what was parsed so far
            score = status[1:] if status[0] == "R" else "C"
            dest[parts[i + 2]] = (parts[i + 1], score)
            i += 3
        else:
            i += 2
    return dest


def _staged_renames_scored() -> dict[str, tuple[str, str]]:
    """Index renames as ``destination -> (source, similarity)``.

    Reads ``git diff --cached --find-renames --name-status -z``. An
    unreachable git yields ``{}`` (callers keep scanning everything --
    fail-open, never a silent skip).
    """
    out = git_out("diff", "--cached", "--find-renames", "--name-status", "-z")
    if out is None:
        return {}
    return _parse_name_status_z(out)


def renames_between(base: str, head: str = "HEAD") -> dict[str, tuple[str, str]]:
    """Renames between ``base...head`` as ``destination -> (source, similarity)``.

    The CI counterpart of the index probe. A path-keyed hook that runs in CI
    (where the checkout IS the head) must know that a file can be merely
    MOVED there too -- the #24068 family is not a pre-commit-only defect.

    The diff is taken **without pathspec** on purpose: a pathspec restricted
    to the destination breaks the rename pairing (git cannot see the source
    it would have to pair with), and the destination then looks like a
    brand-new file -- every line counted as added. That is exactly how a
    pure move resurrects an inherited defect in the ``--base`` mode of
    ``check_encoding_corruption`` (measured, #24068).
    """
    out = git_out("diff", "--find-renames", "--name-status", "-z",
                   f"{base}...{head}")
    if out is None:
        return {}
    return _parse_name_status_z(out)


def pure_renames_between(base: str, head: str = "HEAD") -> set[str]:
    """Destinations that are a *pure* rename (R100) between ``base`` and ``head``.

    The CI-side skip list: a moved-without-edits file adds no line, so no
    defect predicate keyed on added lines can fire on it.
    """
    return {
        dest for dest, (_src, score) in renames_between(base, head).items()
        if score == "100"
    }


def staged_renames_with_old() -> dict[str, str]:
    """Every index rename/copy as ``destination -> source path``."""
    return {new: old for new, (old, _score) in _staged_renames_scored().items()}


def staged_pure_renames() -> set[str]:
    """Destinations arriving in the index as a *pure* rename (R100 only).

    The #24039/#24068 skip list: a moved-without-edits file cannot introduce
    a defect, so path-keyed hooks must not re-report its inherited sites as
    new.
    """
    return {
        new for new, (_old, score) in _staged_renames_scored().items()
        if score == "100"
    }


def repo_relative(path: str) -> str:
    """Normalise a path to the repo-relative POSIX form git reports.

    Git's index payload is keyed by repo-relative forward-slash paths, but a
    caller may hand an ABSOLUTE path (a test, a manual invocation) or a
    Windows path with backslashes. Comparing the two forms directly would
    silently miss every rename -- the skip would degrade into "no skip"
    without any error, which is the failure mode this helper removes. The
    comparison key must be identical on both sides, so it is computed here,
    once, for every caller.

    The separator conversion is made EXPLICIT, because the platform does not
    do it for us: on Windows `Path.as_posix()` turns the backslashes into
    forward slashes, on POSIX a backslash is a legal character in a file
    name and the conversion NEVER happens -- so the same call produced two
    different keys on the two platforms, and the Windows run was green by
    accident while the CI run (Linux) missed every rename (measured on
    #25032). The key is now the same everywhere.

    A root that cannot be resolved (unusable `rev-parse` answer, path
    outside the tree) never raises: the caller keeps scanning the file --
    an absolute path outside the tree cannot be an index entry anyway.
    """
    normalised = path.replace("\\", "/")
    p = Path(normalised)
    try:
        root = repo_root().resolve()
    except (ValueError, OSError):
        root = None
    if root is not None:
        try:
            if not p.is_absolute():
                p = root / p
            return p.resolve().relative_to(root).as_posix()
        except (ValueError, OSError):
            pass
    try:
        return p.as_posix()
    except ValueError:
        return normalised


def skip_pure_renames(paths: Iterable[str]) -> tuple[list[str], list[str]]:
    """Split paths into (kept, skipped-as-pure-rename), repo-relative keys.

    The single entry point the four sibling hooks of #24068 use: each of them
    receives staged filenames (``pass_filenames: true``) and must ignore the
    ones that merely moved. The comparison is done on the repo-relative
    POSIX form (``repo_relative``), because pre-commit hands Windows paths
    with backslashes while git reports forward slashes -- the same
    normalisation the #24067 form used, kept in one place so four hooks
    cannot drift on it.

    ``skipped`` is empty whenever git cannot answer, so a non-repository run
    (or a unit test with a synthetic path list) keeps scanning everything.
    """
    pure = staged_pure_renames()
    kept: list[str] = []
    skipped: list[str] = []
    for p in paths:
        if repo_relative(p) in pure:
            skipped.append(p)
        else:
            kept.append(p)
    return kept, skipped
