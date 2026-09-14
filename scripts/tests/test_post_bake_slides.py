"""Anti-faux-vert tests for scripts/post_bake_slides.py.

Three generations of pins live in this file:

  - c.1037 (#15452 item 2): the four latent defects (hard-coded prefix,
    URL-encoded form, cursor-exhaustion, missing `.map`).
  - c.1051 (#15452 point 1): the "green-that-measures-nothing" -- the
    rewrite left the absolute path intact while the residue check
    returned 0.
  - #15703: the coordinator-decided contract. The whole-path collapse of
    the c.1051 fix is SUPERSEDED -- the acceptance pins, one test each:

    1. `_rewrite` replaces the **build-root prefix** by `.` and leaves
       the rest of the path byte-intact (equality test, as #15699 did).
    2. an absolute path OUTSIDE the build root makes the post-bake FAIL
       naming the offending path -- never silently rewritten.
    3. the matcher never crosses whitespace nor `<`, `>`, `)`: the
       negative-control HTML fragment leaves the markup intact.
    4. `%20` normalization is bounded to the absolute-path context:
       prose `Program%20Files` survives.
    5. the docstring describes what the code does (the obsolete
       `./nodejs/...` promise is gone).

Each test materializes a fake `dist/` tree under a `tmp_path` (or calls
the pure functions directly) and asserts on byte-exact content, the
reported counters, and the process exit code. The tests are positive
controls: each fails on the c.1051 version and passes on the contract.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPT = REPO_ROOT / "scripts" / "post_bake_slides.py"

DECK_ROOT = "D:/deck/dist"


def _write(p: Path, content: bytes) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(content)


def _tmp_posix(tmp_path: Path) -> str:
    """The tmp_path in the forward-slash absolute form the bake machine
    would embed in the output; the subprocess build root is
    `<tmp_posix>/dist` (os.path.abspath(ROOT) with cwd=tmp_path)."""
    return str(tmp_path).replace(os.sep, "/")


# --- acceptance 1: build-root prefix, byte-exact ---------------------------

def test_rewrite_replaces_build_root_prefix_byte_exact() -> None:
    """#15703 acceptance 1: the ONLY rewrite is the build-root prefix ->
    `.`, rest of the path byte-intact. Supersedes the c.1051 whole-path
    collapse (`C:/... -> ./`), which destroyed the meaningful part of
    in-root references."""
    from scripts.post_bake_slides import _rewrite

    cases = [
        # (input, expected_output) -- byte-exact equality
        (b'src="D:/deck/dist/assets/app.js"', b'src="./assets/app.js"'),
        # case-insensitive drive letter / path (Windows semantics)
        (b'src="d:/Deck/Dist/assets/app.js"', b'src="./assets/app.js"'),
        # native backslash separator in the baked path
        (rb'src="D:\deck\dist\assets\app.js"', b'src="./assets/app.js"'),
        # token equal to the root itself collapses to `.`
        (b'x "D:/deck/dist"', b'x "."'),
        # deep rest preserved verbatim
        (b'"D:/deck/dist/a/b/c.js"', b'"./a/b/c.js"'),
        # %20 INSIDE the path context is normalized (bounded, acceptance 4)
        (b'href="D:/deck/dist/Program%20Files/x.js"',
         b'href="./Program/Files/x.js"'),
    ]
    for src, expected in cases:
        out = _rewrite(src, DECK_ROOT)
        assert out == expected, (
            f"rewrite mismatch:\n  in : {src!r}\n  out: {out!r}\n  exp: {expected!r}"
        )


def test_rewrite_passes_through_content_without_absolute_path() -> None:
    """Files that don't carry an absolute Windows path must be left
    untouched (no spurious `./` insertion that would break legitimate
    content such as markdown body text)."""
    from scripts.post_bake_slides import _rewrite

    content = b"<p>plain markdown body</p>\nplain text"
    assert _rewrite(content, DECK_ROOT) == content


# --- acceptance 2: out-of-root is REJECTED, named --------------------------

def test_rewrite_out_of_root_raises_named_path() -> None:
    """#15703 acceptance 2 (unit): an absolute path outside the build
    root raises OutOfRootPathError naming it. A prose path with spaces is
    named in its bounded form (up to the first whitespace); a fully
    quoted path is named in full."""
    from scripts.post_bake_slides import OutOfRootPathError, _rewrite

    with pytest.raises(OutOfRootPathError, match="C:/Program"):
        _rewrite(b'import x from "C:/Program Files/nodejs/lib/app.js";', DECK_ROOT)
    with pytest.raises(OutOfRootPathError, match="C:/Program%20Files/nodejs/lib/app.js"):
        _rewrite(b'import x from "C:/Program%20Files/nodejs/lib/app.js";', DECK_ROOT)


def test_out_of_root_fails_post_bake_without_writing(tmp_path: Path) -> None:
    """#15703 acceptance 2 (integration): the post-bake FAILS (exit 1)
    with the offending path named in stderr, and -- two-phase design --
    NO file is written: the in-root sibling that would have been
    rewritten is still byte-identical on disk."""
    tmp_posix = _tmp_posix(tmp_path)
    out_of_root = b'import x from "C:/Program Files/nodejs/lib/app.js";'
    in_root = (f"import y from '{tmp_posix}/dist/lib/app.js';").encode()
    _write(tmp_path / "dist" / "a.html", out_of_root)
    _write(tmp_path / "dist" / "b.html", in_root)

    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert result.returncode == 1, (
        f"exit={result.returncode} stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    err = result.stderr.decode("utf-8", "replace")
    assert "FAIL" in err, err
    assert "C:/Program" in err, err
    assert (tmp_path / "dist" / "a.html").read_bytes() == out_of_root
    assert (tmp_path / "dist" / "b.html").read_bytes() == in_root


# --- acceptance 3: the matcher never eats markup ---------------------------

def test_rewrite_does_not_eat_markup() -> None:
    """#15703 acceptance 3: the negative control of residu 1. The c.1051
    greedy class consumed `</p>\\n<script src=` when a path was cited in
    prose. Under the contract: an IN-ROOT prose path is rewritten and the
    markup stays byte-intact; an OUT-OF-ROOT prose path raises, and the
    error names the bounded token only -- proof the matcher never
    reached the markup."""
    from scripts.post_bake_slides import OutOfRootPathError, _rewrite

    frag_in_root = (
        b'<p>chemin D:/deck/dist/data et autres</p>\n'
        b'<script src="app.js"></script>'
    )
    assert _rewrite(frag_in_root, DECK_ROOT) == (
        b'<p>chemin ./data et autres</p>\n'
        b'<script src="app.js"></script>'
    )

    frag_out_of_root = (
        b'<p>chemin C:/Users/MYIA/data et autres</p>\n'
        b'<script src="app.js"></script>'
    )
    with pytest.raises(OutOfRootPathError) as ei:
        _rewrite(frag_out_of_root, DECK_ROOT)
    assert "C:/Users/MYIA/data" in str(ei.value)
    assert "script" not in str(ei.value)


# --- acceptance 4: %20 bounded to the path context -------------------------

def test_prose_percent20_survives() -> None:
    """#15703 acceptance 4 (unit): `Program%20Files` in prose (no
    drive-letter context) survives the rewrite byte-identically. The
    c.1037 global `%20 -> /` substitution turned it into
    `Program/Files` in every prose paragraph."""
    from scripts.post_bake_slides import _rewrite

    content = b"<p>see Program%20Files in the docs</p>\nplain text"
    assert _rewrite(content, DECK_ROOT) == content


# --- c.1037 guards still in force under the contract -----------------------

def test_check_residue_reads_each_file_once(tmp_path: Path) -> None:
    """c.1037 defect 3: residue check must detect a remaining absolute
    path even with one read per file. Fixtures carry IN-ROOT paths under
    the subprocess build root (`<tmp>/dist`) so the rewrite succeeds and
    the residue check returns 0 on genuinely clean output."""
    tmp_posix = _tmp_posix(tmp_path)
    _write(
        tmp_path / "dist" / "a.html",
        f"import x from '{tmp_posix}/dist/lib/app.js';".encode(),
    )
    _write(
        tmp_path / "dist" / "b.html",
        f"import x from '{tmp_posix}/dist/Program%20Files/lib/app.js';".encode(),
    )
    _write(tmp_path / "dist" / "c.html", b"plain: nothing to see here")

    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert b"FAIL" not in result.stderr, result.stderr.decode("utf-8", "replace")
    assert b"OK: 0 absolute-path residue in dist/" in result.stdout, (
        result.stdout.decode("utf-8", "replace")
    )
    assert result.returncode == 0
    out_a = (tmp_path / "dist" / "a.html").read_bytes()
    out_b = (tmp_path / "dist" / "b.html").read_bytes()
    assert b"./lib/app.js" in out_a, out_a
    # %20 normalized INSIDE the path context (bounded), never in prose.
    assert b"./Program/Files/lib/app.js" in out_b, out_b


def test_map_files_are_rewritten(tmp_path: Path) -> None:
    """c.1037 defect 4: `.map` files must be in TARGET_EXTS -- the old
    version scanned them for residue but never rewrote them, leaving a
    permanent FAIL on any bundler that emits the cwd path inside a
    sourcemap."""
    tmp_posix = _tmp_posix(tmp_path)
    _write(
        tmp_path / "dist" / "assets" / "app.js.map",
        f'{{"sources":["{tmp_posix}/dist/src/app.ts"]}}'.encode(),
    )
    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert result.returncode == 0, (
        f"exit={result.returncode} stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    out = (tmp_path / "dist" / "assets" / "app.js.map").read_bytes()
    assert b'"./src/app.ts"' in out, out
    assert not re.search(rb"[A-Za-z]:[/\\]", out), out


def test_full_run_reports_modified_files(tmp_path: Path) -> None:
    """End-to-end: a `dist/` with mixed content comes out residue-free
    with the right TOTAL counter; prose `%20` survives untouched
    (#15703 acceptance 4, integration); no drive-letter path remains."""
    tmp_posix = _tmp_posix(tmp_path)
    _write(
        tmp_path / "dist" / "index.html",
        f'<script src="{tmp_posix}/dist/assets/foo.js"></script>'.encode(),
    )
    _write(
        tmp_path / "dist" / "chunks" / "app.js",
        f"console.log('{tmp_posix}/dist/x')".encode(),
    )
    _write(tmp_path / "dist" / "404.html", b"encoded Program%20Files here")
    _write(tmp_path / "dist" / "ok.txt", b"plain text, nothing to rewrite")

    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert result.returncode == 0, (
        f"exit={result.returncode} stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    stdout = result.stdout.decode("utf-8")
    assert "TOTAL: 2/4 files modified" in stdout, stdout
    assert b'./assets/foo.js' in (tmp_path / "dist" / "index.html").read_bytes()
    assert b"'./x'" in (tmp_path / "dist" / "chunks" / "app.js").read_bytes()
    # Prose %20 survives (acceptance 4); no absolute path survives.
    assert (tmp_path / "dist" / "404.html").read_bytes() == b"encoded Program%20Files here"
    for p in (tmp_path / "dist").rglob("*"):
        if p.is_file():
            data = p.read_bytes()
            assert not re.search(rb"[A-Za-z]:[/\\]", data), p


def test_fixed_counter_does_not_count_no_op_substitution(tmp_path: Path) -> None:
    """c.1037 defect 1 follow-up: `fixed` must be 0 when nothing actually
    changed in the file."""
    _write(tmp_path / "dist" / "nothing.html", b"plain text without any marker")
    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert result.returncode == 0
    stdout = result.stdout.decode("utf-8")
    assert "TOTAL: 0/1 files modified" in stdout, stdout


def test_residue_pattern_matches_remaining_absolute_path(tmp_path: Path) -> None:
    """c.1051 guard: `_check_residue` must catch files that still carry a
    drive-letter absolute path (e.g. put back by a downstream tool) --
    the count is per FILE, so two dirty files give 2, not 0."""
    from scripts.post_bake_slides import _check_residue

    _write(tmp_path / "dist" / "a.html", b'import x from "C:/./nodejs/lib/app.js";')
    _write(tmp_path / "dist" / "b.html", b'import x from "C:/Users/dev/lib/x.js";')
    assert _check_residue(str(tmp_path / "dist")) == 2


# --- acceptance 5: docstring describes the code ----------------------------

def test_docstring_describes_the_code() -> None:
    """#15703 acceptance 5: the docstrings no longer carry the c.1051
    PROMISE (`C:/Program%20Files/nodejs/...` becomes `./nodejs/...`)
    that contradicted the code, and document the build-root contract
    actually implemented. The c.1051 HISTORY note (what the old code
    wrongly produced, `C:/./nodejs/...`) legitimately stays."""
    import scripts.post_bake_slides as pbs

    assert "becomes `./nodejs/...`" not in pbs.__doc__, pbs.__doc__
    assert "becomes `./nodejs/...`" not in pbs._rewrite.__doc__
    assert "build root" in pbs.__doc__.lower()
    assert "build-root" in pbs._rewrite.__doc__.lower()
    assert "OutOfRootPathError" in pbs._rewrite.__doc__
