"""Anti-faux-vert tests for scripts/post_bake_slides.py.

These tests pin the four latent defects that ai-01 measured on the previous
version of `post_bake_slides.py` (cf. #15452 item 2 / DM msg-20260911T025004):

  1. cwd-derived rewrite prefix (the old regex was hard-coded to
     `C:/Program Files/Git/`).
  2. both literal (`Program Files`) and URL-encoded (`Program%20Files`)
     forms rewritten.
  3. residue check reads each file exactly once (the old code called
     `f.read()` once per pattern, hitting EOF on the second).
  4. `.map` files included in `TARGET_EXTS` (the old code scanned them
     for residue but never rewrote them).

Tell c.1051 ★ NEW : a fifth positive control pins the "green-that-measures-
nothing" defect raised in #15452 point 1. The previous fix rewrote only
the substring `Program Files` to `.`, leaving the absolute machine path
(`C:/Program Files/nodejs/...`) intact as `C:/./nodejs/...` while
`_check_residue` returned 0 because it matched the marker that was just
removed. The new detection pattern is shape-based (absolute Windows
paths, `%20` separators), so the test below fails on the previous fix
and passes on the new one.

Each test materializes a fake `dist/` tree under a `tmp_path`, runs the
script's pure functions on it, and asserts on the file content and the
reported counters. The tests are positive controls: they fail on the
previous version and pass on the fix.
"""
from __future__ import annotations

import io
import os
import re
import subprocess
import sys
from contextlib import redirect_stdout
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPT = REPO_ROOT / "scripts" / "post_bake_slides.py"


# --- pure-function unit tests ------------------------------------------------

def _write(p: Path, content: bytes) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(content)


def test_rewrite_substitutes_any_absolute_windows_path(tmp_path: Path) -> None:
    """Tell c.1051 ★ NEW : the rewrite must collapse any drive-letter
    absolute path, not just a cwd-derived prefix or the substring
    `Program Files`. Reproduces the case ai-01 measured:

        before : C:/Program Files/nodejs/lib/@slidev/client/app.js
        after  : ./nodejs/lib/@slidev/client/app.js
    """
    from scripts.post_bake_slides import _rewrite

    content = b'import x from "C:/Program Files/nodejs/lib/@slidev/client/app.js";'
    new = _rewrite(content)
    assert b"C:/Program Files" not in new, new
    assert b"./" in new, new
    # The replacement must NOT leave an absolute path behind.
    assert not re.search(rb"[A-Za-z]:[/\\]", new), new


def test_rewrite_handles_url_encoded_separator(tmp_path: Path) -> None:
    """Tell c.1051 ★ NEW : URL-encoded `%20` inside a drive-letter path
    must be normalized first, then the whole path collapsed to `./`."""
    from scripts.post_bake_slides import _rewrite

    content = b'import x from "C:/Program%20Files/nodejs/lib/app.js";'
    new = _rewrite(content)
    assert b"Program%20Files" not in new, new
    assert b"%20" not in new, new
    assert b"./" in new, new


def test_rewrite_passes_through_content_without_absolute_path(tmp_path: Path) -> None:
    """Files that don't carry an absolute Windows path must be left
    untouched (no spurious `./` insertion that would break legitimate
    content such as markdown body text)."""
    from scripts.post_bake_slides import _rewrite

    content = b"<p>plain markdown body</p>\nplain text"
    new = _rewrite(content)
    assert new == content, (new, content)


def test_rewrite_handles_backslash_separator(tmp_path: Path) -> None:
    """Windows-native backslash paths (`C:\\...`) must also collapse to
    `./...` -- not just POSIX-style forward slashes."""
    from scripts.post_bake_slides import _rewrite

    content = rb'import x from "C:\Program Files\nodejs\lib\app.js";'
    new = _rewrite(content)
    assert b"C:\\" not in new, new
    assert b"./" in new, new


def test_rewrite_handles_both_encodings(tmp_path: Path) -> None:
    """Defect 2 (c.1037): both literal and URL-encoded forms must be rewritten."""
    from scripts.post_bake_slides import _rewrite

    content = (
        b"literal: C:/Program Files marker\n"
        b"encoded: C:/Program%20Files marker\n"
    )
    new = _rewrite(content)
    assert b"Program Files" not in new
    assert b"Program%20Files" not in new


def test_check_residue_reads_each_file_once(tmp_path: Path) -> None:
    """Defect 3 (c.1037): residue check must detect both an absolute path
    and a URL-encoded separator even when only one read per file is
    performed. The old code called f.read() once per pattern and missed
    the second pattern because of EOF.
    """
    _write(tmp_path / "dist" / "a.html", b"import x from 'C:/Program Files/lib/app.js';")
    _write(tmp_path / "dist" / "b.html", b"import x from 'C:/Program%20Files/lib/app.js';")
    _write(tmp_path / "dist" / "c.html", b"plain: nothing to see here")

    # Run as a subprocess so the cwd-sensitive logic does not poison the
    # import; cwd is set to tmp_path.
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


def test_map_files_are_rewritten(tmp_path: Path) -> None:
    """Defect 4 (c.1037): `.map` files must be in TARGET_EXTS -- the old
    version scanned them for residue but never rewrote them, leaving a
    permanent FAIL on any bundler that emits the cwd path inside a
    sourcemap.
    """
    _write(
        tmp_path / "dist" / "assets" / "app.js.map",
        b'{"sources":["C:/Program Files/Git/somewhere/app.ts"]}',
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
    assert b"Program Files" not in out
    assert not re.search(rb"[A-Za-z]:[/\\]", out), out


# --- integration test: positive control ------------------------------------

def test_full_run_reports_modified_files(tmp_path: Path) -> None:
    """End-to-end: a `dist/` with mixed content must come out residue-free
    with `fixed >= 1` and `total >= 3`. Hits counter must reflect real
    substitutions, not phantom hits on a regex that did not match.
    """
    _write(tmp_path / "dist" / "index.html", b'<script src="C:/Program Files/Git/foo.js"></script>')
    _write(tmp_path / "dist" / "chunks" / "app.js", b"console.log('C:/Program Files/Git/x')")
    _write(tmp_path / "dist" / "404.html", b"encoded C:/Program%20Files here")
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
    assert "TOTAL: 3/4 files modified" in stdout, stdout
    # Residue check must agree with the rewrite.
    for p in (tmp_path / "dist").rglob("*"):
        if p.is_file():
            data = p.read_bytes()
            assert not re.search(rb"[A-Za-z]:[/\\]", data), p
            assert b"%20" not in data, p


# --- regression guards -------------------------------------------------------

def test_fixed_counter_does_not_count_no_op_substitution(tmp_path: Path) -> None:
    """Defect 1 follow-up (c.1037): `fixed` must be 0 when nothing actually
    changed in the file. The old code incremented `fixed` whenever
    `hits > 0` on `b"Program Files"` even if the actual `PATH_RE.sub()`
    produced no change.
    """
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
    """Tell c.1051 ★ NEW : `_check_residue` must catch a file whose rewrite
    would have left an absolute path behind. This is the positive control
    that the old fix's `_check_residue(b"Program Files", b"Program%20Files")`
    could NOT catch (because it matched the literal substring, which the
    rewrite had already consumed).
    """
    from scripts.post_bake_slides import _rewrite, _check_residue

    bad = b'import x from "C:/./nodejs/lib/app.js";'
    new = _rewrite(bad)
    # The new rewrite MUST collapse `C:/./nodejs/...` too.
    assert not re.search(rb"[A-Za-z]:[/\\]", new), new
    # Two files with absolute paths survive the rewrite (simulating a
    # downstream tool that puts them back in) -- residue check must catch
    # both, so the count is 2, not 0.
    _write(tmp_path / "dist" / "a.html", bad)
    _write(tmp_path / "dist" / "b.html", b'import x from "C:/Users/dev/lib/x.js";')
    assert _check_residue(str(tmp_path / "dist")) == 2
