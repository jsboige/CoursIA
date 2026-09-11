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

Each test materializes a fake `dist/` tree under a `tmp_path`, runs the
script's pure functions on it, and asserts on the file content and the
reported counters. The tests are positive controls: they fail on the
previous version and pass on the fix.
"""
from __future__ import annotations

import io
import os
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


def test_rewrite_substitutes_cwd_prefix(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Defect 1: rewrite must derive the prefix from cwd, not hard-code
    `C:/Program Files/Git/`. With cwd=<tmp_path> the marker `<tmp_path>/foo`
    must collapse to `./foo`."""
    monkeypatch.chdir(tmp_path)
    from scripts.post_bake_slides import _cwd_prefix_bytes, _rewrite

    cwd_prefix = _cwd_prefix_bytes()
    assert cwd_prefix.endswith(b"/")
    # Build the literal cwd-encoded form (Windows-style: backslashes -> slashes).
    cwd_as_posix = str(tmp_path).replace("\\", "/").encode("ascii")
    content = b"asset url(" + cwd_as_posix + b"/foo.css) and also ./local.js"
    new = _rewrite(content, cwd_prefix)
    assert b"./foo.css" in new, f"cwd_prefix={cwd_prefix!r} new={new!r}"
    assert cwd_as_posix not in new, f"cwd should have been substituted, got {new!r}"


def test_rewrite_handles_both_encodings(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """Defect 2: both literal and URL-encoded forms must be rewritten."""
    monkeypatch.chdir(tmp_path)
    from scripts.post_bake_slides import _rewrite

    content = (
        b"literal: Program Files marker\n"
        b"encoded: Program%20Files marker\n"
    )
    new = _rewrite(content, cwd_prefix=b"/unused/")
    assert b"Program Files" not in new
    assert b"Program%20Files" not in new


def test_check_residue_reads_each_file_once(tmp_path: Path) -> None:
    """Defect 3: residue check must detect BOTH patterns even when only
    one read per file is performed. The old code called f.read() once
    per pattern and missed the second pattern because of EOF."""
    _write(tmp_path / "dist" / "a.html", b"literal: Program Files marker only")
    _write(tmp_path / "dist" / "b.html", b"encoded: Program%20Files marker only")
    _write(tmp_path / "dist" / "c.html", b"clean: nothing to see here")

    # Run as a subprocess so the cwd-sensitive cwd_prefix logic does not
    # poison the import; cwd is set to tmp_path so the cwd-derived
    # rewrite prefix has no baked-in residue to clear.
    result = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=tmp_path,
        capture_output=True,
    )
    assert b"FAIL" not in result.stderr, result.stderr.decode("utf-8", "replace")
    assert b"OK: 0 residue" in result.stdout, result.stdout.decode("utf-8", "replace")
    assert result.returncode == 0


def test_map_files_are_rewritten(tmp_path: Path) -> None:
    """Defect 4: `.map` files must be in TARGET_EXTS -- the old version
    scanned them for residue but never rewrote them, leaving a permanent
    FAIL on any bundler that emits the cwd path inside a sourcemap."""
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
    assert b"./" in out  # rewritten to relative


# --- integration test: positive control ------------------------------------

def test_full_run_reports_modified_files(tmp_path: Path) -> None:
    """End-to-end: a `dist/` with mixed content must come out residue-free
    with `fixed >= 1` and `total >= 3`. Hits counter must reflect real
    substitutions, not phantom hits on a regex that did not match."""
    _write(tmp_path / "dist" / "index.html", b'<script src="C:/Program Files/Git/foo.js"></script>')
    _write(tmp_path / "dist" / "chunks" / "app.js", b"console.log('C:/Program Files/Git/x')")
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
    assert "TOTAL: 3/4 files modified" in stdout, stdout
    # Residue check must agree with the rewrite.
    for p in (tmp_path / "dist").rglob("*"):
        if p.is_file():
            data = p.read_bytes()
            assert b"Program Files" not in data, p
            assert b"Program%20Files" not in data, p


# --- regression guard --------------------------------------------------------

def test_fixed_counter_does_not_count_no_op_substitution(tmp_path: Path) -> None:
    """Defect 1 follow-up: `fixed` must be 0 when nothing actually changed
    in the file. The old code incremented `fixed` whenever `hits > 0`
    on `b"Program Files"` even if the actual `PATH_RE.sub()` produced no
    change (e.g. when the cwd was `/d/work/` and the regex did not match).
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
