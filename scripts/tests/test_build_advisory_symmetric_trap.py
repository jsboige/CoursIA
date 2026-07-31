#!/usr/bin/env python3
"""Regression tests for build_advisory.sh — denominator + symmetric-trap (#8929/#8930).

PR #8930 added the symmetric-trap probe to `scripts/slides/build_advisory.sh`
(a non-convention dir that DOES carry a deck is invisible to discovery -> the
`check` command must FAIL, mirroring the gate in BOTH directions). That fix
shipped without a test. These tests build synthetic `slides/` trees in
`tmp_path` and assert the probe fires, so the behavior is locked against
regression. The decisive case is `test_nonconvention_dir_with_deck_is_caught`
(#8929). Verified firsthand before encoding (C976-L).

Executable two ways:
    py scripts/tests/test_build_advisory_symmetric_trap.py
    npx pytest scripts/tests/test_build_advisory_symmetric_trap.py
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "slides" / "build_advisory.sh"

# build_advisory.sh relies on `git check-ignore` (the authority on "ignored").
# `is_deck_dir` falls through to the convention grep when check-ignore reports
# "not ignored" (exit 1), which requires the cwd to be a git worktree. We init a
# real (empty) repo in tmp_path so the tool behaves exactly as it does in CI.
GIT = shutil.which("git")
BASH = shutil.which("bash")

pytestmark = pytest.mark.skipif(
    BASH is None or GIT is None,
    reason="build_advisory.sh needs bash and git on PATH",
)


def _make_tree(tmp_path: Path, entries: dict[str, str]) -> Path:
    """Build a slides/ tree under tmp_path. entries maps rel-path -> file content.

    A rel-path ending in '/' creates an empty dir; otherwise a file with content.
    Returns the slides/ root. Also git-inits tmp_path (check-ignore authority).
    """
    root = tmp_path / "slides"
    root.mkdir(exist_ok=True)
    for rel, content in entries.items():
        target = root / rel
        if rel.endswith("/"):
            target.mkdir(parents=True, exist_ok=True)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
    subprocess.run(
        [GIT, "init", "-q", str(tmp_path)],
        check=True, capture_output=True,
    )
    return root


def _run_check(slides_root: Path) -> subprocess.CompletedProcess:
    """Run `build_advisory.sh check` against a slides tree, return the process."""
    env = os.environ.copy()
    env["SLIDES_DIR"] = str(slides_root)
    return subprocess.run(
        [BASH, str(SCRIPT), "check"],
        capture_output=True, text=True, env=env, cwd=str(slides_root.parent),
        encoding="utf-8", errors="replace",
    )


class TestDenominatorCheck:
    """The trap-1 direction (#8817): convention dir + denominator mismatch."""

    def test_convention_dir_with_deck_passes(self, tmp_path: Path):
        slides = _make_tree(tmp_path, {"01-introduction/slides.md": "# Intro\n"})
        proc = _run_check(slides)
        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "PASS" in proc.stdout

    def test_convention_dir_without_deck_fails(self, tmp_path: Path):
        # One healthy dir + one empty convention dir -> the empty one is a
        # silent-skip risk (deck dir with ZERO discovered decks).
        slides = _make_tree(
            tmp_path,
            {"01-real/slides.md": "# Real\n", "02-empty/": ""},
        )
        proc = _run_check(slides)
        assert proc.returncode == 1
        assert "02-empty" in proc.stdout


class TestSymmetricTrap8929:
    """The symmetric direction (#8929/#8930): the decisive regression.

    A dir that does NOT match the NN/SN convention but DOES carry a deck file is
    invisible to discovery. The `check` command must FAIL here (mirroring the
    gate), otherwise an author renaming `07-xxx` to `slides-07-xxx` sees green
    locally and discovers the red `::error::` only in CI.
    """

    def test_nonconvention_dir_with_deck_is_caught(self, tmp_path: Path):
        # A healthy convention deck + a renamed (non-convention) dir carrying a deck.
        slides = _make_tree(
            tmp_path,
            {
                "01-introduction/slides.md": "# Intro\n",
                "intro-renamed/slides.md": "# Renamed\n",  # non-convention, has deck
            },
        )
        proc = _run_check(slides)
        assert proc.returncode == 1, "symmetric-trap probe should FAIL #8929"
        # The probe prints to stderr.
        assert "intro-renamed" in proc.stderr
        assert "convention" in proc.stderr.lower()

    def test_nonconvention_dir_with_deck_dash_pattern_caught(self, tmp_path: Path):
        # deck-*.md is the other recognized deck filename (not just slides.md).
        slides = _make_tree(
            tmp_path,
            {
                "01-introduction/slides.md": "# Intro\n",
                "legacy-talk/deck-2024.md": "# Legacy\n",
            },
        )
        proc = _run_check(slides)
        assert proc.returncode == 1
        assert "legacy-talk" in proc.stderr

    def test_nonconvention_dir_without_deck_is_skipped(self, tmp_path: Path):
        # A peer infra dir (no convention, no deck) must NOT trip a false error.
        slides = _make_tree(
            tmp_path,
            {
                "01-introduction/slides.md": "# Intro\n",
                "_assets/style.css": "body {}\n",   # non-convention, no deck -> fine
            },
        )
        proc = _run_check(slides)
        assert proc.returncode == 0, proc.stdout + proc.stderr
        assert "PASS" in proc.stdout


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
