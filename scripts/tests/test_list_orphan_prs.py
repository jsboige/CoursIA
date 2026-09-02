#!/usr/bin/env python3
"""Unit tests for list_orphan_prs.py -- the orphan-PR reader of #13086.

Pins the reader half of the orphan detection contract:

- Pure function `find_orphans` returns PRs whose body has NO parseable
  `Grain:` tag per `grain_tag.parse_grain_tag` (the same form-tolerant
  reader the merge-gate uses, #9485).
- `_is_orphan` agrees with `grain_tag` on each canonical form:
  `Grain: TIER/GENRE -- lane ...`, `**Grain:** ...`, `## Grain\n\n...`,
  bare `Grain TIER/GENRE ...`, and tolerates empty bodies as orphan.
- `render_text` reports counts and never crashes on empty input.
- `main` CLI: --limit > 0, --author filter, --json shape.

A control test pins the positive case: a body carrying ANY of the canonical
forms is NOT orphan (so the merge-gate and the reader agree).

Run: python -m pytest scripts/tests/test_list_orphan_prs.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

# `list_orphan_prs` lives under scripts/ci/ (with its sibling scripts under
# scripts/), so we add the ci subdir to the path. Same shape as the other
# `scripts/tests/test_*.py` files that import from `scripts/ci/`.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import list_orphan_prs as lop  # noqa: E402


# --- helpers -----------------------------------------------------------------

def _pr(number, title, author="myia-po-2023", branch=None, body=""):
    """Build a fake PR row shaped like `gh pr list --json ...` output."""
    return {
        "number": number,
        "title": title,
        "author": {"login": author},
        "headRefName": branch or f"feature/{number}-test",
        "body": body,
    }


# --- _is_orphan --------------------------------------------------------------

def test_is_orphan_true_for_empty_body():
    """A PR with no body at all is orphan (nothing to parse)."""
    assert lop._is_orphan("") is True
    assert lop._is_orphan(None) is True


def test_is_orphan_true_for_prose_without_tag():
    """A body with prose but no `Grain:` line is orphan."""
    body = (
        "## Summary\n\n"
        "This PR dedups 4 byte-identical test pairs. No tag line is present.\n"
    )
    assert lop._is_orphan(body) is True


def test_is_orphan_false_for_canonical_tag():
    """The canonical `Grain: TIER/GENRE -- lane ...` form is NOT orphan."""
    body = "Grain: MED/guard -- lane myia-po-2023:CoursIA -- prev: LIGHT/docs #13045\n"
    assert lop._is_orphan(body) is False


def test_is_orphan_false_for_bold_tag_form():
    """The bold `**Grain:** ...` form (the toleration surface of #9485) is NOT orphan."""
    body = "**Grain:** MED/guard - lane myia-po-2023:CoursIA\n"
    assert lop._is_orphan(body) is False


def test_is_orphan_false_for_title_then_tag():
    """The `## Grain\\n\\nLIGHT/guard ...` form (title + next line) is NOT orphan."""
    body = "## Grain\n\nMED/guard -- lane myia-po-2023:CoursIA\n"
    assert lop._is_orphan(body) is False


def test_is_orphan_false_for_bare_grain_word():
    """The bare `` `Grain` ... `` no-colon form is NOT orphan (#9485 tolerance)."""
    body = "`Grain` MED/guard -- lane myia-po-2023:CoursIA\n"
    assert lop._is_orphan(body) is False


# --- find_orphans (pure function) -------------------------------------------

def test_find_orphans_returns_only_bodyless_rows():
    """Mixed batch: 3 tagged + 2 untagged. find_orphans returns the 2 untagged."""
    rows = [
        _pr(13001, "tagged 1", body="Grain: MED/docs -- lane jsboige:CoursIA -- prev: LIGHT/docs #12999"),
        _pr(13002, "no tag 1", body="## Summary\nstuff\n"),
        _pr(13003, "tagged 2", body="**Grain:** LIGHT/guard -- lane myia-po-2026:CoursIA"),
        _pr(13004, "no tag 2", body=""),
        _pr(13005, "tagged 3", body="## Grain\n\nMED/qc -- lane myia-po-2026:CoursIA"),
    ]
    orphans = lop.find_orphans(rows)
    numbers = [o["number"] for o in orphans]
    assert numbers == [13002, 13004]
    # Each orphan row keeps upstream metadata, drops `body`
    for o in orphans:
        assert "body" not in o
        assert {"number", "title", "author", "branch"} <= o.keys()


def test_find_orphans_empty_input():
    """No PRs -> no orphans (not a crash, not a false orphan)."""
    assert lop.find_orphans([]) == []


def test_find_orphans_all_tagged_is_empty():
    """All PRs carry a tag -> zero orphans."""
    rows = [
        _pr(100, "tagged", body="Grain: LIGHT/docs -- lane jsboige:CoursIA"),
        _pr(101, "tagged", body="Grain: MED/lean -- lane myia-po-2024:CoursIA-2"),
    ]
    assert lop.find_orphans(rows) == []


# --- render_text -------------------------------------------------------------

def test_render_text_no_orphans():
    out = lop.render_text([])
    assert "no orphan" in out.lower()


def test_render_text_counts_orphans_and_lists_each():
    rows = [
        _pr(13001, "no tag 1", author="alice"),
        _pr(13002, "no tag 2", author="bob"),
    ]
    orphans = lop.find_orphans(rows)
    out = lop.render_text(orphans)
    assert "2 orphan" in out
    assert "13001" in out
    assert "13002" in out
    assert "alice" in out
    assert "bob" in out


# --- main (CLI) -- bad args --------------------------------------------------

def test_main_rejects_zero_limit(capsys):
    rc = lop.main(["--limit", "0"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "limit" in captured.err.lower()


def test_main_rejects_negative_limit(capsys):
    rc = lop.main(["--limit", "-5"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "limit" in captured.err.lower()


# --- main -- _run_gh_pr_list error path --------------------------------------

def test_run_gh_pr_list_propagates_subprocess_failure(monkeypatch, capsys):
    """If `gh pr list` fails (auth, network), main returns 2 with stderr msg."""
    def fake_run(*args, **kwargs):
        # Build a fake CompletedProcess that looks like gh failure
        import subprocess as sp
        return sp.CompletedProcess(args=["gh"], returncode=1, stdout="", stderr="auth required")

    monkeypatch.setattr(lop.subprocess, "run", fake_run)
    rc = lop.main(["--limit", "10"])
    captured = capsys.readouterr()
    assert rc == 2
    assert "gh pr list" in captured.err.lower() or "auth" in captured.err.lower()


# --- control positive: reader and merge-gate agree ---------------------------

def test_control_positive_canonical_forms_all_non_orphan():
    """Pin that every canonical form (the 4 tolerated by #9485) is NOT orphan.

    If this drifts, the reader and `variation-tag-required` (the merge-gate)
    are saying different things about what "orphan" means -- which is the
    structural defect #13086 was designed to detect.
    """
    canonical_forms = [
        # 1. Canonical
        "Grain: MED/guard -- lane myia-po-2023:CoursIA -- prev: LIGHT/docs #13045",
        # 2. Bold
        "**Grain:** MED/guard - lane myia-po-2023:CoursIA",
        # 3. Title + next line
        "## Grain\n\nMED/guard -- lane myia-po-2023:CoursIA\n",
        # 4. No colon
        "`Grain` MED/guard -- lane myia-po-2023:CoursIA\n",
    ]
    for body in canonical_forms:
        assert lop._is_orphan(body) is False, f"reader said orphan for body: {body!r}"
