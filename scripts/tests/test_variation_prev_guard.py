#!/usr/bin/env python3
"""Unit tests for variation_prev_guard.py -- the BLOCKING prev: close-keyword
gate (#10093).

The #10093 incident: a COMMIT MESSAGE carrying `prev: MED/fix #10067` made
GitHub auto-close PR #10067 at the squash-merge of #10063 -- the PR body of
#10063 was sane (`MED/tooling`). The gate must therefore scan BOTH the body
AND the commit messages, and block (exit 1) when a `prev:` genre is a closing
keyword.

Run:
    python -m pytest scripts/tests/test_variation_prev_guard.py
"""
import sys
from pathlib import Path

# Insert `scripts/ci/` so the script under test is importable from a flat
# `import variation_prev_guard` (same convention as test_variation_tag_required.py).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_prev_guard as vpg  # noqa: E402


CLEAN_BODY = "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2 -- prev: MED/infra #10067"


def test_clean_body_passes():
    v = vpg.check(CLEAN_BODY)
    assert v["guard_pass"] is True
    assert v["hits"] == []


def test_offending_body_blocks():
    # A `prev: MED/fix #10067` in the BODY -> block.
    v = vpg.check(
        "Grain: MED/fix -- lane myia-po-2024:CoursIA-2 -- prev: MED/fix #10067 (c.1331+50)"
    )
    assert v["guard_pass"] is False
    assert v["hits"]["body"] == [{"tier": "MED", "genre": "fix"}]
    assert "refactor" in v["reason"] or "guard" in v["reason"] or "tooling" in v["reason"]


def test_commit_message_only_blocks():
    # The #10093 incident case: the BODY is clean, the COMMIT carries the
    # offending `prev: MED/fix #10067`. A body-only gate would miss it.
    commits = [
        "feat(ci): some normal commit",
        "Grain: MED/fix -- prev: MED/fix #10067 (c.1331+50)",
    ]
    v = vpg.check(CLEAN_BODY, commits)
    assert v["guard_pass"] is False
    assert len(v["hits"]["body"]) == 0
    assert len(v["hits"]["commits"]) == 1
    assert v["hits"]["commits"][0]["commit_index"] == 1
    assert v["hits"]["commits"][0]["genre"] == "fix"
    assert "commit" in v["reason"]


def test_clean_commits_pass():
    # Commits with a non-closing prev: genre pass.
    commits = [
        "Grain: DEEP/lean -- prev: DEEP/lean #2159",
        "Fixes #100 (intended close, no prev: prefix -> NOT flagged)",
    ]
    v = vpg.check(CLEAN_BODY, commits)
    assert v["guard_pass"] is True


def test_intended_close_not_flagged():
    # A standalone `Fixes #100` / `Closes #456` (no `prev:` prefix) is an
    # INTENDED close and must NOT be flagged -- catalog-pr-hygiene HARD 4
    # relies on `Closes #N`. Only the prev: genre slot is in scope.
    v = vpg.check(
        "Grain: MED/refactor -- lane x:y\n\nThis PR fixes a bug. Fixes #100. Closes #456."
    )
    assert v["guard_pass"] is True


def test_all_canonical_genres_in_prev_pass():
    # Every canonical genre in a prev: field passes (no closing keyword).
    for genre in ("lean", "guard", "refactor", "tooling", "docs", "test",
                  "readme", "ledger", "qc", "training", "genai",
                  "notebook-python", "notebook-dotnet", "research-code"):
        v = vpg.check(f"prev: MED/{genre} #100")
        assert v["guard_pass"] is True, f"canonical genre {genre} must pass"


def test_both_body_and_commit_hits_aggregated():
    # Offending prev: in BOTH body and a commit -> both reported.
    body = "Grain: LIGHT/close -- prev: LIGHT/close #1"
    commits = ["prev: MED/fixes #2"]
    v = vpg.check(body, commits)
    assert v["guard_pass"] is False
    assert len(v["hits"]["body"]) == 1
    assert len(v["hits"]["commits"]) == 1


def test_empty_inputs_pass():
    assert vpg.check(None)["guard_pass"] is True
    assert vpg.check("")["guard_pass"] is True
    assert vpg.check("", [])["guard_pass"] is True
