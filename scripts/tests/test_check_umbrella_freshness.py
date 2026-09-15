#!/usr/bin/env python3
"""Tests for scripts/ci/check_umbrella_freshness.py (#11900).

The two founding fixtures are reconstructed from the cases #11900 measured:
  - #2874  "PR #2875 en review" + a path that no longer exists (the lake moved)
  - #7357  a decision request resolved in the first comment

Both had every door closed while their body still read as pending. The
positive control asserts the organ names exactly that situation.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from scripts.ci.check_umbrella_freshness import (  # noqa: E402
    assess,
    classify,
    classify_ref,
    extract_paths,
    extract_refs,
    main,
    missing_paths,
    render_text,
)


# --------------------------------------------------------------------------
# extraction
# --------------------------------------------------------------------------

def test_extract_refs_drops_self_reference_and_dedups():
    body = "See #14366 and #14366, plus #15035. This EPIC is #1453."
    assert extract_refs(body, 1453) == [14366, 15035]


def test_extract_refs_on_empty_body():
    assert extract_refs("", 1) == []
    assert extract_refs(None, 1) == []


def test_extract_refs_ignores_short_numbers():
    # The floor is 3 digits: it keeps #221/#833 while dropping "PR #12" noise.
    assert extract_refs("see #12 and #12345", 1) == [12345]
    assert extract_refs("cf. #221", 1) == [221]


def test_extract_paths_accepts_backticked_file_and_dir():
    body = "livre `docs/ledgers/12204-a3.md` et `MyIA.AI.Notebooks/RL/`"
    assert extract_paths(body) == [
        "docs/ledgers/12204-a3.md",
        "MyIA.AI.Notebooks/RL/",
    ]


def test_extract_paths_rejects_globs_and_prose():
    body = "scope `knot_lean/**` and `Some/Path{x,y}.lean` and `a/b`"
    assert extract_paths(body) == []


# --------------------------------------------------------------------------
# classification of one GitHub payload
# --------------------------------------------------------------------------

def test_classify_ref_issue_payload():
    ref = classify_ref(10, {"state": "open", "pull_request": None})
    assert ref == {"number": 10, "kind": "issue", "state": "OPEN", "merged": False}


def test_classify_ref_merged_pr_payload():
    ref = classify_ref(11, {
        "state": "closed",
        "pull_request": {"merged_at": "2026-06-13T00:00:00Z"},
    })
    assert ref["kind"] == "pr"
    assert ref["merged"] is True


def test_classify_ref_closed_pr_without_merge():
    ref = classify_ref(12, {"state": "closed", "pull_request": {}})
    assert ref["kind"] == "pr"
    assert ref["merged"] is False


def test_classify_ref_unfetchable_is_unknown_not_closed():
    # A network failure must never read as "closed" -- that would forge a red.
    assert classify_ref(13, None)["state"] == "UNKNOWN"


# --------------------------------------------------------------------------
# verdict rules
# --------------------------------------------------------------------------

def _issue(number: int, state: str) -> dict:
    return {"number": number, "kind": "issue", "state": state, "merged": False}


def test_saturated_when_every_child_issue_is_closed():
    """Positive control -- the situation #11900 measured on #2874 and #7357."""
    refs = [_issue(15037, "CLOSED"), _issue(15038, "CLOSED")]
    result = classify(refs, [])
    assert result["verdict"] == "SATURATED"
    assert result["child_open"] == 0


def test_fresh_when_one_child_is_open():
    refs = [_issue(15037, "CLOSED"), _issue(15047, "OPEN")]
    result = classify(refs, [])
    assert result["verdict"] == "FRESH"
    assert result["child_open"] == 1


def test_guard_mordes_when_a_closed_child_reopens():
    """Mutation control: the same fixture must flip once a door reopens."""
    closed = [_issue(15037, "CLOSED")]
    assert classify(closed, [])["verdict"] == "SATURATED"
    reopened = [_issue(15037, "OPEN")]
    assert classify(reopened, [])["verdict"] == "FRESH"


def test_pr_refs_alone_do_not_decide_a_verdict():
    """An EPIC citing only PRs has no child signal -- stay advisory."""
    refs = [{"number": 5, "kind": "pr", "state": "CLOSED", "merged": True}]
    result = classify(refs, [])
    assert result["verdict"] == "UNRESOLVED"
    assert "comments" in result["reason"]


def test_no_refs_at_all_is_unresolved_not_saturated():
    assert classify([], [])["verdict"] == "UNRESOLVED"


def test_unknown_refs_do_not_produce_saturated():
    refs = [classify_ref(13, None)]
    assert classify(refs, [])["verdict"] == "UNRESOLVED"


def test_missing_paths_are_warnings_never_a_verdict():
    refs = [_issue(15047, "OPEN")]
    result = classify(refs, ["MyIA.AI.Notebooks/GameTheory/conway_lean/"])
    assert result["verdict"] == "FRESH"
    assert any("conway_lean" in w for w in result["warnings"])


# --------------------------------------------------------------------------
# filesystem surface (#11900 surface 2: find, never ls)
# --------------------------------------------------------------------------

def test_missing_paths_reports_absent_and_accepts_present(tmp_path):
    (tmp_path / "docs").mkdir()
    (tmp_path / "docs" / "present.md").write_text("x", encoding="utf-8")
    absent = missing_paths(["docs/present.md", "docs/absent.md"], tmp_path)
    assert absent == ["docs/absent.md"]


def test_missing_paths_handles_directory_trailing_slash(tmp_path):
    (tmp_path / "RL").mkdir()
    assert missing_paths(["RL/"], tmp_path) == []
    assert missing_paths(["Gone/"], tmp_path) == ["Gone/"]


# --------------------------------------------------------------------------
# rendering + exit codes
# --------------------------------------------------------------------------

def test_render_text_names_the_saturated_action():
    result = classify([_issue(1, "CLOSED")], [])
    result.update({"number": 11900, "title": "t", "refs": []})
    text = render_text(result)
    assert "container" in text


def test_main_exits_one_on_saturated(monkeypatch, capsys):
    monkeypatch.setattr(
        "scripts.ci.check_umbrella_freshness.assess",
        lambda n, root, repo: {
            "number": n, "title": "t", "verdict": "SATURATED",
            "reason": "r", "refs": [], "warnings": [],
            "child_issues": 1, "child_open": 0,
        },
    )
    assert main(["11900", "--repo-root", "."]) == 1


def test_main_exits_zero_on_unresolved(monkeypatch):
    monkeypatch.setattr(
        "scripts.ci.check_umbrella_freshness.assess",
        lambda n, root, repo: {
            "number": n, "title": "t", "verdict": "UNRESOLVED",
            "reason": "r", "refs": [], "warnings": [],
            "child_issues": 0, "child_open": 0,
        },
    )
    assert main(["11900", "--repo-root", "."]) == 0


def test_assess_degrades_to_unknown_without_gh(monkeypatch, tmp_path):
    monkeypatch.setattr(
        "scripts.ci.check_umbrella_freshness._gh_json", lambda args: None)
    result = assess(11900, tmp_path, "jsboige/CoursIA")
    assert result["verdict"] == "unknown"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-v"]))
