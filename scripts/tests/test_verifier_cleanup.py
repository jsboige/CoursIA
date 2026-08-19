#!/usr/bin/env python3
"""Unit tests for the pure parts of verifier_cleanup.py (#10466 c.303).

The classification core (``is_registry``, the verdict logic) is exercised on
fixtures; the ``gh`` wiring is tested via dry-runs in CI. These fixtures
encode the verdicts measured firsthand over 9 cleanup cycles c.294-c.302:

  - #11266 / #11349 : single merged PR, silence after -> READY
  - #11162 umbrella: multiple merged PRs (multi-phase) -> AMBIGUOUS
  - #10918 : registry title "registre permanent" -> REGISTRY
  - #10600 : merged PR but body has post-merge comments -> AMBIGUOUS
  - IN_FLIGHT : OPEN PR referencing the issue -> IN_FLIGHT
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from verifier_cleanup import (  # noqa: E402
    is_registry, _REGISTRY_MARKERS, classify_one,
)


# --- is_registry (pure, no network) ----------------------------------------

def test_is_registry_title_starts_with_marker():
    assert is_registry("registre permanent : orphan-branch-scan cron") is True


def test_is_registry_title_contains_marker_as_word():
    assert is_registry("Some title with registre inside") is True
    assert is_registry("Registry of upstream advisories") is True
    assert is_registry("Audit permanent schedule") is True


def test_is_registry_false_on_normal_titles():
    # Regression: a regular cleanup / hygiene title must NOT be flagged.
    assert is_registry("fix(gate,#11044): CONDITIONAL_LIFT confond usage") is False
    assert is_registry("Add verifier_cleanup organ") is False


def test_is_registry_does_not_match_substring():
    # "registered" must NOT trigger "registre" / "registry" detection.
    # Substring match would over-fire on titles like "Registered user ..."
    assert is_registry("Registered user cleanup") is False
    assert is_registry("Re-registration of stale branches") is False


def test_registry_markers_constant_includes_three_markers():
    # The constant must include the three c.301-c.302 documented markers;
    # a fourth ("recurring-report") is forward-looking and not asserted here.
    for m in ("registre", "registry", "permanent"):
        assert m in _REGISTRY_MARKERS


# --- classify_one (network mocked at the function level) -------------------

class _FakeProc:
    def __init__(self, stdout="", returncode=0):
        self.stdout = stdout
        self.returncode = returncode


def _stub_subprocess(monkeypatch, mapping):
    """Subprocess stub: maps PREFIX (without leading ``gh``) -> stdout.

    The functions in ``verifier_cleanup`` build their gh calls as
    ``["gh", *args]`` and pass them to ``subprocess.run``. We monkeypatch
    ``subprocess.run`` so the mapping's keys describe the args AFTER the
    leading ``gh`` (which is what the call sites see). A call matches the
    first key whose (post-``gh``) prefix is a prefix of the call's args.
    Order matters: more specific prefixes must come first.

    Values can be either a JSON-serialisable object (returned via
    ``json.dumps``) or a raw string (returned verbatim).

    Calls without a matching prefix return ``returncode=1`` -- the function
    under test treats that as "no result", which is what we want for
    unrelated gh invocations.
    """
    import subprocess
    import json as _json

    keys = sorted(mapping.keys(), key=lambda k: -len(k))

    def fake_run(args, **kwargs):
        # Strip the leading "gh" the function under test prepends.
        tail = tuple(args[1:]) if args and args[0] == "gh" else tuple(args)
        for k in keys:
            if tail[: len(k)] == k:
                v = mapping[k]
                if isinstance(v, str):
                    return _FakeProc(stdout=v)
                return _FakeProc(stdout=_json.dumps(v))
        return _FakeProc(stdout="", returncode=1)

    monkeypatch.setattr(subprocess, "run", fake_run)


def _timeline_event(pr_number, merged_at):
    return {
        "event": "cross-referenced",
        "source": {
            "type": "issue",
            "issue": {
                "number": pr_number,
                "state": "closed",
                "pull_request": {"merged_at": merged_at},
            },
        },
    }


def test_classify_registry_short_circuits(monkeypatch):
    import verifier_cleanup
    # No gh calls expected -- is_registry fires first.
    rows = classify_one("o/r", {"number": 10918, "title": "registre permanent cron"})
    assert rows["verdict"] == "REGISTRY"


def test_classify_no_merged_pr_is_ambiguous(monkeypatch):
    import json
    mapping = {
        ("api", "repos/o/r/issues/9999/timeline", "--paginate"): [],
    }
    _stub_subprocess(monkeypatch, mapping)
    row = classify_one("o/r", {"number": 9999, "title": "fix something"})
    assert row["verdict"] == "AMBIGUOUS"
    assert "no merged PR" in row["reason"]


def test_classify_single_merged_pr_silent_is_ready(monkeypatch):
    mapping = {
        ("api", "repos/o/r/issues/11266/timeline", "--paginate"): [
            _timeline_event(11300, "2026-08-16T10:00:00Z"),
        ],
        ("search", "issues", "--json", "number"): [],
        ("issue", "view", "11266", "--repo", "o/r", "--json", "comments",
         "--jq", ".comments[-1].createdAt"): "",
    }
    _stub_subprocess(monkeypatch, mapping)
    row = classify_one("o/r", {"number": 11266, "title": "step mort workflow-path-filter-audit"})
    assert row["verdict"] == "READY"
    assert row["evidence"]["merged_prs"][0]["pr_number"] == 11300


def test_classify_open_pr_is_in_flight(monkeypatch):
    mapping = {
        ("api", "repos/o/r/issues/11175/timeline", "--paginate"): [
            _timeline_event(11250, "2026-08-16T08:00:00Z"),
        ],
        ("search", "issues", "--json", "number", "--limit", "20"): [
            {"number": 11260},
        ],
        ("issue", "view", "11175", "--repo", "o/r", "--json", "comments",
         "--jq", ".comments[-1].createdAt"): "",
    }
    _stub_subprocess(monkeypatch, mapping)
    row = classify_one("o/r", {"number": 11175, "title": "fix something"})
    assert row["verdict"] == "IN_FLIGHT"
    assert 11260 in row["evidence"]["open_prs"]


def test_classify_multi_phase_is_ambiguous(monkeypatch):
    # Mirrors #11162 umbrella: novelty probe + future Hashlife phase.
    mapping = {
        ("api", "repos/o/r/issues/11162/timeline", "--paginate"): [
            _timeline_event(11221, "2026-08-16T09:00:00Z"),
            _timeline_event(11280, "2026-08-17T11:00:00Z"),
        ],
        ("search", "issues", "--json", "number", "--limit", "20"): [],
        ("issue", "view", "11162", "--repo", "o/r", "--json", "comments",
         "--jq", ".comments[-1].createdAt"): "",
    }
    _stub_subprocess(monkeypatch, mapping)
    row = classify_one("o/r", {"number": 11162, "title": "umbrella novelty"})
    assert row["verdict"] == "AMBIGUOUS"
    assert "multi-phase" in row["reason"]


def test_classify_post_merge_comment_is_ambiguous(monkeypatch):
    # Mirrors #10600 c.297: merged PR landed, then a follow-up comment after.
    # The --jq invocation returns a SCALAR JSON string -- the stub must echo
    # it verbatim (with surrounding quotes) so ``_gh_json`` decodes a string.
    mapping = {
        ("api", "repos/o/r/issues/10600/timeline", "--paginate"): [
            _timeline_event(10799, "2026-08-13T07:00:00Z"),
        ],
        ("search", "issues", "--json", "number", "--limit", "20"): [],
        ("issue", "view", "10600", "--repo", "o/r", "--json", "comments",
         "--jq", ".comments[-1].createdAt"): '"2026-08-14T10:00:00Z"',
    }
    _stub_subprocess(monkeypatch, mapping)
    row = classify_one("o/r", {"number": 10600, "title": "workflow-path-filter-audit"})
    assert row["verdict"] == "AMBIGUOUS"
    assert "AFTER latest merge" in row["reason"]
