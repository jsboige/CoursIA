"""Unit tests for scripts/lane_claim_epic_wide.py (#12156 piste 1).

No network: the analysis functions run on synthetic `gh issue view` payloads.
The parity test replays the SAME payloads through `check_lane_claim._run_check`
and asserts this organ never disagrees with the reference verdict.
"""
from __future__ import annotations

import contextlib
import io
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import check_lane_claim as clc  # noqa: E402
import lane_claim_epic_wide as org  # noqa: E402

NOW = datetime(2026, 9, 11, 17, 0, tzinfo=timezone.utc)
FRESH = "2026-09-11T10:00:00Z"      # 7 h before NOW
OLD = "2026-09-01T10:00:00Z"        # 241 h before NOW (> 48 h threshold)

UNSCOPED = "[CLAIMED] lane myia-po-2025:CoursIA — tranche 1 du chantier"
SCOPED = ("[CLAIMED] lane myia-po-2025:CoursIA -- paths: "
          "MyIA.AI.Notebooks/GameTheory/** -- tranche A (2026-09-11T10:00Z)")
OTHER_LANE_UNSCOPED = "[CLAIMED] lane myia-po-2026:CoursIA — confluence"
DEAD_GLOB_SCOPED = (
    "[CLAIMED] lane myia-po-2025:CoursIA -- paths: "
    "MyIA.AI.Notebooks/ZZ-NoSeries-99/Nonexistent-*.ipynb")
PARTIALLY_DEAD_SCOPED = (
    "[CLAIMED] lane myia-po-2025:CoursIA -- paths: "
    "MyIA.AI.Notebooks/GameTheory/**, "
    "MyIA.AI.Notebooks/ZZ-NoSeries-99/Nonexistent-*.ipynb")


def comment(body: str, created: str = FRESH) -> dict:
    return {"id": 1, "author": {"login": "jsboige"}, "createdAt": created,
            "body": body, "url": "https://example.invalid/c1"}


def issue(comments, title="EPIC chantier", labels=("EPIC",)) -> dict:
    return {"number": 42, "title": title,
            "labels": [{"name": l} for l in labels],
            "comments": comments}


def test_unscoped_other_lane_locks_epic():
    verdict, claims = org.classify(issue([comment(UNSCOPED)]), now=NOW)
    assert verdict == "locked"
    assert [c["lane"] for c in claims] == ["myia-po-2025:CoursIA"]
    assert claims[0]["age_hours"] == 7.0


def test_scoped_claim_does_not_lock():
    verdict, claims = org.classify(issue([comment(SCOPED)]), now=NOW)
    assert verdict == "clear" and claims == []


def test_stale_claim_does_not_lock():
    # The exact case measured on #12156: 260 h-old claim, reprise allowed.
    verdict, _ = org.classify(issue([comment(UNSCOPED, OLD)]), now=NOW)
    assert verdict == "clear"


def test_non_epic_issue_never_locks():
    # Epic-wide is the CORRECT default on a unitary issue (#12156's own words).
    payload = issue([comment(UNSCOPED)], title="Unitaire", labels=("bug",))
    assert org.classify(payload, now=NOW)[0] == "clear"


def test_epic_title_prefix_is_umbrella_too():
    payload = issue([comment(UNSCOPED)], title="[EPIC][ICT] Chantier", labels=())
    assert org.classify(payload, now=NOW)[0] == "locked"


def test_mixed_scoped_and_unscoped_does_not_lock():
    # all() semantics of _run_check: one scoped claim means the umbrella is
    # NOT held epic-wide -- the scoped lane leaves the rest open.
    payload = issue([comment(SCOPED), comment(OTHER_LANE_UNSCOPED)])
    assert org.classify(payload, now=NOW)[0] == "clear"


def test_released_claim_does_not_lock():
    payload = issue([comment(UNSCOPED),
                     comment("[RELEASED] lane myia-po-2025:CoursIA", FRESH)])
    assert org.classify(payload, now=NOW)[0] == "clear"


def test_claim_by_audit_lane_itself_is_not_an_other():
    payload = issue([comment("[CLAIMED] lane advisory:epic-wide-audit — test")])
    assert org.classify(payload, now=NOW)[0] == "clear"


def test_two_unscoped_lanes_both_reported():
    payload = issue([comment(UNSCOPED), comment(OTHER_LANE_UNSCOPED)])
    verdict, claims = org.classify(payload, now=NOW)
    assert verdict == "locked"
    assert [c["lane"] for c in claims] == [
        "myia-po-2025:CoursIA", "myia-po-2026:CoursIA"]


def test_dead_glob_scope_locks_epic_wide():
    # The #15062 shape: a paths: clause whose EVERY glob matches zero tracked
    # files is a BROKEN claim, not a permissive one (#10958) -- lifted to
    # epic-wide. This is the divergence the original organ had: without the
    # tracked walk the witness is absent and the predicate degrades to False.
    tracked = ["scripts/check_lane_claim.py"]
    verdict, claims = org.classify(issue([comment(DEAD_GLOB_SCOPED)]),
                                   now=NOW, tracked=tracked)
    assert verdict == "locked"
    assert [c["lane"] for c in claims] == ["myia-po-2025:CoursIA"]


def test_partially_dead_scope_stays_scoped():
    # At least one LIVE glob: the lock is real on its live part, the claim is
    # not lifted (len(empty_scope) < len(paths)).
    tracked = ["MyIA.AI.Notebooks/GameTheory/GameTheory-01-Introduction.ipynb"]
    verdict, _ = org.classify(issue([comment(PARTIALLY_DEAD_SCOPED)]),
                              now=NOW, tracked=tracked)
    assert verdict == "clear"


# ---- human retraction (#14307) -------------------------------------------


def test_human_unlabeled_sticks():
    ev = org.human_retraction([
        {"event": "labeled", "actor": "jsboige", "created_at": "2026-09-10T01:00:00Z"},
        {"event": "unlabeled", "actor": "jsboige", "created_at": "2026-09-11T01:00:00Z"},
    ])
    assert ev is not None and ev["event"] == "unlabeled"


def test_human_repose_hands_control_back():
    ev = org.human_retraction([
        {"event": "unlabeled", "actor": "jsboige", "created_at": "2026-09-10T01:00:00Z"},
        {"event": "labeled", "actor": "jsboige", "created_at": "2026-09-11T01:00:00Z"},
    ])
    assert ev is None


def test_bot_events_are_not_verdicts():
    ev = org.human_retraction([
        {"event": "unlabeled", "actor": "github-actions[bot]",
         "created_at": "2026-09-11T01:00:00Z"},
    ])
    assert ev is None


# ---- comment plumbing -----------------------------------------------------


def test_comment_body_names_lanes_and_marker():
    body = org.comment_body(
        [{"lane": "myia-po-2025:CoursIA", "claimed_at": FRESH,
          "age_hours": 7.0, "url": "u", "by": "jsboige"}], org.LABEL_DEFAULT)
    assert org.MARKER in body
    assert "myia-po-2025:CoursIA" in body
    assert "paths:" in body  # the scoped form is what the comment recalls


def test_has_marker_comment():
    assert org.has_marker_comment({"comments": [{"body": org.comment_body(
        [{"lane": "x", "claimed_at": FRESH, "age_hours": 1, "url": "u",
          "by": "a"}], org.LABEL_DEFAULT)}]})
    assert not org.has_marker_comment({"comments": [{"body": "hello"}]})


def test_has_label():
    assert org.has_label({"labels": [{"name": "EPIC"}, {"name": org.LABEL_DEFAULT}]},
                         org.LABEL_DEFAULT)
    assert not org.has_label({"labels": [{"name": "EPIC"}]}, org.LABEL_DEFAULT)


# ---- PARITY with the reference organ (the anti-drift contract) ------------


def _run_check_json(payload: dict) -> dict:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        clc._run_check(payload, org.AUDIT_LANE, stale_threshold=48.0, now=NOW)
    all_lines = buf.getvalue().splitlines()
    starts = [i for i, l in enumerate(all_lines) if l.strip().startswith("{")]
    assert starts, "expected a JSON summary from _run_check"
    obj, _end = json.JSONDecoder().raw_decode("\n".join(all_lines[starts[0]:]))
    return obj


def test_parity_with_run_check():
    # The reference walks the REAL repo (git ls-files at cwd) to attach the
    # #10958 witness; the organ must be fed the SAME walk. A local git call,
    # no network -- and the cases below choose paths that are deterministic
    # against this repo's content (GameTheory/** is live; ZZ-NoSeries-99/**
    # matches nothing).
    tracked = clc._git_tracked_files()
    assert tracked, "expected a non-empty git ls-files walk in this repo"
    cases = [
        issue([comment(UNSCOPED)]),                       # locked
        issue([comment(SCOPED)]),                         # clear: scoped
        issue([comment(UNSCOPED, OLD)]),                  # clear: stale
        issue([comment(SCOPED), comment(OTHER_LANE_UNSCOPED)]),  # clear: mixed
        issue([comment(UNSCOPED)], title="Unitaire", labels=("bug",)),  # n/a
        issue([comment(UNSCOPED), comment(OTHER_LANE_UNSCOPED)]),       # locked x2
        issue([comment(DEAD_GLOB_SCOPED)]),               # locked: dead-glob lift
        issue([comment(PARTIALLY_DEAD_SCOPED)]),          # clear: partially dead
    ]
    for payload in cases:
        reference = _run_check_json(payload)["epic_wide_on_umbrella"]
        mine = bool(org.locking_claims(payload, stale_threshold=48.0, now=NOW,
                                       tracked=tracked))
        assert mine == reference, (
            f"parity drift on {payload['title']!r} labels="
            f"{payload['labels']}: organ={mine} reference={reference}")
