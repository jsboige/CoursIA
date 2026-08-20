#!/usr/bin/env python3
"""Unit tests for the PR gate stale-verdict sweep selector (#11862).

The defect #11862 pins: a `PR gate` whose conclusion is `cancelled`
(not `failure` / `timed_out` / `action_required`) was INVISIBLE to
`pr-gate-stale-sweep.yml`. GitHub does not read `cancelled` as a success,
the PR stayed BLOCKED, and the sweep filter -- whose RED set was
`{"failure", "timed_out", "action_required"}` -- had no entry to match.

The fix is asymmetric on purpose (#11862 body, point 2):

* `cancelled` joins the **gate-only** RED set. A gate `cancelled`
  means "verdict never rendered, re-aggregate". Same shape as the
  other three RED conclusions.
* `cancelled` does NOT join the **other-checks** GREEN set. A
  non-required `cancelled` is supersession (already absorbed by the
  per-name fold) or a real interruption we must NOT silently green-wash.

These tests pin both halves of that asymmetry, plus the three acceptance
cases from #11862:

1. Gate `cancelled` alone, every other check green -> selected.
2. Gate `cancelled` + another check RED -> NOT selected.
3. Non-required check `cancelled` superseded by a green rerun -> selected
   (the per-name fold keeps the rerun, the gate's RED conclusion is what
   gates selection).

A regression that adds `cancelled` to GREEN_OTHER will fail case 3 with a
wrong verdict: the cancelled check would NOT be folded by the per-name
fold, the others check would see a non-GREEN member, and the PR would be
spuriously skipped.

A regression that REMOVES `cancelled` from RED_GATE will fail case 1 with
a wrong verdict: the gate `cancelled` would not match the filter, the PR
would be spuriously skipped -- exactly the founding defect of #11862.

Run: python -m pytest scripts/tests/test_pr_gate_sweep_select.py
"""
import json
import sys
from io import StringIO
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pr_gate_sweep_select as sel  # noqa: E402

# --------------------------------------------------------------------------
# Constants pinned by these tests -- a regression here breaks the wiring.
# --------------------------------------------------------------------------

EXPECTED_RED_GATE = frozenset({"failure", "timed_out", "action_required", "cancelled"})
EXPECTED_GREEN_OTHER = frozenset({"success", "neutral", "skipped"})


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def _pr(number: int, *, gate_conclusion: str, others: list[dict] | None = None,
        gate_started_at: str = "2026-08-19T22:00:00Z",
        gate_status: str = "completed") -> dict:
    """Build a single PR dict in the shape ``runs.jsonl`` carries."""
    checks = [
        {
            "name": "PR gate",
            "status": gate_status,
            "conclusion": gate_conclusion,
            "started_at": gate_started_at,
        }
    ]
    for i, o in enumerate(others or []):
        checks.append({
            "name": o.get("name", f"check-{i}"),
            "status": o.get("status", "completed"),
            "conclusion": o.get("conclusion", "success"),
            "started_at": o.get("started_at", f"2026-08-19T22:00:0{i}Z"),
        })
    return {"number": number, "sha": f"sha-{number}", "fork": False, "checks": checks}


def _write_runs(tmp_path: Path, *prs: dict) -> Path:
    path = tmp_path / "runs.jsonl"
    with path.open("w", encoding="utf-8") as fh:
        for p in prs:
            fh.write(json.dumps(p) + "\n")
    return path


def _selected_numbers(runs_path: Path) -> list[int]:
    return [pr["number"] for pr in sel.select_stale_gate_prs(str(runs_path))]


# --------------------------------------------------------------------------
# Constants pin
# --------------------------------------------------------------------------


def test_red_gate_includes_cancelled():
    assert sel.RED_GATE == EXPECTED_RED_GATE, (
        f"RED_GATE drifted: {sorted(sel.RED_GATE)} vs {sorted(EXPECTED_RED_GATE)} -- "
        "this is the founding fix of #11862; do not drop `cancelled`."
    )


def test_green_other_does_not_include_cancelled():
    """The asymmetric half: a non-required check `cancelled` must NOT be
    green-washed. Otherwise case 3 below would silently select nothing."""
    assert sel.GREEN_OTHER == EXPECTED_GREEN_OTHER, (
        f"GREEN_OTHER drifted: {sorted(sel.GREEN_OTHER)} -- "
        "do NOT add `cancelled` here, see #11862 asymmetry."
    )
    assert "cancelled" not in sel.GREEN_OTHER, (
        "asymmetry violated: `cancelled` joined GREEN_OTHER -- "
        "non-required cancellations would be silently treated as green."
    )


# --------------------------------------------------------------------------
# Acceptance case 1: gate `cancelled` alone, others green -> selected.
# --------------------------------------------------------------------------


def test_case_1_gate_cancelled_alone_is_selected(tmp_path):
    pr = _pr(11852, gate_conclusion="cancelled", others=[
        {"name": "Analyze (python)", "conclusion": "success"},
        {"name": "CodeQL", "conclusion": "success"},
    ])
    runs = _write_runs(tmp_path, pr)
    assert _selected_numbers(runs) == [11852], (
        "the founding defect: a gate `cancelled` with all other checks green "
        "must be selected for re-aggregation. Regression here IS #11862."
    )


# --------------------------------------------------------------------------
# Acceptance case 2: gate `cancelled` + another check RED -> NOT selected.
# --------------------------------------------------------------------------


def test_case_2_gate_cancelled_with_other_red_not_selected(tmp_path):
    pr = _pr(99001, gate_conclusion="cancelled", others=[
        {"name": "Analyze (python)", "conclusion": "success"},
        {"name": "Notebook PR Validation", "conclusion": "failure"},
    ])
    runs = _write_runs(tmp_path, pr)
    assert _selected_numbers(runs) == [], (
        "an other-check RED must veto the selection, regardless of the "
        "gate's own verdict. Re-running a gate whose siblings are red "
        "would not unblock the PR and would burn a runner for nothing."
    )


# --------------------------------------------------------------------------
# Acceptance case 3: non-required `cancelled` superseded by green rerun.
# Verifies the per-name fold holds AND that the gate's own RED still gates.
# --------------------------------------------------------------------------


def test_case_3_non_required_cancelled_superseded_by_green_selected(tmp_path):
    """Two check-runs bearing the same name on a SHA: an older `cancelled`
    and a newer `success`. The per-name fold keeps the newer success; the
    filter then sees one completed-green check, and the gate's
    `failure` selects the PR."""
    pr_number = 99100
    pr = {
        "number": pr_number,
        "sha": f"sha-{pr_number}",
        "fork": False,
        "checks": [
            # Gate leg is RED (failure here, but cancelled would behave the
            # same -- the gate test cares about the gate's verdict).
            {
                "name": "PR gate",
                "status": "completed",
                "conclusion": "failure",
                "started_at": "2026-08-19T22:30:00Z",
            },
            # Older cancelled rerun for Analyze (python).
            {
                "name": "Analyze (python)",
                "status": "completed",
                "conclusion": "cancelled",
                "started_at": "2026-08-19T22:00:00Z",
            },
            # Newer success rerun for Analyze (python).
            {
                "name": "Analyze (python)",
                "status": "completed",
                "conclusion": "success",
                "started_at": "2026-08-19T22:35:00Z",
            },
        ],
    }
    runs = _write_runs(tmp_path, pr)
    assert _selected_numbers(runs) == [pr_number], (
        "the per-name fold MUST keep the latest run; a non-required "
        "`cancelled` superseded by a green rerun must NOT veto the "
        "selection. This is the half of the asymmetry case 1 alone "
        "cannot prove."
    )


# --------------------------------------------------------------------------
# Regression guards
# --------------------------------------------------------------------------


def test_no_gate_leg_is_not_selected(tmp_path):
    """Absent gate -> pr-gate-missing-advisory.yml owns the case."""
    pr = _pr(99200, gate_conclusion="success", others=[
        {"name": "CodeQL", "conclusion": "success"},
    ])
    # Drop the gate leg entirely to model the "no PR gate has ever run"
    # state.
    pr["checks"] = [c for c in pr["checks"] if c["name"] != "PR gate"]
    runs = _write_runs(tmp_path, pr)
    assert _selected_numbers(runs) == [], (
        "absent `PR gate` must NOT be selected by this sweep -- that case "
        "belongs to pr-gate-missing-advisory.yml."
    )


def test_pending_other_check_blocks_selection(tmp_path):
    """If any non-required check is still queued, the gate may be
    legitimately waiting. Re-aggregating would burn a verdict on the
    same incomplete set."""
    pr = _pr(99300, gate_conclusion="cancelled", others=[
        {"name": "Analyze (python)", "conclusion": "success"},
        {"name": "CodeQL", "status": "in_progress", "conclusion": None},
    ])
    runs = _write_runs(tmp_path, pr)
    assert _selected_numbers(runs) == [], (
        "an in-progress non-required check must veto the selection. "
        "Same protection as case 2, different mechanism."
    )


def test_module_runs_against_real_runs_jsonl(tmp_path, capsys):
    """End-to-end shape: ``python -m ci.pr_gate_sweep_select <runs.jsonl>``
    must emit ``number sha fork`` triples, one per selected PR, matching
    the format the workflow expects on stdout."""
    pr = _pr(99400, gate_conclusion="cancelled", others=[
        {"name": "Analyze (python)", "conclusion": "success"},
    ])
    runs = _write_runs(tmp_path, pr)
    rc = sel._main(["prog", str(runs)])
    assert rc == 0
    out = capsys.readouterr().out.strip().splitlines()
    assert out == ["99400 sha-99400 false"], (
        f"unexpected stdout shape: {out!r} -- the workflow pipes this into "
        "`while read`; the format must stay `number sha fork`."
    )


def test_module_reports_usage_on_bad_args(capsys):
    rc = sel._main(["prog"])
    assert rc == 2
    err = capsys.readouterr().err
    assert "usage" in err
