#!/usr/bin/env python3
"""Wiring tests for pr-gate-rerun.yml after the event-path retirement (#11860).

The defect #11860 pins: the per-guard `workflow_run` trigger of
pr-gate-rerun.yml ran on a derived 76-workflow list, under a per-PR
`cancel-in-progress: true` concurrency group -- a self-cancellation storm.
Measured 2026-08-23 (window 06:06Z->06:58Z): 404 of the 784 repository CI runs
were `PR gate (re-aggregate)` (294 cancelled / 82 skipped / 24 pending /
0 success / 0 failure), and 476 runs sat queued for 16 runners. The event path
delivered zero verdicts.

The fix retires that trigger: pr-gate-rerun.yml is now a MANUAL
`workflow_dispatch` harness only (testing the re-run recipe by hand), and the
schedule-mutualized `pr-gate-stale-sweep.yml` is the sole re-aggregation path.
These tests fail if someone re-introduces the storm -- the pre-#11860 state --
and pin the pieces of the manual harness that must survive alongside it.

Run:
    python -m pytest scripts/tests/test_pr_gate_rerun_noop_guard.py
"""
from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-gate-rerun.yml"


def _load() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _on(d: dict) -> dict:
    """PyYAML parses the `on:` key as boolean `True`; read whichever is present."""
    return d.get(True) if isinstance(d.get(True), dict) else d.get("on", {})


def test_no_workflow_run_trigger_returns():
    """Le coeur de #11860 : pr-gate-rerun.yml ne doit PLUS trigger sur
    `workflow_run` -- c'est le generateur de la tempete (404 runs = 51,5 % de la
    CI, 0 verdict). Un retour au trigger evenementiel re-ouvre la famine."""
    assert "workflow_run" not in _on(_load()), (
        "workflow_run re-introduit dans pr-gate-rerun.yml ? le trigger "
        "evenementiel par-garde est la tempete #11860 -- retirez-le, la "
        "re-agregation schedule mutuee est pr-gate-stale-sweep.yml"
    )


def test_manual_dispatch_path_survives_the_retirement():
    """Le chemin workflow_dispatch (testing manuel de la recette de re-run,
    sans attendre un garde) doit rester present apres le retrait du trigger."""
    assert "workflow_dispatch" in _on(_load()), (
        "workflow_dispatch absent : le harnais manuel de re-run est coupe"
    )


def test_rerun_recipe_keeps_run_rerun():
    """La recette de re-run (issue #11519: `gh run rerun`, jamais un POST de
    verdict duplique) doit survenir dans le job -- c'est le mecanisme qui leve
    un verdict perime en place, dans la bonne suite de checks."""
    data = _load()
    assert data.get("permissions", {}).get("actions") == "write", (
        "permission actions:write absente -- `gh run rerun` echouerait"
    )
    assert "gh run rerun" in str(data.get("jobs", {})), (
        "la recette de re-run (#11519) a disparu du job reaggregate"
    )
