#!/usr/bin/env python3
"""Wiring tests for the no-op guard of pr-gate-rerun.yml (#11835).

The defect #11835 pins: the workflow-level concurrency key

    pr-gate-rerun-${{ ...pull_requests[0].number || ...inputs.pr_number || github.run_id }}

degenerates on every `workflow_run` triggered from `main` -- GitHub leaves
`workflow_run.pull_requests` empty there BY DESIGN, and `github.run_id` is
unique per run, so the group groups NOTHING. Measured 2026-08-19T19:20Z: 39
simultaneous runs of this workflow on a single main merge SHA, all no-ops
(`pull_requests: 0`), each occupying a runner slot just to `exit 0`.

As long as the key can fall back to `github.run_id`, the ONLY protection
against these no-op runner occupations is the job-level `if:` -- evaluated
by the Actions service BEFORE any runner allocation, so a skipped job costs
zero slots. These tests fail if that guard is removed (the pre-fix state),
and pin the two members of the original condition that must survive
alongside it (manual-dispatch path, cancelled-guard skip).

Run:
    python -m pytest scripts/tests/test_pr_gate_rerun_noop_guard.py
"""
from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-gate-rerun.yml"
JOB = "reaggregate"


def _load() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _job_if(wf: dict) -> str:
    return str(wf["jobs"][JOB].get("if", ""))


def test_degenerate_run_id_key_requires_pr_head_job_guard():
    """Le coeur de #11835 : tant que la cle de concurrence peut retomber sur
    github.run_id (fallback present), le job DOIT refuser de tourner sans PR
    dans le payload -- sinon chaque merge dans main paie ~39 slots de runner
    pour 39 skip mesurables."""
    wf = _load()
    group = str(wf.get("concurrency", {}).get("group", ""))
    assert "github.run_id" in group, (
        "la cle de concurrence n'a plus de fallback run_id ? si la cle est "
        "devenue stable par PR, retirez ce garde ET ce test ensemble"
    )
    cond = _job_if(wf)
    assert "github.event.workflow_run.pull_requests[0]" in cond, (
        "fallback github.run_id dans la cle + pas de garde pull_requests[0] "
        "au niveau job = chaque workflow_run sans PR (tous ceux de main, par "
        "conception) alloue un runner pour exit 0 (#11835 : 39 runs/merge)"
    )


def test_manual_dispatch_path_survives_the_guard():
    """Le membre `event_name != 'workflow_run'` preserve le chemin
    workflow_dispatch (testing): sans lui, le garde pull_requests[0] rendrait
    le dispatch manuel (inputs pr_number/head_sha) impossible a lancer."""
    assert "github.event_name != 'workflow_run'" in _job_if(_load()), (
        "chemin workflow_dispatch coupe : le if doit rester vrai hors workflow_run"
    )


def test_cancelled_guard_skip_survives_the_guard():
    """Le garde `conclusion != 'cancelled'` (payload SUPERSEDED head SHA) doit
    rester combine au garde pull_requests[0] -- les deux protegent des
    situations disjointes."""
    assert "github.event.workflow_run.conclusion != 'cancelled'" in _job_if(_load()), (
        "skip des guards cancelled absent du if: (rerun d'une tete supersedee)"
    )
