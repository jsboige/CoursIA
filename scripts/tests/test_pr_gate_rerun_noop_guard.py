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


# ---------------------------------------------------------------------------
# #16624 -- la jambe gate-absent et le message de skip VEridique
# ---------------------------------------------------------------------------


def test_false_skip_message_is_gone():
    """Demande 2 de #16624 : l'ancien skip affirmait « the gate will run on its
    own » pour une tete sans run pull_request -- FAUX pour la population
    retarget (aucun push, aucun synchronize, et un close/reopen bot est inert
    par anti-recursion). Le message doit rester absent du workflow."""
    assert "the gate will run on its own" not in WORKFLOW.read_text(encoding="utf-8"), (
        "le message de skip mensonger est de retour : une tete sans run "
        "pull_request ne verra JAMAIS le gate partir seule (retarget, #16624)"
    )


def test_absent_leg_posts_via_pr_gate_py_only():
    """La jambe gate-absent agrege via scripts/pr_gate.py --post-check-run --
    le verdict est CALCULE par le meme moteur que le gate reel, jamais asserte
    -- et la permission checks:write nécessaire au POST est déclarée."""
    data = _load()
    assert data.get("permissions", {}).get("checks") == "write", (
        "checks:write absente -- le POST du verdict sur la tete de PR "
        "echouerait silencieusement (#16624)"
    )
    jobs = data.get("jobs", {})
    assert "aggregate_absent" in jobs, (
        "la jambe aggregate_absent manque : la population gate-absent n'a "
        "rien a re-run et rien ne la rattrape (#16624 demande 3)"
    )
    text = str(jobs["aggregate_absent"])
    assert "--post-check-run" in text and "scripts/pr_gate.py" in text, (
        "la jambe absent doit passer par pr_gate.py --post-check-run (verdict "
        "calcule), pas par un verdict asserte"
    )


def test_absent_leg_never_posts_beside_an_existing_gate_check_run():
    """Garde structurale anti-jumeau (#11519) : la route aggregate_absent
    n'est prise QUE si aucun check-run « PR gate » n'existe deja sur la tete.
    Sans elle, un POST pourrait se poser a cote d'un verdict existant et
    l'AND de GitHub garderait la PR bloquee. #17680 : la route vit desormais
    dans scripts/ci/pr_gate_route.py -- la garde a demenage avec elle."""
    route_script = (
        Path(__file__).resolve().parents[2] / "scripts" / "ci" / "pr_gate_route.py"
    )
    assert "refusing to POST beside it (#11519 twin)" in route_script.read_text(
        encoding="utf-8"
    ), (
        "la garde anti-jumeau du resolve a disparu du script de route : la "
        "jambe absent pourrait creer le doublon que #11519 documente"
    )
    # Le workflow doit bien appeler CE script (sinon la garde testee n'est
    # pas celle qui s'execute).
    assert "scripts/ci/pr_gate_route.py" in str(_load().get("jobs", {})), (
        "le resolve n'appelle plus pr_gate_route.py : la garde anti-jumeau "
        "testee dans le script n'est pas celle qui tourne"
    )


def test_resolve_routes_rerun_and_absent():
    """La structure a trois jambes : resolve decide, rerun rejoue l'original,
    aggregate_absent POSTe sur une tete orpheline -- les deux dernieres
    bornees par needs.resolve.outputs.action."""
    data = _load()
    jobs = data.get("jobs", {})
    assert "resolve" in jobs and "rerun" in jobs
    assert jobs["rerun"].get("if") == "needs.resolve.outputs.action == 'rerun'"
    assert jobs["aggregate_absent"].get("if") == (
        "needs.resolve.outputs.action == 'aggregate_absent'"
    )
