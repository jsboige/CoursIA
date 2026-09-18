#!/usr/bin/env python3
"""Wiring tests for the #16624 trigger fix on pr-gate.yml.

The defect #16624 pins, measured firsthand on #16574 (2026-09-18T01:28Z): a
stack PR retargeted onto `main` emits `edited` -- not in the default
pull_request activity types -- so the required `PR gate` check NEVER started,
and the PR sat BLOCKED with 14 green checks and an APPROVED review. The
remedy: listen to `edited` (and `ready_for_review`), with a job-level guard
so body/title edits skip the job instead of burning a waiter slot or faking a
green verdict. These tests fail if the trigger regresses to the default
types, or if the guard moves off the job level (an in-step early exit would
conclude SUCCESS on a SHA whose real verdict may be a stale red).
"""
from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-gate.yml"


def _load() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _on(d: dict) -> dict:
    """PyYAML parses the `on:` key as boolean `True`; read whichever is present."""
    return d.get(True) if isinstance(d.get(True), dict) else d.get("on", {})


def test_edited_and_ready_for_review_are_listened_to():
    """Demande 1 de #16624 : le retarget (edited) et la sortie de draft
    (ready_for_review) doivent etre des types ecoutes, aux cotes des types
    par defaut."""
    types = _on(_load())["pull_request"]["types"]
    for expected in ("opened", "synchronize", "reopened", "edited",
                     "ready_for_review"):
        assert expected in types, (
            f"type {expected!r} absent de pr-gate.yml : une PR retargetee ou "
            "passee ready ne verra jamais de verdict frais (#16624)"
        )


def test_branches_filter_still_main_only():
    """Le filtre branches: [main] est le contrat du check requis -- l'ajout des
    types ne doit pas l'alterer."""
    assert _on(_load())["pull_request"]["branches"] == ["main"]


def test_gate_job_guard_targets_base_edits_only():
    """La garde anti-rafale vit au NIVEAU JOB : un `edited` sans changement de
    base (titre/corps) doit produire un check-run `skipped` (non bloquant,
    n'efface aucun verdict), pas un SUCCESS calcule de zero."""
    gate = _load()["jobs"]["gate"]
    guard = gate.get("if", "")
    assert "github.event.action != 'edited'" in guard, (
        "la garde du job gate ne discriminate plus les edited sans retarget : "
        "chaque edition de titre/corps brulerait un slot coursia-waiter (#16624)"
    )
    assert "github.event.changes.base != null" in guard, (
        "la garde doit ne franchir les `edited` QUE sur un changement de base "
        "(github.event.changes.base) -- sinon tout edited est soit toujours "
        "agrege, soit jamais (#16624)"
    )
    # Le nom du check requis ne bouge pas (détache la branch protection).
    assert gate["name"] == "PR gate"


def test_pull_request_block_stays_unfiltered_for_the_canary():
    """Le bloc pull_request ne doit porter NI paths NI paths-ignore : c'est la
    propriete que derive_always_on_jobs (pr_gate.py, regle 8) lit pour tenir
    ce workflow hors canary de lui-meme et ce garde toujours-verdict. Les
    `types:` n'ont pas cet effet -- ce test l'ancrage."""
    pr_block = _on(_load())["pull_request"]
    assert "paths" not in pr_block and "paths-ignore" not in pr_block, (
        "un filtre paths sur pr-gate.yml desarmerait le verdict-sur-toute-PR "
        "(en-tete du workflow, regle 8 du canari)"
    )
