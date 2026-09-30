#!/usr/bin/env python3
"""Wiring tests pinning the #16624 revision on pr-gate.yml.

The original defect #16624 pins, measured firsthand on #16574
(2026-09-18T01:28Z): a stack PR retargeted onto `main` emits `edited` -- not
in the default pull_request activity types -- so the required `PR gate` check
NEVER started, and the PR sat BLOCKED with 14 green checks and an APPROVED
review. The first fix listened to `edited` behind a job-level guard; ai-01's
CHANGES_REQUESTED (2026-09-18T06:33Z) showed that guard to be a permissive
path: this job IS the required check (`name: PR gate`, job-managed check-run),
so a skipped job emits a SKIPPED same-named check-run on the head SHA -- under
latest-wins the newest verdict for the name, and a required check concluded
`skipped` counts as passing, so editing the body of a red PR would unblock it.

The revision: `edited` stays OUT of the types. The only semantics that cannot
mutate a verdict on a title/body edit is NO RUN AT ALL; the retarget
population is caught from the outside by the pr-gate-stale-sweep.yml
gate-absent leg (label + comment + auto-dispatch of pr-gate-rerun.yml
`aggregate_absent`, capped per pass). These tests fail if anyone re-adds
`edited` (or any guard emitting a verdict-shaped check-run on edits).
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


def test_edited_stays_out_of_the_types():
    """ai-01 CHANGES_REQUESTED 2026-09-18T06:33Z : ecouter `edited` n'a pas de
    forme sure ici. Le job gate EST le check requis (check-run gere par le
    job) : un garde job-level emet un check-run `skipped` homonyme -- en
    latest-wins c'est le verdict le plus recent du nom, et un check requis
    `skipped` compte comme passant, donc editer le corps d'une PR rouge la
    debloquerait. Le re-ajouter sans avoir resolu CE point est une regression
    permissive."""
    types = _on(_load())["pull_request"]["types"]
    assert "edited" not in types, (
        "`edited` est de retour dans les types de pr-gate.yml : chaque edition "
        "de titre/corps emetra un check-run verdict-shaped sur la tete (skipped "
        "via garde job-level, ou success via early-exit) -- le rattrapage "
        "retarget vit dans le stale-sweep gate-absent, pas ici (#16624 rev.)"
    )


def test_default_types_and_ready_for_review_are_listened_to():
    """Les types par defaut restent explicites, et `ready_for_review` reste :
    draft -> ready n'emet aucun push (pas de synchronize), donc sans lui le
    verdict `opened` du draft serait le dernier que la PR aurait jamais."""
    types = _on(_load())["pull_request"]["types"]
    for expected in ("opened", "synchronize", "reopened", "ready_for_review"):
        assert expected in types, (
            f"type {expected!r} absent de pr-gate.yml : une PR passee ready ne "
            "verrait jamais de verdict frais (#16624)"
        )


def test_branches_filter_still_main_only():
    """Le filtre branches: [main] est le contrat du check requis -- l'ajout des
    types ne doit pas l'alterer."""
    assert _on(_load())["pull_request"]["branches"] == ["main"]


def test_gate_job_carries_no_edit_guard():
    """Le job gate ne porte AUCUNE garde `if` discriminant les `edited` : toute
    forme de garde emet un check-run sous le nom du check requis (skipped si
    job-level, success si early-exit in-job) -- les deux sont verdict-shaped.
    La population edited est traitee HORS de ce workflow par le stale-sweep
    gate-absent (voir le commentaire du trigger)."""
    gate = _load()["jobs"]["gate"]
    # Le nom du check requis ne bouge pas (detache la branch protection).
    assert gate["name"] == "PR gate"
    assert "if" not in gate, (
        f"garde `if` inattendue sur le job gate ({gate['if']!r}) : une garde "
        "sur ce job emet un check-run sous le nom du check requis -- skipped "
        "ou success, les deux mutent le verdict (ai-01 2026-09-18T06:33Z)"
    )


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
