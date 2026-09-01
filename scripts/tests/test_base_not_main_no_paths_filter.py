#!/usr/bin/env python3
"""Lock test for the base-not-main organ (#13232 + #13193 + #14057).

L'organe vit depuis #14057 (Vague 2 tranche 1, patron #13384) dans
``.github/workflows/always-on-metadata-guards.yml`` ; le fichier source
``base-not-main-advisory.yml`` reste DORMANT (declencheur pull_request
retire, job conserve verbatim pour la tracabilite).

The organ reads PR-level metadata via the ``gh`` API ONLY
(``scripts/base_not_main.py`` uses ``gh pr view --json baseRefName,title``)
and never inspects the working tree. Its verdict therefore depends on
PR METADATA, not the DIFF. Per the criterion ai-01 wrote in #13232:

    > Le verdict du garde depend-il du DIFF, ou des METADONNEES de la PR ?
    > - diff (regression, translation, ...)            -> paths: legitime
    > - metadonnees (base ref, body, labels, auteur)   -> AUCUN paths:

A ``paths:`` filter on a metadonnee-dependant workflow silently turns
the check into a no-op on the very PRs that need it most: ones that do
NOT touch the listed files. This test reads the UMBRELLA's YAML and
asserts no ``paths:`` block is present under ``on.pull_request``, and
that the union trigger types cover the five events the advisory must
react to. If a future editor re-adds one, the test fails.

Run::

    python -m pytest scripts/tests/test_base_not_main_no_paths_filter.py -v
"""
from __future__ import annotations

import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "always-on-metadata-guards.yml"


def _load_workflow() -> dict:
    """Load the workflow YAML without running any pre-commit hook.

    PyYAML 6.x is the dependency floor; older versions don't round-trip
    GitHub Actions YAML cleanly (anchors, multi-doc)."""
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def test_no_paths_filter_under_pull_request():
    """The workflow MUST NOT define ``paths:`` under ``on.pull_request``.

    The mechanism it gates (base != main) is PR-level metadata. A
    ``paths:`` filter would desarme the check on every PR that does
    not touch exactly the listed files -- the very surface the check
    is supposed to scan. Cf #13232 criterion + #13193 fix."""
    wf = _load_workflow()
    pr_section = wf.get(True, {}).get("pull_request") if True in wf else wf.get("on", {}).get("pull_request")  # noqa: E501
    assert pr_section is not None, "workflow missing on.pull_request"

    # PyYAML may normalize "on" to True (YAML 1.1 boolean) on some inputs.
    on_block = wf["on"] if "on" in wf else (wf[True] if True in wf else {})
    pr_block = on_block.get("pull_request", {})

    assert "paths" not in pr_block, (
        f"always-on-metadata-guards.yml (umbrella de l'organe base-not-main "
        f"depuis #14057) MUST NOT carry paths: under "
        f"on.pull_request (decision ai-01 #13232, 2026-08-27). "
        f"Organ reads PR METADATA only via gh api (baseRefName, "
        f"title). Got: {sorted(pr_block.keys())}"
    )


def test_pull_request_trigger_still_typed():
    """Whatever reduction we apply, the ``types:`` block must remain
    populated so synchronize/edited still trigger a re-render of the
    advisory. Removing paths: must NOT silently drop the surface."""
    wf = _load_workflow()
    on_block = wf["on"] if "on" in wf else (wf[True] if True in wf else {})
    pr_block = on_block.get("pull_request", {})
    assert "types" in pr_block, "on.pull_request.types MUST stay populated"
    types = pr_block["types"]
    assert isinstance(types, list) and types, "types must be a non-empty list"
    # The full list ai-01 requires for the gate to react to body edits.
    expected = {"opened", "reopened", "synchronize", "edited", "ready_for_review"}
    assert expected.issubset(set(types)), (
        f"missing required trigger types: {expected - set(types)}"
    )


def test_signature_locked_in_workflow_header():
    """A grep-level docstring on the workflow keeps the rationale visible
    to the next editor who wonders why there's no paths: filter."""
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "METADONNEES" in text or "METADATA" in text, (
        "the rationale for no paths: filter must be discoverable in "
        "the workflow file itself (decision ai-01 #13232)"
    )


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
