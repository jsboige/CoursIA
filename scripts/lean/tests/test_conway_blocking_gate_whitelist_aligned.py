#!/usr/bin/env python3
"""Contract test: the conway_lean blocking proof-integrity gate's allow-axioms
list is aligned with the gate's actual target closure (#8782 acceptance).

Context
-------
The blocking ``proof-integrity`` job in ``.github/workflows/lean-conway.yml``
runs the Level 3 axiom audit on ``Conway.KochenSpecker`` +
``Conway.FreeWillTheorem`` (sorry-free showcase modules). The historical
``allow-axioms`` list carried 18 names, ALL of them ``Conway.Life.*``-prefixed.
Inspecting the import closure of the two target modules:

* ``Conway.KochenSpecker`` imports ``Mathlib.Data.Real.Basic``,
  ``Mathlib.Data.Fin.Basic``, ``Mathlib.Tactic`` -- nothing from
  ``Conway.Life.*``.
* ``Conway.FreeWillTheorem`` imports ``Conway.KochenSpecker`` -- transitively
  the same.

The 18 ``Conway.Life.*`` names are therefore UNREACHABLE from the gate's
actual scope. The gate acquired them by historical inheritance (the
corresponding audit ran on a different target, HashlifeCorrectness, before
#8782 separated the two jobs), never by measurement of the showcase modules.

This test pins the alignment. It runs the audit script
(``scripts/lean/audit_conway_blocking_gate_whitelist.py``) and asserts that
every entry in the gate's allow-list is either (i) on the default whitelist
(by Lean's `LeanVerifier`: ``Classical.choice, propext, funext, Quot.lift,
Quot.mk, Quot.sound``) or (ii) reachable from the target closure. The
relaxation is the safety net: if a future contributor retargets the gate
and IT CAN reach a ``Conway.Life.*`` declaration, the test passes (the
allow-list is justified by the new scope); if the gate's scope shrinks back
to the showcase modules, the test fails (the list is the fossil).

How to recover a green test on this scope
-----------------------------------------
The blocking gate's scope IS the showcase modules, and the default whitelist
IS what ``scripts/lean/check_target_coverage.py`` says the gate inspects.
The reconciliation is to DROP the 18 entry list back to the default whitelist
(no ``allow-axioms:`` at all -- lean-axiom.yml applies the default). Or, if
the design intent for the showcase gate is to allow ``non-classical`` but
reject ``native_decide``, the default whitelist covers it (the showcase
modules don't emit ``native_decide``; they emit ``propext``, ``funext``,
``Quot.sound``, ``Classical.choice`` -- all in the default).

Run locally
-----------
pytest scripts/lean/tests/test_conway_blocking_gate_whitelist_aligned.py -v
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
AUDIT_SCRIPT = REPO / "scripts" / "lean" / "audit_conway_blocking_gate_whitelist.py"
CONWAY_WF = REPO / ".github" / "workflows" / "lean-conway.yml"


# Default whitelist that ``LeanVerifier.check_axioms`` applies when the
# workflow omits ``allow-axioms`` (or sets it to an empty list). Mirrored
# from ``MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/lean_server.py`` lines
# 636-650 -- a single source of truth would be ideal, but the script is
# meant to run without importing the verifier (which requires a Lean toolchain).
DEFAULT_WHITELIST = {
    "Classical.choice",
    "propext",
    "funext",
    "Quot.lift",
    "Quot.mk",
    "Quot.sound",
}


def _run_audit() -> dict:
    """Run the audit script and return its JSON summary."""
    result = subprocess.run(
        [sys.executable, str(AUDIT_SCRIPT), "--json"],
        cwd=str(REPO),
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert result.returncode == 0, f"audit failed: {result.stderr}"
    import json
    return json.loads(result.stdout)


def test_audit_script_exists():
    assert AUDIT_SCRIPT.is_file(), f"missing {AUDIT_SCRIPT}"


def test_audit_script_runs_clean():
    """Smoke test: the audit script must parse the workflow and produce a
    JSON report with the expected schema."""
    summary = _run_audit()
    assert "blocking_target_modules" in summary
    assert summary["blocking_target_modules"] == [
        "Conway.KochenSpecker",
        "Conway.FreeWillTheorem",
    ], (
        f"blocking gate target-modules drift: {summary['blocking_target_modules']}"
    )
    assert "fossil_count" in summary
    assert "reachable_count" in summary
    assert "default_count" in summary
    assert "fossil" in summary


def test_fossil_count_is_zero():
    """The blocking gate's allow-list must not contain entries that are
    unreachable from the gate's target closure (the 'vert hors-cible' of
    #8782). Each entry must be either on the default whitelist or on a
    reachable closure.

    Goal post-#8782: 0 fossil. The reconciliation PR (this c.8133 cycle) drops
    the 18 ``Conway.Life.*`` entries from the blocking gate's allow-list,
    leaving the default whitelist as the only permitted imports. The audit
    job (proof-integrity-audit) carries the 46-name allow-list for the
    HashlifeCorrectness scope.
    """
    summary = _run_audit()
    fossil = summary["fossil"]
    assert summary["fossil_count"] == 0, (
        f"blocking gate has {summary['fossil_count']} fossil allow-axioms "
        f"({len(fossil)}/{len(fossil) + summary['reachable_count'] + summary['default_count']} "
        f"entries unreachable from target closure). "
        f"First fossiled entry: {fossil[0]['name'] if fossil else 'none'}. "
        f"See #8782 (c.8133): a fossilised allow-list is a green-blind gate, "
        f"not a permission."
    )


def test_no_life_names_in_blocking_allow_list():
    """Regression: the 18 ``Conway.Life.*`` names that contaminated the
    blocking gate's allow-list must not return. The audit (proof-integrity-audit)
    is the home for ``Conway.Life.*`` allow-list management; the blocking
    gate stays Mathlib/classical-only.
    """
    summary = _run_audit()
    allow = summary["blocking_allow_axioms"]
    life_names = [n for n in allow if n.startswith("Conway.Life.")]
    assert not life_names, (
        f"blocking gate allow-list contains {len(life_names)} Conway.Life.* names -- "
        f"the fossil form of #8782. First: {life_names[0]}. "
        f"Remove them; the audit job has the canonical 46-name list."
    )


def test_blocking_gate_audit_job_still_there():
    """This regression test pins the audit job contract (locked c.8126 by
    ``test_proof_integrity_audit_wiring.py``); the c.8133 reconciliation MUST
    NOT remove the audit job while it cleans the blocking gate. Re-running
    the wiring test would catch a regression, but the c.8133 PR body cites
    this as a colocated contract.
    """
    assert CONWAY_WF.is_file()
    import yaml
    with CONWAY_WF.open(encoding="utf-8") as fh:
        doc = yaml.safe_load(fh)
    jobs = doc.get("jobs", {})
    assert "proof-integrity" in jobs, "blocking proof-integrity job removed"
    assert "proof-integrity-audit" in jobs, (
        "proof-integrity-audit job removed -- option (b) of #8782 must stay"
    )
    blocking = jobs["proof-integrity"]["with"]
    assert blocking.get("fail-on-sorry") is True
    assert "Conway.KochenSpecker" in blocking.get("target-modules", "")
    assert "Conway.FreeWillTheorem" in blocking.get("target-modules", "")
    audit = jobs["proof-integrity-audit"]["with"]
    assert audit.get("fail-on-sorry") is False
    assert "Conway.Life.HashlifeCorrectness" in audit.get("target-modules", "")
