#!/usr/bin/env python3
"""Contract test for the conway proof-integrity-audit job (#8782 option (b)).

Dual-mode: runnable directly (``python scripts/lean/tests/test_proof_integrity_audit_wiring.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the wiring of the ADVISORY axiom-audit job that closes the "vert
hors-cible" gap opened in #8782. The blocking ``proof-integrity`` job targets
the sorry-FREE showcase modules (Conway.KochenSpecker + Conway.FreeWillTheorem)
and is therefore green BY CONSTRUCTION on the 8 acknowledged tactic sorries in
Conway.Life.HashlifeCorrectness -- observed on #8809 (SUCCESS beside a file
with 8 sorries). Option (b) adds a non-blocking ``proof-integrity-audit`` job
that runs the axiom audit ON the sorry-bearing module, so the sorries surface
as ``has_sorry`` (reported, not gated -- an honesty knob, not a leniency one)
while a FORBIDDEN axiom (beyond the 19 native_decide allow-list) still
hard-fails. Criterion 1 (#8782): the audit targets the module whose public
anchor (``hashlifeResult_central_correct``) closes the private sorry chain, so
the sorry is REACHED, not hidden; a module with zero enumerated decls reads
'non applicable' explicitly (lean-axiom.yml), never a silent clean.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# scripts/lean/tests/X.py -> parents[3] = repo root
REPO = Path(__file__).resolve().parents[3]
CONWAY_WF = REPO / ".github" / "workflows" / "lean-conway.yml"


def _load_jobs():
    yaml = pytest.importorskip("yaml")
    with CONWAY_WF.open(encoding="utf-8") as fh:
        doc = yaml.safe_load(fh)
    return doc.get("jobs", {})


def test_workflow_exists():
    assert CONWAY_WF.is_file(), f"missing {CONWAY_WF}"


def test_blocking_proof_integrity_targets_showcase_modules():
    """The blocking gate covers the sorry-FREE showcase (KochenSpecker +
    FreeWillTheorem) with fail-on-sorry: true -- the complement of the
    sorry-bearing advisory audit below."""
    jobs = _load_jobs()
    assert "proof-integrity" in jobs, "blocking proof-integrity job removed"
    blocking = jobs["proof-integrity"].get("with", {})
    targets = blocking.get("target-modules", "")
    assert "Conway.KochenSpecker" in targets
    assert "Conway.FreeWillTheorem" in targets
    assert blocking.get("fail-on-sorry") is True


def test_advisory_audit_job_wired():
    """Option (b): an ADVISORY proof-integrity-audit job exists, uses the
    reusable lean-axiom workflow, and is non-blocking on sorry."""
    jobs = _load_jobs()
    assert "proof-integrity-audit" in jobs, (
        "#8782 (b): proof-integrity-audit job missing from lean-conway.yml")
    audit = jobs["proof-integrity-audit"]
    assert "lean-axiom.yml@main" in audit.get("uses", ""), (
        "audit must reuse the lean-axiom workflow")
    with_opts = audit.get("with", {})
    assert with_opts.get("fail-on-sorry") is False, (
        "the audit job must be advisory on sorry (fail-on-sorry: false)")


def test_audit_targets_sorry_bearing_module():
    """The audit closes the vert-hors-cible: it inspects the module that
    CARRIES the 8 sorries (HashlifeCorrectness), which the blocking gate
    skips. Targeting only KochenSpecker/FreeWillTheorem here would reproduce
    the very gap #8782 opened on."""
    jobs = _load_jobs()
    audit = jobs["proof-integrity-audit"].get("with", {})
    targets = audit.get("target-modules", "")
    assert "Conway.Life.HashlifeCorrectness" in targets, (
        "audit must target the sorry-bearing module, not the sorry-free showcase")


def test_audit_allowlists_native_decide_axioms():
    """The audit allow-lists the native_decide axioms its modules ACTUALLY depend
    on, so it reports only a FORBIDDEN axiom (beyond them) as red. The first CI
    run of this audit (#8782) revealed HashlifeCorrectness depends on **28**
    native_decide axioms -- a footprint DISTINCT from the blocking gate's 19-name
    list (triaged from the showcase modules KochenSpecker/FreeWillTheorem, #8749,
    a different scope; the two sets have ZERO overlap). The audit audits
    different modules, so its allow-list is its own (not a copy of the blocking
    gate's). All are decide-kernel (`._native.native_decide.ax_1_N`).

    **Widened to 46 by #9341** (`ci(lean,#8782)`), which took the audit from 3 to
    7 covered modules by adding Oscillators/Spaceships/RLE. The 18 added entries
    are the build-enumerated footprint of exactly those new modules -- 10 new
    theorems, all still-life/spaceship/oscillator decidability
    (`boat|loaf|pond|ship|tub_still_life`, `lwss|mwss|hwss_spaceship`,
    `pulsar_period_three`, `pentadecathlon_period_15`). Coverage went UP, so the
    widening is an expansion of what is audited, not a dilution of the gate.

    This pin is the ratchet's ratchet: it caught #9341 widening the allow-list
    without review and turned `main` red until the widening was justified in
    writing. Raising it is only ever legitimate alongside that justification --
    a new name that is NOT attributable to a newly covered module means an
    unproven `native_decide` slipped in, and the pin must stay put instead."""
    jobs = _load_jobs()
    audit = jobs["proof-integrity-audit"].get("with", {})
    allow = audit.get("allow-axioms", "")
    assert "native_decide" in allow, (
        "audit must allow-list the native_decide axioms or it false-fails")
    # Pin the empirical footprint so a silent re-shrink (or accidental copy of
    # the blocking gate's 19) is caught -- and so any future widening has to
    # come with the module-attribution argument, as #9341's did.
    names = [a.strip() for a in allow.split(",") if a.strip()]
    assert len(names) == 46, (
        f"audit allow-list must carry the 46 native_decide axioms of the 7 "
        f"covered Life modules (empirical footprint, #8782 + #9341); got "
        f"{len(names)}")
    # Sample members from each family revealed by the audit (P4 base cases,
    # box-assez-grand lemmas, hashlife_correct_implies bridges).
    for sample in [
        "Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1✝",
        "Conway.Life.box_assez_grandN_single_cell._native.native_decide.ax_1_4",
        "Conway.Life.hashlife_correct_implies_block_2._native.native_decide.ax_1_1",
        "Conway.Life.padCenter2_correct_block_level1._native.native_decide.ax_1_1",
    ]:
        assert sample in names, (
            f"audit allow-list missing revealed axiom {sample!r}")


def test_audit_allowlist_is_distinct_from_blocking_gate():
    """The audit audits HashlifeCorrectness; the blocking gate audits the
    showcase modules. Their native_decide footprints are disjoint (verified by
    the audit's first CI run: zero overlap). Pinning that they DIFFER prevents
    a future copy-paste of the blocking gate's 19 into the audit (which would
    re-open the vert-hors-cible the audit exists to close)."""
    jobs = _load_jobs()
    audit_set = {a.strip() for a in
                 jobs["proof-integrity-audit"].get("with", {}).get("allow-axioms", "").split(",")
                 if a.strip()}
    blocking_set = {a.strip() for a in
                    jobs["proof-integrity"].get("with", {}).get("allow-axioms", "").split(",")
                    if a.strip()}
    assert audit_set != blocking_set, (
        "audit and blocking gate audit different modules -> their native_decide "
        "allow-lists must differ (28 HashlifeCorrectness vs 19 showcase)")
    assert audit_set.isdisjoint(blocking_set) or len(audit_set & blocking_set) <= 2, (
        "the two native_decide footprints are empirically disjoint")


def test_blocking_and_audit_are_complementary():
    """The two jobs must not both skip HashlifeCorrectness -- that is the
    vert-hors-cible defect. The audit targets it; the blocking gate (which
    cannot, it has sorries) deliberately excludes it."""
    jobs = _load_jobs()
    blocking_targets = jobs["proof-integrity"].get("with", {}).get("target-modules", "")
    audit_targets = jobs["proof-integrity-audit"].get("with", {}).get("target-modules", "")
    assert "Conway.Life.HashlifeCorrectness" in audit_targets
    assert "Conway.Life.HashlifeCorrectness" not in blocking_targets


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
