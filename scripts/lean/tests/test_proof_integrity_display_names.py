#!/usr/bin/env python3
"""Contract test: lean-axiom.yml jobs in a workflow must carry DISTINCT display-names (#8848).

Dual-mode: runnable directly (``python scripts/lean/tests/test_proof_integrity_display_names.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

The reusable ``lean-axiom.yml`` workflow exposes a ``display-name`` input that becomes
the check's label in the CI rollup (``Proof integrity (<display-name>)``). When a lake
wires TWO lean-axiom.yml jobs -- a BLOCKING one (``fail-on-sorry: true``, sorry-free
modules) and an ADVISORY one (``fail-on-sorry: false``, sorry-bearing modules) -- giving
both the SAME display-name renders them indistinguishable at a glance (#8848): a reviewer
sees ``Proof integrity (conway_lean)`` twice and cannot tell which one tolerates 8
acknowledged sorries from which one refuses them. That recreates, one layer up, the very
"green whose scope is invisible" defect the audit job was built to close (#8782).

This test pins the convention PROACTIVELY for every lake that has, or will have, more
than one lean-axiom.yml job: the advisory one MUST carry a distinguishing suffix
(``<lake> (audit)``), the blocking one keeps the bare lake name (so any branch-protection
rule referencing the check name is unaffected). Discovery is glob-based over
``.github/workflows/lean-*.yml`` so a future lake that adds a second lean-axiom.yml job
is caught the moment it lands -- "corrected at two occurrences, not six" (#8848).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
WF_DIR = REPO / ".github" / "workflows"


def _lean_workflows():
    """Every ``lean-*.yml`` workflow in the repo (discover-based: a future lake that
    wires lean-axiom.yml is covered without editing this test)."""
    return sorted(WF_DIR.glob("lean-*.yml"))


def _lean_axiom_jobs(doc):
    """Map ``job-name -> display-name`` for jobs that reuse ``lean-axiom.yml``.

    The blocking job conventionally carries the bare lake ``display-name``; any
    ADDITIONAL lean-axiom.yml job (advisory) must distinguish itself."""
    yaml = pytest.importorskip("yaml")
    jobs = doc.get("jobs", {})
    out = {}
    for name, spec in jobs.items():
        uses = (spec or {}).get("uses", "")
        if "lean-axiom.yml" in uses:
            display = (spec.get("with", {}) or {}).get("display-name", "")
            out[name] = display
    return out


def test_there_is_at_least_one_lean_workflow():
    wfs = _lean_workflows()
    assert wfs, "no .github/workflows/lean-*.yml found -- test discovery is broken"


def test_lean_axiom_jobs_carry_distinct_display_names():
    """#8848: within ONE workflow, no two lean-axiom.yml jobs may share a
    display-name. The advisory job must suffix `` (audit)``; the blocking job keeps
    the bare lake name (branch-protection check-name stability)."""
    yaml = pytest.importorskip("yaml")
    failures = []
    for wf in _lean_workflows():
        with wf.open(encoding="utf-8") as fh:
            doc = yaml.safe_load(fh)
        jobs = _lean_axiom_jobs(doc)
        if not jobs:
            continue
        # Group jobs by display-name; any group with >1 entry is a collision.
        by_display = {}
        for name, display in jobs.items():
            by_display.setdefault(display, []).append(name)
        for display, owners in by_display.items():
            if len(owners) > 1:
                failures.append(
                    f"{wf.name}: jobs {sorted(owners)} share display-name "
                    f"{display!r} -- the advisory job must suffix ' (audit)' (#8848)")
    assert not failures, (
        "#8848: indistinguishable proof-integrity checks in the CI rollup:\n  - "
        + "\n  - ".join(failures))


def test_advisory_audit_job_carries_audit_suffix():
    """The advisory job (``fail-on-sorry: false``) must carry the `` (audit)``
    suffix WHEN it coexists with a BLOCKING job (``fail-on-sorry: true``) in the
    same workflow -- that is the only configuration where the two are
    indistinguishable without the suffix (#8848). A lake whose sole lean-axiom.yml
    job is already advisory (knot_lean: one ``proof-integrity`` job,
    ``fail-on-sorry: false``) has nothing to distinguish FROM, so the bare lake
    name is correct there. The convention is "distinguish the advisory FROM the
    blocking", not "advisory jobs always suffix"."""
    yaml = pytest.importorskip("yaml")
    failures = []
    for wf in _lean_workflows():
        with wf.open(encoding="utf-8") as fh:
            doc = yaml.safe_load(fh)
        jobs = doc.get("jobs", {}) or {}
        # Does THIS workflow have a blocking (fail-on-sorry: true) lean-axiom job?
        has_blocking = any(
            "lean-axiom.yml" in ((spec or {}).get("uses", ""))
            and (spec.get("with", {}) or {}).get("fail-on-sorry") is True
            for spec in jobs.values()
        )
        if not has_blocking:
            continue  # no blocking job to distinguish from (e.g. knot_lean)
        for name, spec in jobs.items():
            uses = (spec or {}).get("uses", "")
            if "lean-axiom.yml" not in uses:
                continue
            with_opts = spec.get("with", {}) or {}
            if with_opts.get("fail-on-sorry") is False:
                display = with_opts.get("display-name", "")
                if "(audit)" not in display:
                    failures.append(
                        f"{wf.name}: job {name} is advisory (fail-on-sorry: false) "
                        f"beside a blocking job but display-name {display!r} lacks "
                        f"the ' (audit)' suffix (#8848)")
    assert not failures, (
        "#8848: advisory proof-integrity job(s) indistinguishable from blocking:\n  - "
        + "\n  - ".join(failures))


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
