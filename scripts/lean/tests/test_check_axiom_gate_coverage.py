#!/usr/bin/env python3
"""Tests for check_axiom_gate_coverage.py (#17097 proof-integrity coverage).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_axiom_gate_coverage.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_axiom_gate_coverage import (  # noqa: E402
    calls_gate,
    deleted_dispatchers,
    gate_project_paths,
    main,
    matrix_lakes,
    measure,
)

_REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
_REF = os.environ.get("AXIOM_GATE_COVERAGE_REF", "origin/main")


class TestCallsGate:
    """The tool's whole precision rests on call-vs-mention."""

    def test_real_call_is_detected(self):
        text = (
            "jobs:\n"
            "  proof-integrity:\n"
            "    needs: ci\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean\n"
        )
        assert calls_gate(text) is True

    def test_self_cover_mention_alone_is_not_a_call(self):
        """A path filter entry is not a call — the defect this tool must avoid."""
        text = (
            "on:\n"
            "  push:\n"
            "    paths:\n"
            "      - 'MyIA.AI.Notebooks/Sudoku/sudoku_lean/**.lean'\n"
            "      - '.github/workflows/lean-axiom.yml'\n"
        )
        assert calls_gate(text) is False

    def test_commented_call_is_not_a_call(self):
        """lean-axiom.yml documents its own caller pattern inside comments."""
        text = (
            "# Callers invoke this via:\n"
            "#   jobs:\n"
            "#     proof-integrity:\n"
            "#       uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "#       with:\n"
            "#         project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean\n"
        )
        assert calls_gate(text) is False

    def test_local_relative_form_is_detected(self):
        assert calls_gate("    uses: ./.github/workflows/lean-axiom.yml\n") is True

    def test_unrelated_reusable_workflow_is_not_the_gate(self):
        assert calls_gate("    uses: ./.github/workflows/lean-build.yml@main\n") is False


class TestGateProjectPaths:
    def test_extracts_every_calling_job(self):
        """A lake may call the gate twice (blocking + advisory audit)."""
        text = (
            "jobs:\n"
            "  proof-integrity:\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean\n"
            "  proof-integrity-audit:\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean\n"
        )
        assert gate_project_paths(text) == [
            "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean",
            "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean",
        ]

    def test_commented_project_path_is_ignored(self):
        text = (
            "# project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/ghost_lean\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/real_lean\n"
        )
        assert gate_project_paths(text) == ["MyIA.AI.Notebooks/SymbolicAI/Lean/real_lean"]


class TestMatrixLakes:
    def test_reads_the_lakes_key(self):
        lakes = matrix_lakes(_REF)
        if not lakes:
            pytest.skip(f"no manifest at {_REF}")
        assert all("project-path" in lk for lk in lakes), (
            "every manifest entry must carry a project-path: it is the key the "
            "coverage set is compared against"
        )


class TestDeletedDispatchers:
    def test_partition_is_a_partition(self):
        """Each deleted dispatcher is either 'had_gate' or not — never both/neither."""
        entries = deleted_dispatchers(_REF)
        if not entries:
            pytest.skip(f"no deleted dispatchers visible at {_REF}")
        for e in entries:
            assert set(e) == {"dispatcher", "deleted_by", "had_gate"}
            assert isinstance(e["had_gate"], bool)
            assert e["dispatcher"].startswith("lean-")
            assert e["deleted_by"], "a deletion must carry the commit that made it"


class TestMeasurePartition:
    """Logic invariants — deliberately NOT exact counts, which drift legitimately."""

    @pytest.fixture(scope="class")
    def report(self):
        r = measure(_REF)
        if not r["gate_callers"]:
            pytest.skip(f"no gate caller visible at {_REF}")
        return r

    def test_gated_and_ungated_matrix_lakes_are_disjoint(self, report):
        """The defect this guards: a lake both covered and reported without a gate."""
        overlap = set(report["gated_lakes"]) & set(report["matrix_lakes_without_gate"])
        assert not overlap, f"lake in both sets: {sorted(overlap)}"

    def test_every_ungated_lake_comes_from_the_manifest(self, report):
        assert set(report["matrix_lakes_without_gate"]) <= set(report["matrix_lakes"])

    def test_every_gate_caller_passes_a_project_path(self, report):
        """A `uses:` without project-path would silently gate nothing."""
        for wf, paths in report["gate_callers"].items():
            assert paths, f"{wf} calls the gate but passes no project-path"

    def test_lost_and_never_had_are_disjoint_and_exhaustive(self, report):
        lost = {d["dispatcher"] for d in report["lost_gate"]}
        never = {d["dispatcher"] for d in report["never_had_gate"]}
        assert not (lost & never)
        assert len(lost) + len(never) == report["deleted_dispatchers"]

    def test_verdict_is_not_dressed_as_an_acceptance_criterion(self, report):
        assert "not_an_acceptance_criterion" in report
        assert report["not_an_acceptance_criterion"].strip()


class TestRealRefRegression:
    """Guards the #17097 answer on the real ref: no lake lost the gate."""

    def test_no_lake_ever_lost_the_gate(self):
        r = measure(_REF)
        if not r["deleted_dispatchers"]:
            pytest.skip(f"no deletion history visible at {_REF}")
        assert r["lost_gate"] == [], (
            "a deleted dispatcher called lean-axiom.yml and its lake is now "
            "served only by the matrix: silent coverage regression. Re-wire the "
            "gate or justify it in writing (#17097 criterion 3)."
        )

    def test_missing_gate_on_matrix_lakes_is_reportable(self):
        """The pre-existing gap must stay MEASURABLE, whatever its size."""
        r = measure(_REF)
        if not r["matrix_lakes"]:
            pytest.skip(f"no manifest at {_REF}")
        assert set(r["matrix_lakes"]) <= (
            set(r["gated_lakes"]) | set(r["matrix_lakes_without_gate"])
        )


class TestCheckExitCode:
    def _run(self, argv):
        saved = sys.argv
        try:
            sys.argv = ["check_axiom_gate_coverage.py", *argv]
            return main()
        finally:
            sys.argv = saved

    def test_check_exits_zero_when_nothing_was_lost(self, capsys):
        rc = self._run(["--check", "--ref", _REF])
        out = capsys.readouterr().out
        if "PERDU : 0" in out or "| 0 PERDUS" in out:
            assert rc == 0
        else:
            pytest.skip("ref shows a lost gate; covered by TestRealRefRegression")

    def test_json_output_is_parseable(self, capsys):
        self._run(["--json", "--ref", _REF])
        payload = json.loads(capsys.readouterr().out)
        assert payload["ref"] == _REF
        assert "gate_callers" in payload


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
