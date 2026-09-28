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
    composite_axiom_coverage,
    calls_gate,
    classify_deleted,
    deleted_dispatchers,
    filewide_project_paths,
    gate_project_paths,
    iter_jobs,
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
        text = (
            "jobs:\n"
            "  proof-integrity:\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
        )
        assert calls_gate(text) is True

    def test_gate_mentioned_outside_jobs_is_not_a_call(self):
        """A `uses:` line that no job carries is prose, not a job call."""
        assert calls_gate("    uses: ./.github/workflows/lean-axiom.yml\n") is False

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
            "jobs:\n"
            "  proof-integrity:\n"
            "# project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/ghost_lean\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/real_lean\n"
        )
        assert gate_project_paths(text) == ["MyIA.AI.Notebooks/SymbolicAI/Lean/real_lean"]

    def test_build_job_lake_is_not_credited_to_the_gate(self):
        """The defect Hermes measured on lean-knot.yml (#17150, 2026-09-21).

        The `ci` job hands a `project-path:` to lean-build.yml; only the
        `proof-integrity` job hands one to the gate. A file-wide scan returns
        both and credits a lake the gate never saw.
        """
        text = (
            "jobs:\n"
            "  ci:\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-build.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/built_lean\n"
            "  proof-integrity:\n"
            "    needs: ci\n"
            "    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main\n"
            "    with:\n"
            "      project-path: MyIA.AI.Notebooks/SymbolicAI/Lean/gated_lean\n"
        )
        assert gate_project_paths(text) == ["MyIA.AI.Notebooks/SymbolicAI/Lean/gated_lean"]

    def test_two_gate_jobs_keep_their_own_lakes(self):
        """Scoping pairs per job -- it does not merely deduplicate."""
        text = (
            "jobs:\n"
            "  proof-integrity:\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
            "    with:\n"
            "      project-path: A/a_lean\n"
            "  proof-integrity-audit:\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
            "    with:\n"
            "      project-path: B/b_lean\n"
        )
        assert gate_project_paths(text) == ["A/a_lean", "B/b_lean"]

    def test_a_job_after_the_gate_caller_does_not_leak_in(self):
        """The surplus is not always *before* the calling job."""
        text = (
            "jobs:\n"
            "  proof-integrity:\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
            "    with:\n"
            "      project-path: A/gated_lean\n"
            "  notebook-validate:\n"
            "    with:\n"
            "      project-path: B/not_a_lake\n"
        )
        assert gate_project_paths(text) == ["A/gated_lean"]


class TestIterJobs:
    """The indentation-based job splitter the whole pairing rests on."""

    def test_splits_and_keeps_bodies_apart(self):
        text = (
            "on:\n"
            "  push:\n"
            "    paths:\n"
            "      - 'a/**'\n"
            "jobs:\n"
            "  first:\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - uses: actions/checkout@v4\n"
            "  second:\n"
            "    runs-on: ubuntu-latest\n"
        )
        assert [name for name, _ in iter_jobs(text)] == ["first", "second"]

    def test_a_top_level_key_closes_the_jobs_mapping(self):
        """Keys AFTER jobs: must not be read as jobs (and vice versa)."""
        text = (
            "jobs:\n"
            "  only:\n"
            "    runs-on: ubuntu-latest\n"
            "notifications:\n"
            "  email: someone@example.com\n"
        )
        assert [name for name, _ in iter_jobs(text)] == ["only"]

    def test_keys_before_jobs_are_not_jobs(self):
        text = (
            "on:\n"
            "  workflow_dispatch:\n"
            "env:\n"
            "  FOO: bar\n"
            "jobs:\n"
            "  real:\n"
            "    runs-on: ubuntu-latest\n"
        )
        assert [name for name, _ in iter_jobs(text)] == ["real"]

    def test_a_job_key_with_a_trailing_comment_is_still_a_job(self):
        text = (
            "jobs:\n"
            "  proof-integrity:  # the gate\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
        )
        assert [name for name, _ in iter_jobs(text)] == ["proof-integrity"]


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
            assert set(e) == {"dispatcher", "deleted_by", "had_gate", "gated_paths"}
            assert isinstance(e["had_gate"], bool)
            assert e["dispatcher"].startswith("lean-")
            assert e["deleted_by"], "a deletion must carry the commit that made it"
            assert isinstance(e["gated_paths"], list)


class TestClassifyDeleted:
    """Deplacer le gate n'est pas le perdre — et l'illisible reste PERDU."""

    def _d(self, paths):
        return {"dispatcher": "lean-x.yml", "deleted_by": "0123456789",
                "had_gate": True, "gated_paths": paths}

    def test_full_recoverage_is_relocation_not_loss(self):
        d = self._d(["A/a_lean", "B/b_lean"])
        r = classify_deleted([d], {"A/a_lean", "B/b_lean", "C/c_lean"})
        assert r["lost"] == [] and r["never"] == []
        assert [e["dispatcher"] for e in r["relocated"]] == ["lean-x.yml"]

    def test_one_uncovered_path_keeps_it_lost(self):
        d = self._d(["A/a_lean", "B/b_lean"])
        r = classify_deleted([d], {"A/a_lean"})
        assert r["relocated"] == [] and r["never"] == []
        assert [e["dispatcher"] for e in r["lost"]] == ["lean-x.yml"]

    def test_gate_without_project_path_fails_closed(self):
        """A caller that passed no project-path cannot prove coverage moved."""
        d = self._d([])
        r = classify_deleted([d], {"A/a_lean"})
        assert r["relocated"] == []
        assert [e["dispatcher"] for e in r["lost"]] == ["lean-x.yml"]

    def test_never_had_gate_stays_never(self):
        d = {"dispatcher": "lean-y.yml", "deleted_by": "0123456789",
             "had_gate": False, "gated_paths": []}
        r = classify_deleted([d], set())
        assert r["lost"] == [] and r["relocated"] == []
        assert [e["dispatcher"] for e in r["never"]] == ["lean-y.yml"]


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

    def test_lost_relocated_and_never_had_are_disjoint_and_exhaustive(self, report):
        lost = {d["dispatcher"] for d in report["lost_gate"]}
        relocated = {d["dispatcher"] for d in report["gate_relocated"]}
        never = {d["dispatcher"] for d in report["never_had_gate"]}
        assert not (lost & relocated) and not (lost & never) and not (relocated & never)
        assert len(lost) + len(relocated) + len(never) == report["deleted_dispatchers"]

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


class TestScopingHoldsOnTheRealRef:
    """The fixtures prove the pairing; these prove it is EXERCISED.

    A job-scoped scan that never disagrees with the file-wide one is
    indistinguishable from the file-wide scan the fix replaces. The
    counterfactual therefore has to stay measurable on the real ref, not only
    on synthetic text.
    """

    @pytest.fixture(scope="class")
    def report(self):
        r = measure(_REF)
        if not r["gate_callers"]:
            pytest.skip(f"no gate caller visible at {_REF}")
        return r

    def test_every_caller_names_the_job_that_calls_the_gate(self, report):
        for wf, jobs in report["gate_calls_by_job"].items():
            assert jobs, f"{wf} is listed as a caller but names no calling job"

    def test_scoping_may_discard_but_never_invents(self, report):
        filewide = filewide_project_paths(_REF)
        for wf, paths in report["gate_callers"].items():
            assert set(paths) <= set(filewide[wf]), (
                f"{wf}: job-scoped scan credited {sorted(set(paths) - set(filewide[wf]))} "
                "which no project-path: of that file carries"
            )

    def test_real_data_distinguishes_job_scoped_from_file_wide(self, report):
        """Ratchet against a silent revert to the file-wide READER.

        Compared as **multiplicities**, not as sets: on ``origin/main`` the
        surplus a file-wide scan picks up is always a *duplicate* of the lake
        the gate itself was given, so a set comparison agrees with the scoped
        scan and this ratchet would be blind -- which it was, measurably, until
        the negative control was run (2026-09-21). Counts separate them: a
        file-wide reader attributes every ``project-path:`` of the file to one
        synthetic job, so its counts equal ``filewide`` by construction.

        Fails if no workflow passes a ``project-path:`` to a job other than the
        gate -- delete this test then, and say so.
        """
        filewide = filewide_project_paths(_REF)
        over = sorted(
            wf for wf, jobs in report["gate_calls_by_job"].items()
            if sum(len(paths) for paths in jobs.values()) != len(filewide[wf]))
        assert over, (
            "no caller separates job-scoped from file-wide extraction: either "
            "the reader went back to reading whole files, or no workflow "
            "passes a project-path to a non-gate job any more"
        )

    def test_filewide_only_paths_is_the_measured_defect(self, report):
        """The surplus the fix discards is reported, so the fix is falsifiable."""
        surplus = report["filewide_only_paths"]
        assert isinstance(surplus, list)
        assert not (set(surplus) & set(report["gated_lakes"])), (
            "a lake cannot be both credited by the job-scoped scan and counted "
            "as surplus of the file-wide one"
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


class TestCompositeAxiomCoverage:
    """Jambe B.3 matricielle (#17336) : le credit via l'action composite.

    Sur cette jambe le project-path est interpole -- le manifeste est la
    verite terrain. Vecu #17370 : lean-serre.yml supprime au profit de la
    matiere, le checker ne voyait plus la couverture et le test
    test_no_lake_ever_lost_the_gate rougissait sur main (2 tetes, 2026-09-25).
    """

    BODIES = {
        "lean-build.yml": (
            "on:\n"
            "  push:\n"
            "jobs:\n"
            "  ci-matrix:\n"
            "    steps:\n"
            "      - uses: ./.github/actions/lean-build\n"
            "      - name: Proof integrity\n"
            "        if: matrix.axiom-target-modules != ''\n"
            "        uses: ./.github/actions/lean-axiom\n"
            "        with:\n"
            "          project-path: ${{ matrix.project-path }}\n"
            "  other:\n"
            "    steps:\n"
            "      - run: echo hi\n"
        ),
        "lean-axiom.yml": (
            "jobs:\n"
            "  axiom:\n"
            "    steps:\n"
            "      - uses: ./.github/actions/lean-axiom\n"
        ),
    }

    def test_action_use_credits_opted_manifest_paths(self):
        cov = composite_axiom_coverage(self.BODIES, {"A/a_lean"})
        assert cov == {"lean-build.yml": {"ci-matrix": ["A/a_lean"]}}

    def test_no_optin_no_credit(self):
        """Sans cle d'opt-in dans le manifeste, rien n'est credite."""
        assert composite_axiom_coverage(self.BODIES, set()) == {}

    def test_gate_file_itself_is_not_credited(self):
        """Le fichier du gate ne compte jamais comme appelant (meme forme)."""
        cov = composite_axiom_coverage(self.BODIES, {"A/a_lean"})
        assert "lean-axiom.yml" not in cov

    def test_workflow_call_form_is_not_composite(self):
        """`uses: ./…/workflows/lean-axiom.yml` releve du scan workflow-call,
        pas du credit composite -- les deux formes ne se melangent pas."""
        bodies = {"w.yml": (
            "jobs:\n"
            "  proof:\n"
            "    uses: ./.github/workflows/lean-axiom.yml\n"
        )}
        assert composite_axiom_coverage(bodies, {"A/a_lean"}) == {}

    def test_composite_paths_relocate_a_deleted_dispatcher(self):
        """Controle d'integration : la couverture composite suffit a faire
        `relocated` (pas `lost`) un dispatcher supprime dont elle reprend
        les project-paths."""
        cov = composite_axiom_coverage(
            self.BODIES, {"MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean"})
        gated = {p for jobs in cov.values() for ps in jobs.values() for p in ps}
        d = {"dispatcher": "lean-serre.yml", "deleted_by": "52b248a3e0",
             "had_gate": True,
             "gated_paths": ["MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean"]}
        r = classify_deleted([d], gated)
        assert r["lost"] == []
        assert [e["dispatcher"] for e in r["relocated"]] == ["lean-serre.yml"]
