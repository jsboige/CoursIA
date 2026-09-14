"""Tests du rapport de reproduction Euler/Navier–Stokes."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from nse_reproduction import (
    EXPECTED_AXIOM_DECLARATIONS,
    PERMITTED_AXIOMS,
    axiom_evidence_verified,
    parse_axiom_declarations,
    parse_axioms,
    parse_comparator_record,
    parse_confinement_record,
    parse_integrity_record,
)


def _organ(**overrides):
    record = {
        "status": "ok",
        "child_exit_code": 0,
        "exit_code": 0,
        "killed": False,
        "orphans": [],
        "duration_s": 12.5,
        "backend": "posix",
    }
    record.update(overrides)
    return record


def _record(**overrides):
    values = {
        "organ": _organ(),
        "stdout": (
            "nanoda kernel accepts the solution\n"
            "Lean default kernel accepts the solution\n"
            "Your solution is okay!\n"
        ),
        "stderr": "",
        "challenge_sha256": "a" * 64,
        "expected_sha256": "a" * 64,
        "started_utc": "2026-09-13T00:00:00Z\n",
        "ended_utc": "2026-09-13T00:00:13Z\n",
        "stdout_sha256": "b" * 64,
        "stderr_sha256": "c" * 64,
    }
    values.update(overrides)
    return parse_comparator_record(**values)


class TestConfinementRecord:
    def test_requires_exact_version_and_functional_probe(self):
        result = parse_confinement_record(
            "landrun version 0.1.17\n", "denied=true allowed=true\n"
        )
        assert result["verified"] is True
        assert result["unauthorized_write_denied"] is True
        assert result["authorized_write_allowed"] is True

    def test_rejects_wrong_version_or_partial_probe(self):
        assert not parse_confinement_record(
            "landrun version 0.1.16", "denied=true allowed=true"
        )["verified"]
        assert not parse_confinement_record(
            "landrun version 0.1.17", "denied=true allowed=false"
        )["verified"]


class TestAxiomParsing:
    def test_parses_wrapped_lists(self):
        text = (
            "'a' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
            "'b' depends on axioms: [Quot.sound, propext, Classical.choice]\n"
        )
        assert parse_axioms(text) == [
            sorted(PERMITTED_AXIOMS),
            sorted(PERMITTED_AXIOMS),
        ]

    def test_surfaces_forbidden_axiom(self):
        text = "'a' depends on axioms: [propext, sorryAx]\n"
        assert parse_axioms(text) == [["propext", "sorryAx"]]

    def test_requires_all_eleven_named_probes(self):
        permitted = {
            declaration: sorted(PERMITTED_AXIOMS)
            for declaration in EXPECTED_AXIOM_DECLARATIONS
        }
        assert axiom_evidence_verified(permitted)
        permitted.pop(EXPECTED_AXIOM_DECLARATIONS[-1])
        assert not axiom_evidence_verified(permitted)

    def test_parses_declaration_names(self):
        text = (
            "'Euler.euler_breakdown_R3' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
        )
        assert parse_axiom_declarations(text) == {
            "Euler.euler_breakdown_R3": sorted(PERMITTED_AXIOMS)
        }
        assert parse_axiom_declarations(text + text) == {}


class TestIntegrityRecord:
    def test_accepts_complete_zero_debt_evidence(self):
        evidence = {
            "schema_version": 1,
            "root_sha": "a" * 40,
            "scanner": "scripts/lean/count_code_sorry.py:scan_file",
            "tracked_lean_files": 2486,
            "challenge_sorry_locations": [
                {
                    "file": "ComparatorChallenges/Euler.lean",
                    "declaration": "euler_breakdown_R3",
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/Euler.lean",
                    "declaration": "exists_compact_smooth_euler_singularity",
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/NavierStokes.lean",
                    "declaration": (
                        "navier_stokes_breakdown_R3"
                    ),
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/NavierStokes.lean",
                    "declaration": (
                        "navier_stokes_breakdown_periodic"
                    ),
                    "count": 1,
                },
            ],
            "solution_sorry_locations": [],
            "solution_sorry_proof_count": 0,
            "native_decide_locations": [],
            "native_decide_count": 0,
        }
        result = parse_integrity_record(evidence, expected_sha="a" * 40)
        assert result["verified"] is True
        assert result["challenge_sorry_proof_count"] == 4
        assert {
            (item["file"], item["declaration"], item["count"])
            for item in result["challenge_sorry_locations"]
        } == {
            (item["file"], item["declaration"], item["count"])
            for item in evidence["challenge_sorry_locations"]
        }

        evidence["challenge_sorry_locations"][0]["file"] = "Euler/Solution.lean"
        assert not parse_integrity_record(
            evidence, expected_sha="a" * 40
        )["verified"]

    def test_rejects_missing_or_nonzero_evidence(self):
        evidence = {
            "schema_version": 1,
            "root_sha": "a" * 40,
            "scanner": "scripts/lean/count_code_sorry.py:scan_file",
            "tracked_lean_files": 2486,
            "solution_sorry_locations": [{"file": "Euler/Solution.lean"}],
            "solution_sorry_proof_count": 1,
            "native_decide_locations": [],
            "native_decide_count": 0,
        }
        assert not parse_integrity_record(
            evidence, expected_sha="a" * 40
        )["verified"]
        del evidence["solution_sorry_locations"]
        assert not parse_integrity_record(
            evidence, expected_sha="a" * 40
        )["verified"]

    def test_rejects_noncanonical_scanner(self):
        evidence = {
            "schema_version": 1,
            "root_sha": "a" * 40,
            "scanner": "custom-grep",
            "tracked_lean_files": 2486,
            "challenge_sorry_locations": [
                {
                    "file": "ComparatorChallenges/Euler.lean",
                    "declaration": "euler_breakdown_R3",
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/Euler.lean",
                    "declaration": "exists_compact_smooth_euler_singularity",
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/NavierStokes.lean",
                    "declaration": (
                        "navier_stokes_breakdown_R3"
                    ),
                    "count": 1,
                },
                {
                    "file": "ComparatorChallenges/NavierStokes.lean",
                    "declaration": (
                        "navier_stokes_breakdown_periodic"
                    ),
                    "count": 1,
                },
            ],
            "solution_sorry_locations": [],
            "solution_sorry_proof_count": 0,
            "native_decide_locations": [],
            "native_decide_count": 0,
        }
        assert not parse_integrity_record(
            evidence, expected_sha="a" * 40
        )["verified"]


class TestComparatorRecord:
    def test_accepts_complete_evidence(self):
        result = _record()
        assert result["verified"] is True
        assert result["kernels"] == {
            "nanoda": "accepts",
            "lean_kernel": "accepts",
        }
        assert result["orphan_postcondition_ok"] is True

    def test_rejects_parent_success_without_nanoda_marker(self):
        result = _record(
            stdout=(
                "Lean default kernel accepts the solution\n"
                "Your solution is okay!\n"
            )
        )
        assert result["verified"] is False
        assert result["kernels"]["nanoda"] == "missing"

    def test_rejects_semantic_error_despite_success_markers(self):
        result = _record(stderr="uncaught exception: kernel rejected the solution")
        assert result["verified"] is False
        assert result["semantic_rejection"] is True

    def test_rejects_child_failure(self):
        result = _record(organ=_organ(status="child_failed", child_exit_code=1))
        assert result["verified"] is False

    def test_rejects_orphans(self):
        result = _record(organ=_organ(orphans=[{"pid": 42}]))
        assert result["verified"] is False
        assert result["orphan_postcondition_ok"] is False

    def test_rejects_challenge_hash_mismatch(self):
        result = _record(expected_sha256="d" * 64)
        assert result["verified"] is False
        assert result["challenge_hash_matches"] is False

    def test_rejects_reworded_final_marker(self):
        result = _record(
            stdout=(
                "nanoda kernel accepts the solution\n"
                "Lean default kernel accepts the solution\n"
                "Solution accepted\n"
            )
        )
        assert result["verified"] is False
        assert result["semantic_verdict"] is None

    def test_preserves_timestamps_and_hashes(self):
        result = _record()
        assert result["started_utc"] == "2026-09-13T00:00:00Z"
        assert result["ended_utc"] == "2026-09-13T00:00:13Z"
        assert result["stdout_sha256"] == "b" * 64
        assert result["stderr_sha256"] == "c" * 64
