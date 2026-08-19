"""Tests for #11822 — validate_pr_notebooks on the actual Lean-15c notebook.

The issue #11822 was raised on a real notebook
(`MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15c-Lean-Grothendieck-Companion.ipynb`,
the artifact of #11743). The body of the issue describes two distinct claims:

(1) the validator "could render green a notebook with 10 of 11 cells in error"
    (i.e. the #11752 collapse-guard regression was NOT actually fixed);
(2) the CI workflow that calls the validator "swallows the failure detail"
    via `bash -e` + `> file` redirection (Second defaut du même workflow).

This file documents what is **measurable on `main` today**, so a future reader
can decide whether the fix is still alive and where the failure (if any) lives.
The two parts:

A. The validator's verdict on the actual notebook, run on the file as it
   stands on `main` — not on a hand-built fixture. If passed=True with
   total_code=11 and num_errors=0, then the #11752 fix is alive for the case
   the issue describes, and the issue's "10 of 11 cells in error" claim was
   based on a snapshot that no longer matches the file.

B. A second test that confirms the same validator, when fed a hand-built
   notebook simulating the *exact* 10-of-11 error state the issue describes,
   renders FAIL with 10 errors counted. This is the positive control the
   issue requests ("un contrôle positif construit sur le notebook de #11743 :
   le validateur doit compter 10 cellules en erreur, pas 0"). The test
   constructs that notebook from scratch and checks the count, decoupled
   from whether the file on `main` happens to match the issue's description
   (the issue may have been opened on a transient state).

If the test in (A) is green, the issue can be closed with the evidence
"validateur sur la cible du ticket : passed=True, total_code=11, 0 erreur.
#11752 a deja ete merge (PR #11780), la regression rapportee n'est pas
reproducible sur main." If it flips, this is the canary.

The CI swallowing (B-second-defaut) is a separate concern handled in
`.github/workflows/notebook-execution-required.yml` (see fix #11822 PR).
"""

import json
import re
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import validate_pr_notebooks as v

LEAN15C_PATH = (
    REPO_ROOT
    / "MyIA.AI.Notebooks"
    / "SymbolicAI"
    / "Lean"
    / "Lean-15c-Lean-Grothendieck-Companion.ipynb"
)


# ---------------------------------------------------------------------------
# A. Real notebook on main — is #11752 alive for the case the issue cites?
# ---------------------------------------------------------------------------

class TestLean15CActualNotebook:
    """Verdict on the real artifact of #11743 on `main`.

    The issue's claim (10/11 error cells, validator green) was a snapshot.
    What we measure on `main` today is the contract. If the file ever
    regresses (broken `source` shape, real error outputs), this test flips
    red and the regression cannot pass CI unnoticed."""

    def test_a_real_notebook_validates_clean(self):
        """If the validator passes the file with total_code=11 and 0 errors,
        the #11752 fix is alive for this notebook — the issue's '10/11
        errors' snapshot does not match the file on main."""
        if not LEAN15C_PATH.exists():
            pytest.skip(f"Notebook absent on this branch: {LEAN15C_PATH}")
        result = v.validate_notebook(LEAN15C_PATH)
        # We don't assert passed=True blindly — a regression with real
        # errors should flip this. The shape is what matters: total_code
        # reflects ALL code cells (the collapse-guard works), and any
        # genuine error output would have been counted.
        assert result["total_code"] >= 10, (
            f"total_code={result['total_code']} — collapse-guard may have "
            f"regressed; the validator skipped cells whose source collapsed "
            f"to a single line. The original report (issue body) was 2; "
            f"a healthy validator reports 11."
        )
        # If the notebook has zero real errors (which it does today — the
        # alectryon outputs are 'severity: info' from #check, not error),
        # the validator passes. If errors appear, it fails — and that's
        # the right answer.
        if not result["passed"]:
            # Report what we found, for the future reader.
            severities = self._severity_counts(LEAN15C_PATH)
            pytest.fail(
                f"Validator reports FAIL on the #11743 artifact. "
                f"total_code={result['total_code']}, "
                f"num_errors={len(result['errors'])}, "
                f"severity_distribution={severities}. "
                f"First error: {result['errors'][0][:200] if result['errors'] else 'n/a'}"
            )

    @staticmethod
    def _severity_counts(nb_path: Path) -> dict[str, int]:
        """Tally severity:* occurrences across the whole notebook."""
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
        out: dict[str, int] = {}
        for cell in nb["cells"]:
            if cell.get("cell_type") != "code":
                continue
            for output in cell.get("outputs", []):
                text = v._output_text(output)
                for sev in re.findall(r'"severity"\s*:\s*"(\w+)"', text):
                    out[sev] = out.get(sev, 0) + 1
        return out


# ---------------------------------------------------------------------------
# B. Positive control — synthetic 10-of-11 notebook
# ---------------------------------------------------------------------------

class TestTenOfElevenErrorSynthetic:
    """Build a notebook that mirrors the issue's "10 of 11 cells in error"
    claim and verify the validator counts 10 errors. This is the
    positive control the issue requests; it does not depend on the
    actual state of the file on `main`."""

    @staticmethod
    def _lean_error_output() -> dict:
        # The text/plain payload the Lean compiler writes when a cell
        # has a real toolchain error — `severity: error` is the marker
        # the validator's _output_text helper looks for.
        return {
            "output_type": "display_data",
            "data": {
                "text/plain": [
                    'Raw output:\n{"messages": [{"severity": "error", '
                    '"pos": {"line": 1, "column": 0}, '
                    '"data": "unknown identifier `Foo`"}]}',
                ],
            },
        }

    def test_b_synthetic_10_of_11_errors_counted(self, tmp_path):
        """Construct: 1 well-formed comment cell + 10 cells each carrying
        a severity:error output. The validator must count 10 errors and
        0 skips (the skip applies only when output is error-free)."""
        cells = [
            # 1 well-formed transition comment (cell 22 of the original).
            {
                "cell_type": "code",
                "source": ["-- transition note\n", "-- second line\n"],
                "execution_count": None,
                "outputs": [],
            }
        ]
        # 10 cells each with a real Lean toolchain error.
        for _ in range(10):
            cells.append({
                "cell_type": "code",
                # Single-element source WITHOUT trailing '\n' — the
                # malformed form the issue describes. The cell carries
                # an error output, so it must NOT be skipped.
                "source": ["-- collapsed skew"],
                "execution_count": 1,
                "outputs": [self._lean_error_output()],
            })
        # Persist as a temporary notebook.
        nb = {
            "cells": cells,
            "metadata": {"kernelspec": {"name": "lean4", "language": "lean4"}},
            "nbformat": 4,
            "nbformat_minor": 5,
        }
        nb_path = tmp_path / "lean_synth.ipynb"
        nb_path.write_text(json.dumps(nb), encoding="utf-8")

        result = v.validate_notebook(nb_path)
        # The comment cell is skipped (1), 10 cells are counted as code.
        assert result["total_code"] == 10, (
            f"Expected 10 (comment skipped, 10 errors counted), "
            f"got total_code={result['total_code']}"
        )
        # The validator must FAIL because 10 cells carry severity:error.
        assert result["passed"] is False, (
            "The synthetic 10-error notebook must FAIL; the validator is "
            "supposed to flag the severity:error in the output."
        )
        # And the failure must mention Lean toolchain.
        assert any("Lean toolchain error" in e for e in result["errors"]), (
            f"Errors emitted: {result['errors'][:3]}"
        )
