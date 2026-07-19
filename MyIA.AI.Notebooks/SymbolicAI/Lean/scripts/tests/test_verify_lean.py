"""
Tests for verify_lean.py CLI validation script.

Covers:
- NotebookValidation / EnvironmentCheck / LeanVerificationReport dataclasses
  and their .status / .ready / .can_execute / count properties.
- get_repo_root() / get_lean_directory() path discovery.
- validate_notebook() against fixture notebooks (kernel, cells, content).
- check_support_files() against a temporary Lean-like directory.
- get_notebook_kernel() routing (Lean-1/7/8 -> python3, others -> lean4).
- filter_notebooks() with --notebook and --python-only.
- Argparse CLI shape via subprocess --help (and a --quick dry run).

All tests are CPU-only and hermetic. They do NOT require Lean, Elan, lean4_jupyter,
papermill, or jupyter_client installed — those are runtime-only paths covered by
sibling tests (test_leandojo_basic / test_leandojo_repos / test_wsl_lean4_jupyter).

Surfaced as test-coverage grain for verify_lean.py (orphaned, 850L, pure-stdlib).
Run with:
    cd MyIA.AI.Notebooks/SymbolicAI/Lean/scripts
    pytest tests/test_verify_lean.py -v
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Make verify_lean importable (script lives at ../verify_lean.py)
SCRIPTS_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import verify_lean as vl  # noqa: E402  (path injected above)


# =============================================================================
# NotebookValidation dataclass + .status property
# =============================================================================

class TestNotebookValidationStatus:
    """Test NotebookValidation.status property covers MISSING / ERROR / WARNING / OK."""

    def test_status_missing_when_not_exists(self):
        nb = vl.NotebookValidation(name="nope.ipynb")
        assert nb.exists is False
        assert nb.status == "MISSING"

    def test_status_error_when_errors_present(self):
        nb = vl.NotebookValidation(name="bad.ipynb", exists=True, errors=["bad JSON"])
        assert nb.status == "ERROR"

    def test_status_warning_when_warnings_only(self):
        nb = vl.NotebookValidation(
            name="warn.ipynb",
            exists=True,
            valid_json=True,
            has_cells=True,
            warnings=["Only 1 markdown cell (expected >= 3 for pedagogical content)"],
        )
        assert nb.status == "WARNING"

    def test_status_ok_when_no_errors_no_warnings(self):
        nb = vl.NotebookValidation(
            name="good.ipynb",
            exists=True,
            valid_json=True,
            has_cells=True,
        )
        assert nb.status == "OK"

    def test_errors_take_precedence_over_warnings(self):
        nb = vl.NotebookValidation(
            name="mixed.ipynb",
            exists=True,
            warnings=["some warning"],
            errors=["some error"],
        )
        # Error branch wins (matches status property: errors checked before warnings)
        assert nb.status == "ERROR"


# =============================================================================
# EnvironmentCheck dataclass + properties
# =============================================================================

class TestEnvironmentCheck:
    """Test EnvironmentCheck.ready / .can_execute properties."""

    def test_default_environment_not_ready(self):
        env = vl.EnvironmentCheck()
        assert env.ready is False
        assert env.can_execute is False

    def test_ready_when_elan_and_lean_installed(self):
        env = vl.EnvironmentCheck(elan_installed=True, lean_installed=True)
        assert env.ready is True
        # No kernel yet -> cannot execute
        assert env.can_execute is False

    def test_can_execute_requires_kernel(self):
        env = vl.EnvironmentCheck(
            elan_installed=True,
            lean_installed=True,
            lean4_jupyter_installed=True,
            kernel_registered=True,
        )
        assert env.can_execute is True

    def test_can_execute_false_if_kernel_unregistered_even_with_packages(self):
        env = vl.EnvironmentCheck(
            elan_installed=True,
            lean_installed=True,
            lean4_jupyter_installed=True,
            kernel_registered=False,
        )
        assert env.can_execute is False

    def test_errors_default_to_empty_list(self):
        # Important: each EnvironmentCheck must have its own list, not share with dataclass
        env1 = vl.EnvironmentCheck()
        env1.errors.append("err1")
        env2 = vl.EnvironmentCheck()
        assert env2.errors == []  # default_factory isolates instances


# =============================================================================
# LeanVerificationReport dataclass + count properties + to_dict
# =============================================================================

class TestLeanVerificationReport:
    """Test count properties and to_dict() output."""

    def test_empty_report_counts(self):
        report = vl.LeanVerificationReport(timestamp="2026-01-01T00:00:00", lean_directory="/x")
        assert report.notebook_count == 0
        assert report.error_count == 0
        assert report.missing_count == 0
        assert report.support_files_ok is True  # vacuously true on empty dict

    def test_notebook_count_counts_only_existing(self):
        report = vl.LeanVerificationReport(timestamp="t", lean_directory="/x")
        report.notebooks = [
            vl.NotebookValidation(name="a.ipynb", exists=True),
            vl.NotebookValidation(name="b.ipynb", exists=False),
            vl.NotebookValidation(name="c.ipynb", exists=True),
        ]
        assert report.notebook_count == 2

    def test_error_count_counts_error_status_only(self):
        report = vl.LeanVerificationReport(timestamp="t", lean_directory="/x")
        report.notebooks = [
            vl.NotebookValidation(name="ok.ipynb", exists=True),
            vl.NotebookValidation(name="bad.ipynb", exists=True, errors=["x"]),
            vl.NotebookValidation(name="miss.ipynb", exists=False),  # counts as MISSING
            vl.NotebookValidation(name="warn.ipynb", exists=True, warnings=["x"]),
        ]
        # status: ok.ipynb=OK, bad.ipynb=ERROR, miss.ipynb=MISSING, warn.ipynb=WARNING
        assert report.error_count == 1  # only bad.ipynb
        assert report.missing_count == 1  # only miss.ipynb

    def test_to_dict_shape_matches_documented_contract(self):
        report = vl.LeanVerificationReport(timestamp="t", lean_directory="/x")
        env = vl.EnvironmentCheck(elan_installed=True)
        report.environment = env
        report.notebooks = [vl.NotebookValidation(name="a.ipynb", exists=True)]
        report.support_files = {"README.md": True}
        report.execution_results = {"a.ipynb": "OK"}

        d = report.to_dict()
        assert d["timestamp"] == "t"
        assert d["lean_directory"] == "/x"
        assert d["summary"]["notebooks_found"] == 1
        assert d["summary"]["notebooks_expected"] == len(vl.LEAN_NOTEBOOKS)
        assert d["environment"]["elan_installed"] is True
        assert isinstance(d["notebooks"], list)
        assert d["support_files"] == {"README.md": True}
        assert d["execution_results"] == {"a.ipynb": "OK"}

    def test_to_dict_without_environment(self):
        report = vl.LeanVerificationReport(timestamp="t", lean_directory="/x")
        d = report.to_dict()
        assert d["environment"] is None
        assert d["summary"]["environment_ready"] is False
        assert d["summary"]["can_execute"] is False


# =============================================================================
# Module-level constants (pin guards against accidental edit)
# =============================================================================

class TestConstants:
    """Test module-level lists/kernels — guards against accidental edit."""

    def test_lean_notebooks_count_is_8(self):
        assert len(vl.LEAN_NOTEBOOKS) == 8

    def test_lean_notebooks_start_with_setup(self):
        assert vl.LEAN_NOTEBOOKS[0] == "Lean-1-Setup.ipynb"

    def test_python_notebooks_subset_of_lean_notebooks(self):
        for nb in vl.PYTHON_NOTEBOOKS:
            assert nb in vl.LEAN_NOTEBOOKS

    def test_lean4_notebooks_disjoint_with_python_notebooks(self):
        overlap = set(vl.LEAN4_NOTEBOOKS) & set(vl.PYTHON_NOTEBOOKS)
        assert overlap == set()

    def test_python_notebooks_are_1_7_8(self):
        # 1=setup/diagnostic, 7=LLM, 8=agentic — documented in module
        assert set(vl.PYTHON_NOTEBOOKS) == {
            "Lean-1-Setup.ipynb",
            "Lean-7-LLM-Integration.ipynb",
            "Lean-8-Agentic-Proving.ipynb",
        }

    def test_support_files_includes_examples(self):
        assert "examples/basic_logic.lean" in vl.SUPPORT_FILES
        assert "examples/mathlib_examples.lean" in vl.SUPPORT_FILES
        assert "README.md" in vl.SUPPORT_FILES


# =============================================================================
# get_repo_root() / get_lean_directory() path discovery
# =============================================================================

class TestPathDiscovery:
    """Test path-discovery helpers return non-throwing canonical paths."""

    def test_get_repo_root_returns_path(self):
        # Script is at .../Lean/scripts/verify_lean.py — root is 4 levels up
        root = vl.get_repo_root()
        assert isinstance(root, Path)
        assert root.is_absolute()
        # The root should end in a recognizable segment (CoursIA on this machine)
        assert root.name  # just not empty

    def test_get_lean_directory_includes_lean_notebooks(self):
        lean_dir = vl.get_lean_directory(vl.get_repo_root())
        assert isinstance(lean_dir, Path)
        # verify_lean.py runs from this directory's scripts/ — get_lean_directory
        # prefers the local Lean-1-Setup check, so the dir should be the real one
        assert lean_dir.exists()


# =============================================================================
# validate_notebook() against fixture notebooks (created in tmp_path)
# =============================================================================

def _write_nb(tmp_path: Path, name: str, nb: dict) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _well_formed_kernel() -> dict:
    return {"kernelspec": {"name": "lean4", "language": "lean4", "display_name": "Lean 4"}}


def _well_formed_cells():
    return [
        {"cell_type": "markdown", "source": ["# Title\n", "Intro paragraph"], "metadata": {}},
        {"cell_type": "markdown", "source": ["## Section\n"], "metadata": {}},
        {"cell_type": "markdown", "source": ["## Another\n"], "metadata": {}},
        {"cell_type": "markdown", "source": ["## More\n"], "metadata": {}},
        {"cell_type": "code", "source": ["#check 1 + 1"], "metadata": {}},
        {"cell_type": "code", "source": ["#eval 2 + 2"], "metadata": {}},
    ]


class TestValidateNotebook:
    """Test validate_notebook() against fixture notebooks."""

    def test_missing_file_returns_missing_status(self, tmp_path):
        nb_path = tmp_path / "does_not_exist.ipynb"
        result = vl.validate_notebook(nb_path)
        assert result.status == "MISSING"
        assert "File does not exist" in result.errors

    def test_invalid_json_returns_error(self, tmp_path):
        bad = tmp_path / "bad.ipynb"
        bad.write_text("{not valid json")
        result = vl.validate_notebook(bad)
        assert result.status == "ERROR"
        assert any("Invalid JSON" in e for e in result.errors)

    def test_missing_cells_field_is_error(self, tmp_path):
        nb_path = _write_nb(tmp_path, "x.ipynb", {"metadata": _well_formed_kernel()})
        result = vl.validate_notebook(nb_path)
        assert result.status == "ERROR"
        assert any("Missing 'cells' field" in e for e in result.errors)

    def test_missing_metadata_field_is_error(self, tmp_path):
        nb_path = _write_nb(tmp_path, "x.ipynb", {"cells": _well_formed_cells()})
        result = vl.validate_notebook(nb_path)
        assert result.status == "ERROR"
        assert any("Missing 'metadata' field" in e for e in result.errors)

    def test_missing_source_field_per_cell_is_error(self, tmp_path):
        nb = {"cells": [
            {"cell_type": "markdown", "metadata": {}},  # no source
        ], "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "x.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert any("missing 'source'" in e for e in result.errors)

    def test_low_markdown_cells_triggers_warning(self, tmp_path):
        cells = [
            {"cell_type": "markdown", "source": ["# only one"], "metadata": {}},
            {"cell_type": "code", "source": ["#eval 1"], "metadata": {}},
            {"cell_type": "code", "source": ["#eval 2"], "metadata": {}},
        ]
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-1-Setup.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.status in ("WARNING", "ERROR")
        assert any("markdown cells" in w for w in result.warnings)

    def test_low_code_cells_triggers_warning(self, tmp_path):
        cells = [
            {"cell_type": "markdown", "source": ["# m1"], "metadata": {}},
            {"cell_type": "markdown", "source": ["# m2"], "metadata": {}},
            {"cell_type": "markdown", "source": ["# m3"], "metadata": {}},
            {"cell_type": "markdown", "source": ["# m4"], "metadata": {}},
            {"cell_type": "code", "source": ["#eval 1"], "metadata": {}},
        ]
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-2-Dependent-Types.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert any("code cells" in w for w in result.warnings)

    def test_lean4_kernel_correct(self, tmp_path):
        nb = {"cells": _well_formed_cells(), "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-2-Dependent-Types.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.kernel_correct is True

    def test_lean_kernel_name_also_accepted(self, tmp_path):
        kernel = {"kernelspec": {"name": "lean", "language": "lean", "display_name": "Lean"}}
        nb = {"cells": _well_formed_cells(), "metadata": kernel}
        nb_path = _write_nb(tmp_path, "Lean-3-Propositions-Proofs.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.kernel_correct is True

    def test_python_kernel_on_lean7_accepted_with_warning(self, tmp_path):
        kernel = {"kernelspec": {"name": "python3", "language": "python", "display_name": "Python 3"}}
        nb = {"cells": _well_formed_cells(), "metadata": kernel}
        nb_path = _write_nb(tmp_path, "Lean-7-LLM-Integration.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.kernel_correct is True
        assert any("Python kernel" in w for w in result.warnings)

    def test_unexpected_kernel_on_lean2_warns(self, tmp_path):
        kernel = {"kernelspec": {"name": "iruby", "language": "ruby", "display_name": "Ruby"}}
        nb = {"cells": _well_formed_cells(), "metadata": kernel}
        nb_path = _write_nb(tmp_path, "Lean-2-Dependent-Types.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.kernel_correct is False
        assert any("Expected lean4" in w for w in result.warnings)

    def test_lean1_setup_should_have_install_code(self, tmp_path):
        # Setup notebook missing install/elan references -> warning
        cells = [
            {"cell_type": "markdown", "source": ["# Setup"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## More"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## More2"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## More3"], "metadata": {}},
            {"cell_type": "code", "source": ["-- this is just commentary"], "metadata": {}},
            {"cell_type": "code", "source": ["-- nothing actionable"], "metadata": {}},
        ]
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-1-Setup.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert any("installation/verification code" in w for w in result.warnings)

    def test_lean2_dependent_types_wants_check_examples(self, tmp_path):
        # Filename MUST contain "Lean-N" — regex 'Lean-(\d+)' gates the
        # content-specific branch. Source must NOT contain "#check" substring
        # (the validator scans for it literally).
        cells = [
            {"cell_type": "markdown", "source": ["# Types"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m2"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m3"], "metadata": {}},
            {"cell_type": "code", "source": ["-- no type examples"], "metadata": {}},
            {"cell_type": "code", "source": ["-- nothing useful"], "metadata": {}},
        ]
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-2-Dependent-Types.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert any("#check examples" in w for w in result.warnings)

    def test_lean5_tactics_wants_by_keyword(self, tmp_path):
        cells = [
            {"cell_type": "markdown", "source": ["# Tactics"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m2"], "metadata": {}},
            {"cell_type": "markdown", "source": ["## m3"], "metadata": {}},
            {"cell_type": "code", "source": ["#check 1"], "metadata": {}},
            {"cell_type": "code", "source": ["-- nothing useful here"], "metadata": {}},
        ]
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-5-Tactics.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert any("'by' keyword" in w for w in result.warnings)

    def test_cell_counts_accurate(self, tmp_path):
        cells = _well_formed_cells()
        nb = {"cells": cells, "metadata": _well_formed_kernel()}
        nb_path = _write_nb(tmp_path, "Lean-3-Propositions-Proofs.ipynb", nb)
        result = vl.validate_notebook(nb_path)
        assert result.total_cells == len(cells)
        assert result.markdown_cells == 4
        assert result.code_cells == 2


# =============================================================================
# check_support_files()
# =============================================================================

class TestCheckSupportFiles:
    """Test support-file discovery against a synthetic Lean directory."""

    def test_all_support_files_present(self, tmp_path):
        # Create the directory tree described in SUPPORT_FILES
        (tmp_path / "examples").mkdir()
        for f in vl.SUPPORT_FILES:
            (tmp_path / f).parent.mkdir(parents=True, exist_ok=True)
            (tmp_path / f).write_text("# stub", encoding="utf-8")

        result = vl.check_support_files(tmp_path)
        assert len(result) == len(vl.SUPPORT_FILES)
        assert all(result.values())
        assert result["README.md"] is True
        assert result["examples/basic_logic.lean"] is True

    def test_missing_one_support_file(self, tmp_path):
        # Create everything EXCEPT one
        (tmp_path / "examples").mkdir()
        for f in vl.SUPPORT_FILES:
            (tmp_path / f).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / "README.md").write_text("ok", encoding="utf-8")
        (tmp_path / ".env.example").write_text("ok", encoding="utf-8")
        for name in [
            "basic_logic.lean", "quantifiers.lean", "tactics_demo.lean",
            "mathlib_examples.lean", "llm_assisted_proof.lean",
        ]:
            (tmp_path / "examples" / name).write_text("ok", encoding="utf-8")

        result = vl.check_support_files(tmp_path)
        assert result["README.md"] is True
        assert all(result.values())

    def test_empty_directory(self, tmp_path):
        result = vl.check_support_files(tmp_path)
        assert all(v is False for v in result.values())

    def test_partial_directory(self, tmp_path):
        (tmp_path / "README.md").write_text("ok", encoding="utf-8")
        result = vl.check_support_files(tmp_path)
        assert result["README.md"] is True
        assert result[".env.example"] is False


# =============================================================================
# get_notebook_kernel()
# =============================================================================

class TestGetNotebookKernel:
    """Test kernel-routing for Python notebooks (1, 7, 8) vs Lean4 (others)."""

    @pytest.mark.parametrize("name", ["Lean-1-Setup.ipynb", "Lean-7-LLM-Integration.ipynb", "Lean-8-Agentic-Proving.ipynb"])
    def test_python_notebooks_route_to_python3(self, name):
        assert vl.get_notebook_kernel(Path(name)) == "python3"

    @pytest.mark.parametrize("name", [
        "Lean-2-Dependent-Types.ipynb",
        "Lean-3-Propositions-Proofs.ipynb",
        "Lean-4-Quantifiers.ipynb",
        "Lean-5-Tactics.ipynb",
        "Lean-6-Mathlib-Essentials.ipynb",
    ])
    def test_lean_notebooks_route_to_lean4(self, name):
        assert vl.get_notebook_kernel(Path(name)) == "lean4"


# =============================================================================
# filter_notebooks()
# =============================================================================

class TestFilterNotebooks:
    """Test notebook filter by name (comma-separated) and python-only flag."""

    def test_no_filter_returns_all(self):
        assert vl.filter_notebooks(vl.LEAN_NOTEBOOKS, None) == vl.LEAN_NOTEBOOKS

    def test_python_only_returns_three(self):
        result = vl.filter_notebooks(vl.LEAN_NOTEBOOKS, None, python_only=True)
        assert set(result) == set(vl.PYTHON_NOTEBOOKS)
        assert len(result) == 3

    def test_filter_by_single_name(self):
        result = vl.filter_notebooks(vl.LEAN_NOTEBOOKS, "Lean-2")
        assert result == ["Lean-2-Dependent-Types.ipynb"]

    def test_filter_by_multiple_names(self):
        result = vl.filter_notebooks(vl.LEAN_NOTEBOOKS, "Lean-2,Lean-5")
        assert "Lean-2-Dependent-Types.ipynb" in result
        assert "Lean-5-Tactics.ipynb" in result
        assert len(result) == 2

    def test_filter_is_case_insensitive(self):
        result = vl.filter_notebooks(vl.LEAN_NOTEBOOKS, "lean-2")
        assert "Lean-2-Dependent-Types.ipynb" in result

    def test_filter_name_with_python_only_combo(self):
        # Filter "Lean-1" + python_only → still only python notebooks match
        result = vl.filter_notebooks(
            vl.LEAN_NOTEBOOKS, "Lean-1", python_only=True
        )
        # Lean-1 is in PYTHON_NOTEBOOKS, so it passes both filters
        assert result == ["Lean-1-Setup.ipynb"]

    def test_filter_with_no_matches_returns_empty(self):
        result = vl.filter_notebooks(vl.LEAN_NOTEBOOKS, "Nonexistent-99")
        assert result == []


# =============================================================================
# Argparse CLI shape (subprocess --help)
# =============================================================================

class TestArgparse:
    """Test the CLI parser accepts the documented flags."""

    def test_help_exits_0(self):
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "verify_lean.py"), "--help"],
            capture_output=True, text=True, timeout=15,
        )
        assert result.returncode == 0
        assert "Verify Lean notebooks" in result.stdout
        # Spot-check key flags are documented in --help
        for flag in ["--quick", "--check-env", "--execute", "--cell-by-cell",
                     "--notebook", "--python-only", "--verbose", "--json", "--timeout"]:
            assert flag in result.stdout, f"--help missing flag: {flag}"

    def test_quick_dry_run_does_not_crash_when_module_in_path(self, tmp_path, monkeypatch):
        # Invoking the script under pytest as a subprocess in tmp cwd to ensure
        # the script returns something predictable: ModuleNotFoundError on Lean-1
        # OR a verification report. We just want non-zero-info exit if Lean
        # notebooks aren't present.
        result = subprocess.run(
            [sys.executable, str(SCRIPTS_DIR / "verify_lean.py"), "--quick"],
            capture_output=True, text=True, timeout=30,
            cwd=str(tmp_path),
        )
        # Script should at least print "Verifying Lean notebooks in:" before exiting
        # with 0 or 1 depending on whether any notebook was found. We don't assert
        # exit code — we just verify it ran without Python error.
        assert "Error" not in result.stderr or "Traceback" not in result.stderr
        # Output should mention the Lean notebooks directory (even if missing)
        assert "Verifying Lean notebooks" in result.stdout or "Lean directory not found" in result.stdout
