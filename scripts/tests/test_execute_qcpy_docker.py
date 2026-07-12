"""Tests for scripts/notebook_tools/execute_qcpy_docker.py — QC-Py Docker executor.

Tests focus on: cell_needs_execution (pure predicate), constants.
No Docker / websocket / network calls required.
"""

import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest

# Mock optional dependencies before importing the module.
# Save the prior binding and restore it after the import. Without save/restore,
# the MagicMock stays in sys.modules["requests"] for the rest of the session and
# contaminates any later module that does `import requests` at its top level
# (e.g. docker.py -> _dk_mod.requests becomes a MagicMock, breaking
# test_genai_docker::TestCheckServiceHealth under the full ubuntu collection
# order). See #2871.
_mocked_optional_deps = {}
for mod_name in ("websocket", "requests"):
    if mod_name not in sys.modules:
        _mocked_optional_deps[mod_name] = None  # sentinel: was absent
        sys.modules[mod_name] = MagicMock()

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from execute_qcpy_docker import (
    BASE_URL_DEFAULT,
    QCPY_DIR,
    REPO_ROOT,
    cell_needs_execution,
)

# Restore sys.modules so the optional-dep mocks don't leak to sibling suites.
for mod_name in list(_mocked_optional_deps):
    sys.modules.pop(mod_name, None)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    def test_base_url_default(self):
        """Default base URL is localhost:8888."""
        assert BASE_URL_DEFAULT == "http://localhost:8888"

    def test_repo_root_is_path(self):
        """REPO_ROOT is a valid Path."""
        assert isinstance(REPO_ROOT, Path)

    def test_qcpy_dir_under_repo(self):
        """QCPY_DIR is under REPO_ROOT."""
        assert QCPY_DIR.is_relative_to(REPO_ROOT)

    def test_qcpy_dir_points_to_quantconnect_python(self):
        """QCPY_DIR points to QuantConnect/Python."""
        assert QCPY_DIR == REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "Python"


# ---------------------------------------------------------------------------
# cell_needs_execution
# ---------------------------------------------------------------------------

class TestCellNeedsExecution:
    def _make_cell(self, cell_type="code", source=None, **kwargs):
        """Build a minimal notebook cell dict."""
        if source is None:
            source = ["print('hello')"]
        cell = {"cell_type": cell_type, "source": source}
        cell.update(kwargs)
        return cell

    def test_markdown_cell_skipped(self):
        """Markdown cells are never executed."""
        assert cell_needs_execution(self._make_cell(cell_type="markdown")) is False

    def test_empty_code_cell_skipped(self):
        """Empty code cells are skipped."""
        assert cell_needs_execution(self._make_cell(source=[])) is False

    def test_whitespace_only_cell_skipped(self):
        """Whitespace-only code cells are skipped."""
        assert cell_needs_execution(self._make_cell(source=["   ", "  "])) is False

    def test_comment_only_cell_skipped(self):
        """All-comment cells are skipped."""
        cell = self._make_cell(source=["# comment", "# another"])
        assert cell_needs_execution(cell) is False

    def test_normal_code_needs_execution(self):
        """Regular code cells need execution."""
        assert cell_needs_execution(self._make_cell(source=["x = 1"])) is True

    def test_mixed_code_and_comments_needs_execution(self):
        """Cells with comments and code need execution."""
        cell = self._make_cell(source=["# setup\n", "x = 1"])
        assert cell_needs_execution(cell) is True

    def test_reference_qc_cell_skipped(self):
        """Cells with [REFERENCE QC] marker are skipped."""
        cell = self._make_cell(source=["class QCAlgorithm:", "    # [REFERENCE QC]"])
        assert cell_needs_execution(cell) is False

    def test_reference_qc_in_comment_not_skipped(self):
        """[REFERENCE QC] in comment-only cell is already skipped by comment check."""
        cell = self._make_cell(source=["# [REFERENCE QC] implementation"])
        assert cell_needs_execution(cell) is False

    def test_reference_qc_with_code_skipped(self):
        """[REFERENCE QC] marker skips even if there's real code."""
        cell = self._make_cell(source=["# [REFERENCE QC]", "qb = QuantBook()"])
        assert cell_needs_execution(cell) is False

    def test_string_source(self):
        """Source as a single string works."""
        cell = {"cell_type": "code", "source": "x = 42"}
        assert cell_needs_execution(cell) is True

    def test_missing_source_key(self):
        """Missing source defaults to empty."""
        assert cell_needs_execution({"cell_type": "code"}) is False

    def test_missing_cell_type(self):
        """Missing cell_type defaults to not code."""
        assert cell_needs_execution({"source": ["x = 1"]}) is False

    def test_multiline_code(self):
        """Multi-line code cells need execution."""
        cell = self._make_cell(source=["import numpy as np\n", "x = np.array([1, 2, 3])"])
        assert cell_needs_execution(cell) is True

    def test_single_line_comment(self):
        """Single comment line is skipped."""
        assert cell_needs_execution(self._make_cell(source=["# just a note"])) is False

    def test_code_with_leading_comment(self):
        """Code after a comment is executed."""
        cell = self._make_cell(source=["# compute\n", "result = 42"])
        assert cell_needs_execution(cell) is True

    def test_multiline_string_source(self):
        """Multi-line string source with code."""
        cell = {"cell_type": "code", "source": "line1\nline2\nline3"}
        assert cell_needs_execution(cell) is True
