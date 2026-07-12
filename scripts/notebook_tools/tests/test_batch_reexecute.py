"""Tests for scripts/notebook_tools/batch_reexecute.py — batch notebook re-execution.

Tests focus on pure functions: needs_reexecution, get_kernel_name.
No filesystem I/O on production files.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from batch_reexecute import get_kernel_name, needs_reexecution


# ---------------------------------------------------------------------------
# needs_reexecution
# ---------------------------------------------------------------------------

class TestNeedsReexecution:
    def test_broken_notebook_skipped(self):
        """BROKEN notebooks are never re-executed."""
        entry = {"status": "BROKEN", "cells_without_outputs": 5}
        assert needs_reexecution(entry) is False

    def test_missing_outputs_needs_reexec(self):
        """Notebooks with cells_without_outputs > 0 need re-execution."""
        entry = {"status": "READY", "cells_without_outputs": 3}
        assert needs_reexecution(entry) is True

    def test_zero_outputs_ok(self):
        """Notebooks with 0 missing outputs don't need re-execution."""
        entry = {"status": "READY", "cells_without_outputs": 0}
        assert needs_reexecution(entry) is False

    def test_no_status_field(self):
        """Missing status field defaults to not BROKEN."""
        entry = {"cells_without_outputs": 2}
        assert needs_reexecution(entry) is True

    def test_no_outputs_field(self):
        """Missing cells_without_outputs defaults to 0."""
        entry = {"status": "READY"}
        assert needs_reexecution(entry) is False

    def test_empty_entry(self):
        """Empty dict needs no re-execution."""
        assert needs_reexecution({}) is False

    def test_status_draft_with_missing(self):
        """DRAFT status with missing outputs still needs re-execution."""
        entry = {"status": "DRAFT", "cells_without_outputs": 1}
        assert needs_reexecution(entry) is True


# ---------------------------------------------------------------------------
# get_kernel_name
# ---------------------------------------------------------------------------

class TestGetKernelName:
    def test_python3(self):
        assert get_kernel_name({"kernel": "Python 3"}) == "python3"

    def test_python3_case_insensitive(self):
        assert get_kernel_name({"kernel": "python 3"}) == "python3"

    def test_dotnet_csharp(self):
        assert get_kernel_name({"kernel": ".NET (C#)"}) == ".net-interactive"

    def test_dotnet_fsharp(self):
        assert get_kernel_name({"kernel": ".NET (F#)"}) == ".net-interactive"

    def test_csharp_direct(self):
        assert get_kernel_name({"kernel": "C# Interactive"}) == ".net-interactive"

    def test_unknown_kernel_passthrough(self):
        """Unknown kernel names are passed through as-is (lowercased)."""
        assert get_kernel_name({"kernel": "Lean4"}) == "lean4"

    def test_empty_kernel(self):
        assert get_kernel_name({"kernel": ""}) == ""

    def test_missing_kernel_key(self):
        assert get_kernel_name({}) == ""

    def test_python3_exact(self):
        """Exact 'Python 3' match."""
        assert get_kernel_name({"kernel": "Python 3 (ipykernel)"}) == "python3"

    def test_dotnet_in_name(self):
        """Any '.net' substring maps to .net-interactive."""
        assert get_kernel_name({"kernel": ".NET Interactive"}) == ".net-interactive"
