"""Tests for batch_reexecute.py — batch notebook re-execution logic."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from batch_reexecute import get_kernel_name, needs_reexecution


# --- needs_reexecution ---

class TestNeedsReexecution:
    def test_needs_reexecution_missing_outputs(self):
        entry = {"status": "READY", "cells_without_outputs": 3}
        assert needs_reexecution(entry) is True

    def test_no_need_fully_executed(self):
        entry = {"status": "READY", "cells_without_outputs": 0}
        assert needs_reexecution(entry) is False

    def test_broken_skipped(self):
        entry = {"status": "BROKEN", "cells_without_outputs": 10}
        assert needs_reexecution(entry) is False

    def test_no_field_defaults_zero(self):
        entry = {"status": "READY"}
        assert needs_reexecution(entry) is False

    def test_missing_status_with_missing_outputs(self):
        entry = {"cells_without_outputs": 5}
        assert needs_reexecution(entry) is True


# --- get_kernel_name ---

class TestGetKernelName:
    def test_python3(self):
        assert get_kernel_name({"kernel": "Python 3"}) == "python3"

    def test_python3_versioned(self):
        assert get_kernel_name({"kernel": "Python 3 (IPython)"}) == "python3"

    def test_dotnet(self):
        assert get_kernel_name({"kernel": ".NET (C#)"}) == ".net-interactive"

    def test_csharp(self):
        assert get_kernel_name({"kernel": "C# .NET Interactive"}) == ".net-interactive"

    def test_unknown_passthrough(self):
        assert get_kernel_name({"kernel": "Lean 4"}) == "lean 4"

    def test_empty_kernel(self):
        assert get_kernel_name({"kernel": ""}) == ""

    def test_case_insensitive(self):
        assert get_kernel_name({"kernel": "PYTHON 3.10"}) == "python3"

    def test_missing_key(self):
        assert get_kernel_name({}) == ""


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
