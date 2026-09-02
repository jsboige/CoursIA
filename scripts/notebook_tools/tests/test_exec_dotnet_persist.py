"""Tests for exec_dotnet_persist.py — _split_lines helper."""

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
import exec_dotnet_persist
from exec_dotnet_persist import _split_lines


# --- _split_lines ---


class TestSplitLines:
    def test_single_line(self):
        result = _split_lines("hello")
        assert result == ["hello"]

    def test_two_lines(self):
        result = _split_lines("hello\nworld")
        assert result == ["hello\n", "world"]

    def test_three_lines(self):
        result = _split_lines("a\nb\nc")
        assert result == ["a\n", "b\n", "c"]

    def test_trailing_newline(self):
        result = _split_lines("hello\n")
        # "hello\n".split('\n') = ["hello", ""]
        # lines[:-1] = ["hello"], lines[-1] = "" (falsy) -> no trailing element
        assert result == ["hello\n"]

    def test_empty_string(self):
        result = _split_lines("")
        # "".split('\n') = [""]
        # lines[:-1] = [], lines[-1] = "" (falsy) -> no trailing element
        assert result == []

    def test_only_newlines(self):
        result = _split_lines("\n\n")
        # "\n\n".split('\n') = ["", "", ""]
        # lines[:-1] = ["", ""], lines[-1] = "" (falsy) -> []
        assert result == ["\n", "\n"]

    def test_multiline_code(self):
        result = _split_lines("x = 1\ny = 2\nz = 3")
        assert result == ["x = 1\n", "y = 2\n", "z = 3"]
        # Verify nbformat convention: all but last end with \n
        for line in result[:-1]:
            assert line.endswith("\n")
        assert not result[-1].endswith("\n")


class TestCompatibilityWrapper:
    def test_delegates_to_canonical_executor_with_legacy_options(self, tmp_path):
        path = tmp_path / "legacy.ipynb"
        path.write_text(json.dumps({
            "cells": [],
            "metadata": {"kernelspec": {"name": ".net-fsharp"}},
        }), encoding="utf-8")

        with patch.object(exec_dotnet_persist, "execute_notebook") as execute:
            execute.return_value = {"executed": 4, "errors": 1}
            result = exec_dotnet_persist.execute_and_persist(str(path), 45)

        assert result == (4, 1)
        execute.assert_called_once_with(
            path,
            kernel_name=".net-fsharp",
            cell_timeout=45,
            ready_timeout=120,
            skip_empty_code_cells=True,
            text_as_lines=True,
            allowed_mime_types=("text/plain", "text/html", "image/svg+xml"),
            idle_grace=2.0,
        )

    def test_kernel_defaults_when_metadata_is_absent(self, tmp_path):
        path = tmp_path / "default.ipynb"
        path.write_text(json.dumps({"cells": [], "metadata": {}}),
                        encoding="utf-8")

        with patch.object(exec_dotnet_persist, "execute_notebook") as execute:
            execute.return_value = {"executed": 0, "errors": 0}
            exec_dotnet_persist.execute_and_persist(str(path))

        assert execute.call_args.kwargs["kernel_name"] == ".net-csharp"
