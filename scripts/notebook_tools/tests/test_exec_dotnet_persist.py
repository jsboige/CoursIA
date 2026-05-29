"""Tests for exec_dotnet_persist.py — _split_lines helper."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
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
