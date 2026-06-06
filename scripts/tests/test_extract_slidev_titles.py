"""Tests for scripts/extract_slidev_titles.py — pure function unit tests.

Tests cover split_blocks, is_frontmatter, and title_of (all pure, no I/O).
The extract() function does filesystem I/O and printing, so it is excluded.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_slidev_titles import split_blocks, is_frontmatter, title_of


# ---------------------------------------------------------------------------
# split_blocks
# ---------------------------------------------------------------------------


class TestSplitBlocks:
    """Tests for split_blocks — splits lines by '---' delimiters."""

    def test_empty_input(self):
        assert split_blocks([]) == [[]]

    def test_no_delimiters(self):
        lines = ["line 1", "line 2"]
        result = split_blocks(lines)
        assert result == [["line 1", "line 2"]]

    def test_single_delimiter(self):
        lines = ["before", "---", "after"]
        result = split_blocks(lines)
        assert result == [["before"], ["after"]]

    def test_multiple_delimiters(self):
        lines = ["root fm", "---", "slide 1", "---", "slide 2"]
        result = split_blocks(lines)
        assert len(result) == 3
        assert result[0] == ["root fm"]
        assert result[1] == ["slide 1"]
        assert result[2] == ["slide 2"]

    def test_consecutive_delimiters(self):
        lines = ["---", "---"]
        result = split_blocks(lines)
        assert result == [[], [], []]

    def test_trailing_delimiter(self):
        lines = ["content", "---"]
        result = split_blocks(lines)
        assert result == [["content"], []]

    def test_leading_delimiter(self):
        lines = ["---", "content"]
        result = split_blocks(lines)
        assert result == [[], ["content"]]

    def test_whitespace_delimiter(self):
        """'---' with surrounding whitespace is still a delimiter."""
        lines = ["before", "  ---  ", "after"]
        result = split_blocks(lines)
        assert len(result) == 2

    def test_four_dashes_not_delimiter(self):
        """'----' is NOT a delimiter (exact match on '---')."""
        lines = ["before", "----", "after"]
        result = split_blocks(lines)
        assert len(result) == 1

    def test_preserves_line_content(self):
        lines = ["  indented  ", "\ttab\t"]
        result = split_blocks(lines)
        assert result[0] == ["  indented  ", "\ttab\t"]


# ---------------------------------------------------------------------------
# is_frontmatter
# ---------------------------------------------------------------------------


class TestIsFrontmatter:
    """Tests for is_frontmatter — detects per-slide YAML frontmatter blocks."""

    def test_empty_block(self):
        assert is_frontmatter([]) is False

    def test_whitespace_only(self):
        assert is_frontmatter(["  ", "  "]) is False

    def test_yaml_layout(self):
        assert is_frontmatter(["layout: default"]) is True

    def test_yaml_background(self):
        assert is_frontmatter(["background: /images/bg.png"]) is True

    def test_yaml_transition(self):
        assert is_frontmatter(["transition: slide-up"]) is True

    def test_yaml_multiple_keys(self):
        assert is_frontmatter(["layout: cover", "background: dark"]) is True

    def test_heading_not_frontmatter(self):
        """A block with a '# ' heading is slide content, not frontmatter."""
        assert is_frontmatter(["# My Title", "layout: cover"]) is False

    def test_no_yaml_key(self):
        """Plain text without YAML key pattern is not frontmatter."""
        assert is_frontmatter(["Just some text"]) is False

    def test_numeric_start_not_frontmatter(self):
        """Lines starting with digits are not YAML keys."""
        assert is_frontmatter(["123: value"]) is False

    def test_hyphen_start_not_frontmatter(self):
        """Lines starting with hyphens (list items) are not YAML keys."""
        assert is_frontmatter(["- item 1"]) is False

    def test_yaml_with_comment(self):
        """Lines starting with # comment are not YAML keys."""
        assert is_frontmatter(["# comment"]) is False

    def test_underscore_key(self):
        """Keys with underscores are valid YAML."""
        assert is_frontmatter(["class: my-class"]) is True

    def test_yaml_key_with_spaces(self):
        """YAML key with trailing spaces is still valid."""
        assert is_frontmatter(["layout : center"]) is True


# ---------------------------------------------------------------------------
# title_of
# ---------------------------------------------------------------------------


class TestTitleOf:
    """Tests for title_of — extracts title from a slide block."""

    def test_h1_title(self):
        assert title_of(["# Introduction"]) == "Introduction"

    def test_h1_with_leading_whitespace(self):
        assert title_of(["  # Spaced Title"]) == "Spaced Title"

    def test_h1_trailing_whitespace(self):
        assert title_of(["# Title  "]) == "Title"

    def test_no_h1_uses_first_line(self):
        assert title_of(["First line content"]) == "[no-h1] First line content"

    def test_no_h1_truncates_long_line(self):
        long_line = "A" * 100
        result = title_of([long_line])
        assert result.startswith("[no-h1] ")
        assert len(result) < len(long_line) + 10  # truncated

    def test_empty_block(self):
        assert title_of([]) == "[empty]"

    def test_whitespace_only(self):
        assert title_of(["  ", "  "]) == "[empty]"

    def test_h2_not_used_as_title(self):
        """Only H1 (#) is used; H2 (##) falls through to first-line fallback."""
        result = title_of(["## Subtitle"])
        assert result == "[no-h1] ## Subtitle"

    def test_h1_in_middle(self):
        """First H1 in the block is used, even if not the first line."""
        assert title_of(["some text", "# Found Title", "more text"]) == "Found Title"

    def test_first_h1_wins(self):
        """When multiple H1 lines exist, the first one is used."""
        assert title_of(["# First", "# Second"]) == "First"

    def test_no_h1_ignores_empty_lines(self):
        """Empty lines before the first content line are skipped."""
        assert title_of(["", "  ", "Real content"]) == "[no-h1] Real content"
