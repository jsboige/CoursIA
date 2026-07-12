"""Tests for scripts/extract_slidev_titles.py and scripts/extract_pptx_titles.py.

Tests focus on pure functions: split_blocks, is_frontmatter, title_of (slidev),
and SLIDE_MARKER-based extraction (pptx). File reading uses tmp_path.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_slidev_titles import split_blocks, is_frontmatter, title_of
from extract_pptx_titles import SLIDE_MARKER


# ---------------------------------------------------------------------------
# extract_slidev_titles — split_blocks
# ---------------------------------------------------------------------------

class TestSplitBlocks:
    def test_simple_two_blocks(self):
        lines = ["aaa", "---", "bbb"]
        blocks = split_blocks(lines)
        assert len(blocks) == 2
        assert blocks[0] == ["aaa"]
        assert blocks[1] == ["bbb"]

    def test_multiple_separators(self):
        lines = ["a", "---", "b", "---", "c"]
        blocks = split_blocks(lines)
        assert len(blocks) == 3
        assert blocks[2] == ["c"]

    def test_no_separator(self):
        lines = ["aaa", "bbb"]
        blocks = split_blocks(lines)
        assert len(blocks) == 1
        assert blocks[0] == ["aaa", "bbb"]

    def test_consecutive_separators(self):
        lines = ["---", "---", "content"]
        blocks = split_blocks(lines)
        assert len(blocks) == 3
        assert blocks[0] == []
        assert blocks[1] == []
        assert blocks[2] == ["content"]

    def test_empty_input(self):
        blocks = split_blocks([])
        assert len(blocks) == 1
        assert blocks[0] == []

    def test_trailing_separator(self):
        lines = ["content", "---"]
        blocks = split_blocks(lines)
        assert len(blocks) == 2
        assert blocks[1] == []

    def test_separator_with_whitespace(self):
        lines = ["a", "  ---  ", "b"]
        blocks = split_blocks(lines)
        assert len(blocks) == 2


# ---------------------------------------------------------------------------
# extract_slidev_titles — is_frontmatter
# ---------------------------------------------------------------------------

class TestIsFrontmatter:
    def test_yaml_key_value(self):
        assert is_frontmatter(["layout: default"]) is True

    def test_yaml_with_indent_not_matched(self):
        """Indented YAML keys don't match the regex (starts with space)."""
        assert is_frontmatter(["  props:", "    a: 1"]) is False

    def test_heading_is_not_frontmatter(self):
        assert is_frontmatter(["# Title"]) is False

    def test_empty_block(self):
        assert is_frontmatter([]) is False

    def test_only_whitespace(self):
        assert is_frontmatter(["  ", "  "]) is False

    def test_comment_only(self):
        assert is_frontmatter(["<!-- comment -->"]) is False

    def test_mixed_heading_and_yaml(self):
        """If block has a heading, it's not pure frontmatter."""
        assert is_frontmatter(["layout: default", "# Title"]) is False

    def test_numeric_start_not_yaml(self):
        assert is_frontmatter(["123: value"]) is False

    def test_underscore_key(self):
        assert is_frontmatter(["_key: value"]) is True

    def test_kebab_key(self):
        assert is_frontmatter(["my-key: value"]) is True


# ---------------------------------------------------------------------------
# extract_slidev_titles — title_of
# ---------------------------------------------------------------------------

class TestTitleOf:
    def test_h1_heading(self):
        assert title_of(["# Hello World"]) == "Hello World"

    def test_h1_with_leading_whitespace(self):
        assert title_of(["  # Spaced Title  "]) == "Spaced Title"

    def test_no_h1_falls_back_to_content(self):
        result = title_of(["Some content here"])
        assert result == "[no-h1] Some content here"

    def test_no_h1_truncates_long_line(self):
        long_line = "x" * 100
        result = title_of([long_line])
        assert result.startswith("[no-h1] ")
        assert len(result) <= len("[no-h1] ") + 80

    def test_empty_block(self):
        assert title_of([]) == "[empty]"

    def test_only_whitespace_lines(self):
        assert title_of(["  ", "  "]) == "[empty]"

    def test_skips_h2_and_h3(self):
        """Only H1 (# ) counts as title, not ## or ###."""
        result = title_of(["## Subtitle", "### Sub-sub", "Content"])
        assert result == "[no-h1] ## Subtitle"

    def test_first_h1_wins(self):
        result = title_of(["# First", "# Second"])
        assert result == "First"

    def test_skips_empty_before_content(self):
        result = title_of(["", "", "Actual content"])
        assert result == "[no-h1] Actual content"


# ---------------------------------------------------------------------------
# extract_pptx_titles — SLIDE_MARKER regex
# ---------------------------------------------------------------------------

class TestSlideMarker:
    def test_standard_marker(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 1 -->")
        assert m is not None
        assert m.group(1) == "1"

    def test_with_extra_whitespace(self):
        m = SLIDE_MARKER.match("<!--  Slide number:  42  -->")
        assert m is not None
        assert m.group(1) == "42"

    def test_no_match_plain_comment(self):
        assert SLIDE_MARKER.match("<!-- some comment -->") is None

    def test_no_match_regular_line(self):
        assert SLIDE_MARKER.match("Just a line") is None

    def test_multidigit_number(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 123 -->")
        assert m is not None
        assert m.group(1) == "123"

    def test_zero_number(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 0 -->")
        assert m is not None
        assert m.group(1) == "0"


# ---------------------------------------------------------------------------
# extract_pptx_titles — extract (integration with tmp_path)
# ---------------------------------------------------------------------------

class TestPptxExtract:
    def test_basic_extraction(self, tmp_path, capsys):
        from extract_pptx_titles import extract

        content = (
            "<!-- Slide number: 1 -->\n"
            "# Introduction\n"
            "Some content\n"
            "<!-- Slide number: 2 -->\n"
            "# Conclusion\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        assert "1: Introduction" in output
        assert "2: Conclusion" in output

    def test_no_heading_uses_content(self, tmp_path, capsys):
        from extract_pptx_titles import extract

        content = (
            "<!-- Slide number: 1 -->\n"
            "First line content\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        assert "1:" in output
        assert "[no-h1]" in output

    def test_empty_slide(self, tmp_path, capsys):
        from extract_pptx_titles import extract

        content = "<!-- Slide number: 1 -->\n"
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        assert "1: [empty]" in output


# ---------------------------------------------------------------------------
# extract_slidev_titles — extract (integration with tmp_path)
# ---------------------------------------------------------------------------

class TestSlidevExtract:
    def test_basic_extraction(self, tmp_path, capsys):
        from extract_slidev_titles import extract

        content = (
            "---\n"
            "title: My Presentation\n"
            "---\n"
            "# Slide One\n"
            "Content\n"
            "---\n"
            "# Slide Two\n"
        )
        f = tmp_path / "slides.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        assert "1: Slide One" in output
        assert "2: Slide Two" in output

    def test_per_slide_frontmatter(self, tmp_path, capsys):
        from extract_slidev_titles import extract

        # No gap between closing root FM and per-slide FM
        content = (
            "---\n"
            "title: Root\n"
            "---\n"
            "---\n"
            "layout: center\n"
            "---\n"
            "# Centered Slide\n"
        )
        f = tmp_path / "slides.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        # Empty block between root FM close and per-slide FM open creates [empty] slide 1
        # Per-slide FM merges with next block -> Centered Slide is slide 2
        assert "Centered Slide" in output

    def test_no_heading_slide(self, tmp_path, capsys):
        from extract_slidev_titles import extract

        content = (
            "---\n"
            "title: Root\n"
            "---\n"
            "Just content without heading\n"
        )
        f = tmp_path / "slides.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        output = capsys.readouterr().out
        assert "1:" in output
        assert "[no-h1]" in output
