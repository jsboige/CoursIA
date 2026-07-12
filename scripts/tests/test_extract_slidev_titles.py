"""Tests for extract_slidev_titles.py — Slidev slide title extraction."""

import sys
from io import StringIO
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_slidev_titles import split_blocks, is_frontmatter, title_of, extract


# ---------------------------------------------------------------------------
# split_blocks
# ---------------------------------------------------------------------------


class TestSplitBlocks:
    """Tests for the `---`-based block splitter."""

    def test_empty_input(self):
        assert split_blocks([]) == [[]]

    def test_no_separators(self):
        lines = ["line1\n", "line2\n"]
        blocks = split_blocks(lines)
        assert len(blocks) == 1
        assert blocks[0] == ["line1\n", "line2\n"]

    def test_single_separator(self):
        lines = ["---\n"]
        blocks = split_blocks(lines)
        assert len(blocks) == 2
        assert blocks[0] == []
        assert blocks[1] == []

    def test_two_separators(self):
        lines = ["---\n", "content\n", "---\n"]
        blocks = split_blocks(lines)
        assert len(blocks) == 3
        assert blocks[0] == []
        assert blocks[1] == ["content\n"]
        assert blocks[2] == []

    def test_trailing_content(self):
        lines = ["---\n", "fm\n", "---\n", "slide content\n"]
        blocks = split_blocks(lines)
        assert len(blocks) == 3
        assert blocks[2] == ["slide content\n"]

    def test_separator_with_spaces(self):
        """Separator with only whitespace on the line is still a separator."""
        lines = ["---\n", "  ---  \n", "slide\n"]
        blocks = split_blocks(lines)
        # "  ---  ".strip() == "---" => separator
        assert len(blocks) == 3

    def test_not_separator_with_text(self):
        lines = ["--- text\n", "content\n"]
        blocks = split_blocks(lines)
        assert len(blocks) == 1
        assert blocks[0] == ["--- text\n", "content\n"]


# ---------------------------------------------------------------------------
# is_frontmatter
# ---------------------------------------------------------------------------


class TestIsFrontmatter:
    """Tests for per-slide frontmatter detection."""

    def test_empty_block(self):
        assert is_frontmatter([]) is False

    def test_whitespace_only(self):
        assert is_frontmatter(["  \n", "\n"]) is False

    def test_yaml_key(self):
        assert is_frontmatter(["layout: default\n"]) is True

    def test_yaml_key_with_nested(self):
        assert is_frontmatter(["layout: cover\n", "background: /img.png\n"]) is True

    def test_heading_is_not_frontmatter(self):
        assert is_frontmatter(["# My Title\n", "layout: default\n"]) is False

    def test_no_yaml_key(self):
        assert is_frontmatter(["Some content\n"]) is False

    def test_yaml_key_complex(self):
        assert is_frontmatter(["transition: slide-left\n", "css: unocss\n"]) is True

    def test_indented_yaml_not_detected(self):
        """Indented YAML lines don't start with [A-Za-z_] at column 0."""
        assert is_frontmatter(["  layout: default\n"]) is False


# ---------------------------------------------------------------------------
# title_of
# ---------------------------------------------------------------------------


class TestTitleOf:
    """Tests for slide title extraction."""

    def test_h1_title(self):
        assert title_of(["# Introduction\n"]) == "Introduction"

    def test_h1_with_leading_whitespace(self):
        assert title_of(["  # Spaced Title\n"]) == "Spaced Title"

    def test_no_h1_uses_first_line(self):
        assert title_of(["Some content\n"]) == "[no-h1] Some content"

    def test_no_h1_truncates_at_80(self):
        long_line = "x" * 100
        result = title_of([long_line + "\n"])
        assert result.startswith("[no-h1] ")
        # First line is truncated at 80 chars in the display
        assert len(result) <= len("[no-h1] ") + 80

    def test_empty_block(self):
        assert title_of([]) == "[empty]"

    def test_whitespace_only_lines(self):
        assert title_of(["  \n", "\n", "visible\n"]) == "[no-h1] visible"

    def test_h2_not_used_as_title(self):
        """Only # (h1) is used, not ## (h2)."""
        assert title_of(["## Subtitle\n", "text\n"]) == "[no-h1] ## Subtitle"

    def test_first_h1_wins(self):
        assert title_of(["# First\n", "# Second\n"]) == "First"


# ---------------------------------------------------------------------------
# extract (integration)
# ---------------------------------------------------------------------------


class TestExtract:
    """Integration tests for the full extract pipeline."""

    def test_minimal_slidev(self, tmp_path, capsys):
        md = tmp_path / "slides.md"
        md.write_text(
            "---\ntitle: Test\n---\n"
            "# Slide 1\n\nContent\n"
            "---\n"
            "# Slide 2\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: Slide 1" in out
        assert "2: Slide 2" in out

    def test_per_slide_frontmatter(self, tmp_path, capsys):
        md = tmp_path / "slides.md"
        md.write_text(
            "---\ntitle: Test\n---\n"
            "# Slide 1\n"
            "---\n"
            "layout: cover\n"
            "---\n"
            "# Slide 2\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: Slide 1" in out
        assert "2: Slide 2" in out

    def test_no_h1_slide(self, tmp_path, capsys):
        md = tmp_path / "slides.md"
        md.write_text(
            "---\ntitle: Test\n---\n"
            "Just a paragraph\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: [no-h1] Just a paragraph" in out

    def test_empty_file(self, tmp_path, capsys):
        md = tmp_path / "slides.md"
        md.write_text("", encoding="utf-8")
        extract(md)
        out = capsys.readouterr().out
        assert out == ""

    def test_root_fm_only_produces_empty_slide(self, tmp_path, capsys):
        """Trailing --- produces one empty slide (split_blocks creates trailing block)."""
        md = tmp_path / "slides.md"
        md.write_text("---\ntitle: Test\n---\n", encoding="utf-8")
        extract(md)
        out = capsys.readouterr().out
        assert "1: [empty]" in out

    def test_three_slides(self, tmp_path, capsys):
        md = tmp_path / "slides.md"
        md.write_text(
            "---\ntitle: Test\n---\n"
            "# One\n---\n"
            "# Two\n---\n"
            "# Three\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: One" in out
        assert "2: Two" in out
        assert "3: Three" in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
