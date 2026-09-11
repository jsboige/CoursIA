"""Tests for extract_slidev_titles.py — Slidev slide parsing."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
from extract_slidev_titles import split_blocks, is_frontmatter, title_of, extract


# --- split_blocks ---


class TestSplitBlocks:
    def test_single_block(self):
        lines = ["# Hello", "World"]
        result = split_blocks(lines)
        assert result == [["# Hello", "World"]]

    def test_two_blocks_separated(self):
        lines = ["# Slide 1", "---", "# Slide 2"]
        result = split_blocks(lines)
        assert len(result) == 2
        assert result[0] == ["# Slide 1"]
        assert result[1] == ["# Slide 2"]

    def test_empty_input(self):
        result = split_blocks([])
        assert result == [[]]

    def test_only_separators(self):
        lines = ["---", "---"]
        result = split_blocks(lines)
        assert result == [[], [], []]

    def test_frontmatter_and_slides(self):
        lines = [
            "---",
            "title: My Presentation",
            "---",
            "# Slide 1",
            "Content",
            "---",
            "# Slide 2",
        ]
        result = split_blocks(lines)
        # blocks: [] | [title: ...] | [# Slide 1, Content] | [# Slide 2]
        assert len(result) == 4
        assert result[0] == []
        assert result[1] == ["title: My Presentation"]
        assert result[2] == ["# Slide 1", "Content"]
        assert result[3] == ["# Slide 2"]

    # --- ported from deleted legacy scripts/tests/test_extract_slidev_titles.py
    # shadow (#10066 consolidation): separator edge cases the canon lacked. ---

    def test_separator_with_spaces(self):
        """A separator line with only surrounding whitespace is still a separator
        (split_blocks matches on ``line.strip() == '---'``)."""
        lines = ["---", "  ---  ", "slide"]
        result = split_blocks(lines)
        assert len(result) == 3

    def test_not_separator_with_text(self):
        """``--- text`` (text after the dashes) is NOT a separator."""
        lines = ["--- text", "content"]
        result = split_blocks(lines)
        assert len(result) == 1
        assert result[0] == ["--- text", "content"]

    def test_single_separator(self):
        """A lone separator yields two empty blocks (minimal boundary case)."""
        assert split_blocks(["---"]) == [[], []]


# --- is_frontmatter ---


class TestIsFrontmatter:
    def test_yaml_key_value(self):
        assert is_frontmatter(["layout: default"]) is True

    def test_yaml_with_number_value(self):
        assert is_frontmatter(["level: 2"]) is True

    def test_not_frontmatter_has_heading(self):
        assert is_frontmatter(["# Title"]) is False

    def test_not_frontmatter_no_yaml(self):
        assert is_frontmatter(["Just text"]) is False

    def test_empty_block(self):
        assert is_frontmatter([]) is False

    def test_whitespace_only(self):
        assert is_frontmatter(["  ", "\t"]) is False

    def test_yaml_key_with_underscore(self):
        # Fixture corrected in the #14730 consolidation: the key must START with
        # an underscore to test what the name announces. The previous fixture
        # ("transition: slide") only exercised a plain alpha key, already
        # covered by test_yaml_key_value. Ported from the legacy suite.
        assert is_frontmatter(["_transition: slide"]) is True

    def test_yaml_key_with_dash(self):
        # Fixture corrected in the #14730 consolidation: a dashed key exercises
        # the [A-Za-z0-9_-]* part of YAML_KEY. Ported from the legacy suite.
        assert is_frontmatter(["text-align: center"]) is True

    def test_mixed_yaml_and_heading(self):
        """Block with both YAML key and heading → NOT frontmatter (heading wins)."""
        assert is_frontmatter(["layout: default", "# Title"]) is False

    def test_multiline_yaml(self):
        block = ["layout: cover", "background: /images/bg.png"]
        assert is_frontmatter(block) is True

    # --- ported from deleted legacy scripts/tests/test_extract_slidev_titles.py
    # shadow (#10066 consolidation): the only frontmatter edge case the canon
    # lacked — indented YAML must NOT be detected (YAML_KEY anchors at ^). ---

    def test_indented_yaml_not_detected(self):
        """An indented YAML line does not start with [A-Za-z_] at column 0, so it
        is not treated as frontmatter (anchors the YAML_KEY regex)."""
        assert is_frontmatter(["  layout: default"]) is False

    # --- ported from the deleted legacy scripts/tests/test_extract_titles.py
    # (#14730 consolidation): negative edges the canon lacked — an HTML-comment
    # block and a numeric-start key must not read as frontmatter. ---

    def test_comment_only(self):
        """A block of only HTML comments is not frontmatter (no YAML key)."""
        assert is_frontmatter(["<!-- comment -->"]) is False

    def test_numeric_start_not_yaml(self):
        """A numeric-start key does not match YAML_KEY (anchors [A-Za-z_])."""
        assert is_frontmatter(["123: value"]) is False


# --- title_of ---


class TestTitleOf:
    def test_h1_title(self):
        assert title_of(["# My Slide"]) == "My Slide"

    def test_h1_with_whitespace(self):
        assert title_of(["#   Spaced Title  "]) == "Spaced Title"

    def test_no_h1_first_nonempty(self):
        block = ["", "Some text content", "More text"]
        result = title_of(block)
        assert result.startswith("[no-h1]")
        assert "Some text content" in result

    def test_empty_block(self):
        assert title_of([]) == "[empty]"

    def test_whitespace_only_block(self):
        assert title_of(["  ", "\t"]) == "[empty]"

    def test_truncation_long_line(self):
        long_line = "x" * 200
        result = title_of([long_line])
        assert len(result) <= 88  # "[no-h1] " + max 80 chars

    def test_h1_after_blank_lines(self):
        block = ["", "", "# Actual Title"]
        assert title_of(block) == "Actual Title"

    def test_multiple_h1_first_wins(self):
        block = ["# First", "# Second"]
        assert title_of(block) == "First"

    def test_h2_not_used_as_title(self):
        block = ["## Subtitle", "# Real Title"]
        assert title_of(block) == "Real Title"

    # --- ported from the deleted legacy scripts/tests/test_extract_titles.py
    # (#14730 consolidation): edges the canon lacked. ---

    def test_h1_with_leading_whitespace(self):
        """An h1 with whitespace BEFORE the # still titles (title_of strips the
        line before matching, so indentation cannot hide the heading)."""
        assert title_of(["  # Spaced Title  "]) == "Spaced Title"

    def test_skips_h2_and_h3(self):
        """Without any h1, h2/h3 lines are NOT promoted to title: the first
        non-empty line becomes [no-h1] content, hash signs included."""
        assert title_of(["## Subtitle", "### Sub-sub", "Content"]) == "[no-h1] ## Subtitle"


# --- extract (integration) ---
#
# Ported verbatim from the deleted legacy scripts/tests/test_extract_slidev_titles.py
# shadow (#10066 consolidation). The canon previously tested only the pure
# helpers (split_blocks / is_frontmatter / title_of) and never exercised the
# ``extract()`` integration pipeline — reading a real .md file, dropping the
# root frontmatter, interleaving per-slide frontmatter, and printing
# ``idx: title`` lines. The module collision (both files shared the basename
# ``test_extract_slidev_titles``) meant the canon's 24 helper tests were DEAD
# in CI whenever both ran; deleting the legacy after porting these 6
# integration tests resurrects the 24 AND unifies integration coverage in the
# canonical home.


class TestExtract:
    """Integration tests for the full ``extract`` pipeline."""

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
        """A trailing ``---`` produces one empty slide (split_blocks creates a
        trailing block)."""
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

    # --- ported from the deleted legacy scripts/tests/test_extract_titles.py
    # (#14730 consolidation): the adjacency edge — root FM directly followed
    # by per-slide FM, with no slide content between them. ---

    def test_slide_fm_directly_after_root_fm(self, tmp_path, capsys):
        """Per-slide frontmatter immediately after the root FM (no gap): the
        empty block between them becomes slide 1 ([empty]), and the per-slide
        FM merges with the following block, which becomes slide 2."""
        md = tmp_path / "slides.md"
        md.write_text(
            "---\ntitle: Root\n---\n"
            "---\nlayout: center\n---\n"
            "# Centered Slide\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: [empty]" in out
        assert "2: Centered Slide" in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
