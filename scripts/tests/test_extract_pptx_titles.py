"""Tests for extract_pptx_titles.py — PPTX slide title extraction."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_pptx_titles import extract


class TestExtract:
    """Integration tests for PPTX slide title extraction."""

    def test_basic_markers(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n"
            "# Introduction\n\n"
            "Some content\n"
            "<!-- Slide number: 2 -->\n"
            "# Conclusion\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: Introduction" in out
        assert "2: Conclusion" in out

    def test_no_heading_uses_first_line(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n"
            "Just a paragraph\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: [no-h1] Just a paragraph" in out

    def test_empty_slide(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: [empty]" in out

    def test_marker_with_spaces(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!--  Slide number:  5  -->\n"
            "# Spaced\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "5: Spaced" in out

    def test_no_markers(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text("# Title\nNo markers here\n", encoding="utf-8")
        extract(md)
        out = capsys.readouterr().out
        assert out == ""

    def test_empty_file(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text("", encoding="utf-8")
        extract(md)
        out = capsys.readouterr().out
        assert out == ""

    def test_multiple_slides(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n# A\n"
            "<!-- Slide number: 2 -->\n# B\n"
            "<!-- Slide number: 3 -->\n# C\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: A" in out
        assert "2: B" in out
        assert "3: C" in out

    def test_comment_lines_skipped_for_no_h1(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n"
            "<!-- some other comment -->\n"
            "Real content\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: [no-h1] Real content" in out

    def test_truncation_at_80(self, tmp_path, capsys):
        long_line = "x" * 100
        md = tmp_path / "content.md"
        md.write_text(
            f"<!-- Slide number: 1 -->\n{long_line}\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        # Title portion should be <= 80 chars
        title_line = out.strip().split(": ", 1)[1]
        assert len(title_line) <= len("[no-h1] ") + 80

    def test_first_h1_wins(self, tmp_path, capsys):
        md = tmp_path / "content.md"
        md.write_text(
            "<!-- Slide number: 1 -->\n"
            "# First\n# Second\n",
            encoding="utf-8",
        )
        extract(md)
        out = capsys.readouterr().out
        assert "1: First" in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
