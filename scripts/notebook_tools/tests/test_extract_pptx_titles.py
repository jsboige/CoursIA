"""Tests for extract_pptx_titles.py — PPTX slide title extraction."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
from extract_pptx_titles import extract, SLIDE_MARKER


# --- SLIDE_MARKER regex ---


class TestSlideMarker:
    def test_standard_marker(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 1 -->")
        assert m is not None
        assert m.group(1) == "1"

    def test_marker_with_extra_spaces(self):
        m = SLIDE_MARKER.match("<!--  Slide number:  42  -->")
        assert m is not None
        assert m.group(1) == "42"

    def test_not_marker(self):
        assert SLIDE_MARKER.match("<!-- just a comment -->") is None

    def test_no_marker(self):
        assert SLIDE_MARKER.match("# Title") is None

    def test_marker_multiline(self):
        """Regex anchors to ^ so mid-line comment not matched."""
        assert SLIDE_MARKER.match("text <!-- Slide number: 1 -->") is None


# --- extract (captures stdout, uses tmp_path) ---


class TestExtract:
    def test_basic_slide_titles(self, tmp_path, capsys):
        content = (
            "<!-- Slide number: 1 -->\n"
            "# Introduction\n"
            "\n"
            "<!-- Slide number: 2 -->\n"
            "# Methods\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: Introduction" in out
        assert "2: Methods" in out

    def test_no_heading_uses_first_line(self, tmp_path, capsys):
        content = (
            "<!-- Slide number: 1 -->\n"
            "Some content without heading\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: [no-h1]" in out
        assert "Some content" in out

    def test_empty_slide(self, tmp_path, capsys):
        content = (
            "<!-- Slide number: 1 -->\n"
            "\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: [empty]" in out

    def test_multiple_slides(self, tmp_path, capsys):
        content = (
            "<!-- Slide number: 1 -->\n"
            "# First\n"
            "<!-- Slide number: 2 -->\n"
            "# Second\n"
            "<!-- Slide number: 3 -->\n"
            "# Third\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        lines = [l for l in out.strip().splitlines() if l.strip()]
        assert len(lines) == 3

    def test_no_slide_markers(self, tmp_path, capsys):
        content = "# Just a heading\nSome text\n"
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert out.strip() == ""

    def test_heading_after_blank_lines(self, tmp_path, capsys):
        content = (
            "<!-- Slide number: 1 -->\n"
            "\n"
            "\n"
            "# Actual Title\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: Actual Title" in out

    def test_html_comment_not_used_as_title(self, tmp_path, capsys):
        """HTML comments are skipped when looking for first non-empty line."""
        content = (
            "<!-- Slide number: 1 -->\n"
            "<!-- internal note -->\n"
            "Real content\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        # No h1 → uses first non-empty non-comment line
        assert "Real content" in out

    def test_h2_not_used(self, tmp_path, capsys):
        """Only h1 (# ) is used as title, not h2 (## )."""
        content = (
            "<!-- Slide number: 1 -->\n"
            "## Subtitle\n"
            "# Main Title\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: Main Title" in out

    # --- ported from the deleted legacy scripts/tests/test_extract_pptx_titles.py
    # (#10066 consolidation). These two assertions were UNIQUE to the legacy file:
    # the canonical suite did not cover truncation (impl L37 `s[:80]`) nor the
    # first-of-multiple-h1 ordering. Ported verbatim before deleting the shadow. ---

    def test_truncation_at_80(self, tmp_path, capsys):
        """No-h1 title is truncated to 80 chars (impl: f\"[no-h1] {s[:80]}\")."""
        long_line = "x" * 100
        content = f"<!-- Slide number: 1 -->\n{long_line}\n"
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        # Title portion should be <= 80 chars (plus the "[no-h1] " prefix).
        title_line = out.strip().split(": ", 1)[1]
        assert len(title_line) <= len("[no-h1] ") + 80

    def test_first_h1_wins(self, tmp_path, capsys):
        """When two h1 headings follow a marker, the first is used as title."""
        content = (
            "<!-- Slide number: 1 -->\n"
            "# First\n"
            "# Second\n"
        )
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")
        extract(f)
        out = capsys.readouterr().out
        assert "1: First" in out


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
