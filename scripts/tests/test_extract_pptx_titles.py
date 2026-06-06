"""Tests for scripts/extract_pptx_titles.py — pure function unit tests.

Tests cover the SLIDE_MARKER regex and the extract() function via
filesystem mocking (tmp_path). The script reads a markdown file with
slide number markers and extracts titles.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from extract_pptx_titles import SLIDE_MARKER


# ---------------------------------------------------------------------------
# SLIDE_MARKER regex
# ---------------------------------------------------------------------------


class TestSlideMarkerRegex:
    """Tests for the SLIDE_MARKER regex pattern."""

    def test_standard_marker(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 1 -->")
        assert m is not None
        assert m.group(1) == "1"

    def test_multi_digit_number(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 42 -->")
        assert m is not None
        assert m.group(1) == "42"

    def test_extra_spaces(self):
        m = SLIDE_MARKER.match("<!--  Slide number: 3  -->")
        assert m is not None
        assert m.group(1) == "3"

    def test_no_spaces_around_number(self):
        m = SLIDE_MARKER.match("<!-- Slide number:7 -->")
        assert m is not None
        assert m.group(1) == "7"

    def test_not_a_marker(self):
        assert SLIDE_MARKER.match("Some regular text") is None

    def test_partial_marker(self):
        assert SLIDE_MARKER.match("<!-- Slide -->") is None

    def test_marker_in_middle(self):
        """Marker only matches at line start."""
        assert SLIDE_MARKER.match("  <!-- Slide number: 1 -->") is None

    def test_leading_whitespace_fails(self):
        """Indentation before marker prevents match."""
        assert SLIDE_MARKER.match("\t<!-- Slide number: 1 -->") is None

    def test_zero_number(self):
        m = SLIDE_MARKER.match("<!-- Slide number: 0 -->")
        assert m is not None
        assert m.group(1) == "0"

    def test_case_sensitive(self):
        """Pattern is case-sensitive."""
        assert SLIDE_MARKER.match("<!-- slide number: 1 -->") is None

    def test_case_number_lowercase(self):
        """'Slide number' is expected casing."""
        assert SLIDE_MARKER.match("<!-- SLIDE NUMBER: 1 -->") is None


# ---------------------------------------------------------------------------
# extract function (via tmp_path)
# ---------------------------------------------------------------------------


class TestExtract:
    """Tests for extract() using temporary files."""

    def test_basic_slides(self, tmp_path):
        """Extract titles from basic slide markers with H1 headings."""
        content = """<!-- Slide number: 1 -->
# Title One

<!-- Slide number: 2 -->
# Title Two
"""
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")

        from extract_pptx_titles import extract
        # extract prints to stdout, capture it
        import io
        from unittest.mock import patch

        with patch("sys.stdout", new_callable=io.StringIO) as mock_out:
            extract(f)
        output = mock_out.getvalue()
        assert "1: Title One" in output
        assert "2: Title Two" in output

    def test_no_h1_uses_first_line(self, tmp_path):
        """Slides without H1 use first non-empty, non-comment line."""
        content = """<!-- Slide number: 1 -->
Some content line

<!-- Slide number: 2 -->
# Has Title
"""
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")

        from extract_pptx_titles import extract
        import io
        from unittest.mock import patch

        with patch("sys.stdout", new_callable=io.StringIO) as mock_out:
            extract(f)
        output = mock_out.getvalue()
        assert "1: [no-h1] Some content line" in output
        assert "2: Has Title" in output

    def test_empty_slide(self, tmp_path):
        """Slide with only a marker gets [empty] title."""
        content = """<!-- Slide number: 1 -->
<!-- Slide number: 2 -->
# Real Title
"""
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")

        from extract_pptx_titles import extract
        import io
        from unittest.mock import patch

        with patch("sys.stdout", new_callable=io.StringIO) as mock_out:
            extract(f)
        output = mock_out.getvalue()
        assert "1: [empty]" in output
        assert "2: Real Title" in output

    def test_single_slide(self, tmp_path):
        """Single slide extraction."""
        content = "<!-- Slide number: 1 -->\n# Only Slide\n"
        f = tmp_path / "test.md"
        f.write_text(content, encoding="utf-8")

        from extract_pptx_titles import extract
        import io
        from unittest.mock import patch

        with patch("sys.stdout", new_callable=io.StringIO) as mock_out:
            extract(f)
        output = mock_out.getvalue()
        assert "1: Only Slide" in output

    def test_empty_file(self, tmp_path):
        """Empty file produces no output."""
        f = tmp_path / "empty.md"
        f.write_text("", encoding="utf-8")

        from extract_pptx_titles import extract
        import io
        from unittest.mock import patch

        with patch("sys.stdout", new_callable=io.StringIO) as mock_out:
            extract(f)
        assert mock_out.getvalue() == ""
