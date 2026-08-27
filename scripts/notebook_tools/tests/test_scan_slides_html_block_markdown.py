"""Tests for the HTML-block markdown detector (issue #13216).

The suite is written around the failure mode the detector exists for -- a line of
block markdown swallowed because it follows an opening tag with no blank line -- and
around the OVER-accusation that a naive version of the same detector produced.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scan_slides_html_block_markdown import scan_text  # noqa: E402


# --- the defect itself -------------------------------------------------------


def test_bold_swallowed_by_an_html_block_is_reported():
    """The canonical shape from PR #13096, verbatim."""
    text = (
        '<div class="grid grid-cols-2 gap-5 -mt-2">\n'
        "<div>\n"
        "**Environnement multi-agents**\n"
    )
    hits = scan_text(text)
    assert len(hits) == 1
    line, offending = hits[0]
    assert line == 3, "the reported line must be the swallowed markdown, not the tag"
    assert offending == "**Environnement multi-agents**"


def test_blank_line_after_the_tag_is_clean():
    """The in-artifact positive control: the SAME construct, one blank line later.

    Both forms coexisted in `slides/S3-acculturation/slides.md`; the blank line was
    the only variable between the broken left column and the working right one.
    """
    text = "<div>\n\n**Optimisation de strategies**\n"
    assert scan_text(text) == []


@pytest.mark.parametrize(
    "markdown",
    [
        "- N-grams",
        "1. Premier point",
        "## Un titre",
        "> une citation",
        "| col | col |",
        "**gras**",
    ],
)
def test_every_block_level_construct_is_caught(markdown):
    """A detector is validated by its FALSE NEGATIVES: name the shapes it must
    catch and check it catches them, rather than trusting its hits."""
    assert len(scan_text("<div>\n%s\n" % markdown)) == 1, markdown


# --- and what it must NOT report ---------------------------------------------


def test_inline_markdown_is_not_reported():
    """The over-accusation that the first version of this detector produced.

    Inline emphasis inside an HTML block renders acceptably; flagging it reported 7
    hits on a file that holds 0 real defects. Only block-level constructs are
    destroyed outright, so only those are reported.
    """
    text = "<div>\nDu texte courant avec de l'*emphase* et du `code`.\n"
    assert scan_text(text) == []


def test_nested_tag_on_the_next_line_is_not_reported():
    """A tag keeps the block open but carries no markdown; the line after IT is
    examined on its own iteration, so reporting here would double-count."""
    text = "<div>\n<span>\n"
    assert scan_text(text) == []


def test_self_closing_tag_opens_no_block():
    assert scan_text('<img src="x.png" />\n**gras**\n') == []


def test_tag_closed_on_its_own_line_opens_no_block():
    assert scan_text("<span>inline</span>\n**gras**\n") == []


def test_tag_with_trailing_content_is_not_a_lone_opening_tag():
    """Only a tag ALONE on its line starts the shape this rule is about."""
    assert scan_text("<div>du texte\n**gras**\n") == []


def test_opening_tag_on_the_last_line_does_not_crash():
    assert scan_text("<div>") == []


def test_several_defects_are_all_reported_in_order():
    text = "<div>\n**a**\n\n<div>\n- b\n"
    assert [line for line, _ in scan_text(text)] == [2, 5]
