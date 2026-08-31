"""Tests for the HTML-block markdown detector (issue #13216).

The suite is written around the failure mode the detector exists for -- a line of
block markdown swallowed because it follows an opening tag with no blank line -- and
around the OVER-accusation that a naive version of the same detector produced.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scan_slides_html_block_markdown import iter_decks, scan_file, scan_text  # noqa: E402


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


def test_lone_closing_tag_swallows_following_block_markdown():
    """The closing-tag form of HTML-block type 6 (CommonMark) — a lone `</div>`
    alone on its line opens the block just like `<div>` does.

    Issue #13345 found one live occurrence: `slides/01-introduction`, where a
    bare `</div>` swallowed three list bullets rendered as literal text. The
    detector must catch this form, not only the opening-tag form.
    """
    text = "</div>\n- Behaviourism\n"
    assert scan_text(text) == [(2, "- Behaviourism")]


def test_blank_line_after_closing_tag_is_clean():
    """The burn-down shape from issue #13345: a blank line after the lone
    `</div>` makes the next line parse normally. Verifies the fix path."""
    text = "</div>\n\n- Behaviourism\n"
    assert scan_text(text) == []


def test_corpus_is_zero_on_main():
    """The ratchet the PR #13681 body claims to hold.

    Scans the rendered Slidev/Marp corpus (``slides/<deck>/*.md``, top-level only
    — see ``iter_decks`` docstring for the non-recursive convention) and asserts
    zero violations. This is what the body of PR #13681 calls "the test IS the
    ratchet": if the defect class reappears on any deck, this test goes red in
    local pytest BEFORE the workflow wiring of #13364 lands.

    Pre-PR #13681 corpus measurement: 1 live occurrence at ``slides/01-introduction``
    L598 (`- Behaviourism` swallowed by the bare `</div>` L597). Post-PR measurement
    on the same commit: 0. The blank line after `</div>` is the fix; this test
    asserts the post-fix state holds across the whole rendered corpus.

    Skipped if the ``slides/`` directory is absent (e.g. CI environment where only
    a partial checkout is present).
    """
    repo_root = Path(__file__).resolve().parents[3]
    slides_root = repo_root / "slides"
    if not slides_root.is_dir():
        pytest.skip("slides/ not present in this checkout (partial CI checkout)")

    violations = {}
    for deck in iter_decks(slides_root):
        hits = scan_file(deck)
        if hits:
            violations[deck.as_posix()] = hits

    assert violations == {}, (
        "rendered Slidev/Marp corpus is expected to hold zero HTML-block-swallowed "
        "markdown after PR #13681; found: %r" % violations
    )


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


# --- closing tags open a block too (found by review on #13218) ---------------
#
# CommonMark HTML block type 6 opens on `</tag>` exactly as it does on `<tag>`.
# The detector shipped blind to that half, so the ratchet would have let the
# whole class through forever. These tests are the faux-negatif controls: each
# one names a shape the pattern MUST catch, so a future narrowing of the regex
# fails here instead of silently rendering a smaller, cleaner-looking count.


@pytest.mark.parametrize(
    "markdown",
    ["- Behaviourism", "**gras**", "## Titre", "1. premier", "> citation", "| a | b |"],
)
def test_bare_closing_tag_swallows_every_block_construct(markdown):
    """The founder case: `</div>` alone, then block markdown.

    Verified at the engine Slidev uses -- markdown_it.MarkdownIt("commonmark")
    renders "</div>\n- Behaviourism\n" unchanged, with no <li>: the bullet comes
    back as literal text on the slide.
    """
    assert scan_text("</div>\n" + markdown + "\n") == [(2, markdown)]


def test_bare_closing_tag_followed_by_blank_line_is_clean():
    """The positive control for the FIX itself: a blank line closes the block.

    This is the exact edit the companion fixer applies, so if this test ever
    fails the repair recipe is wrong, not just the detector.
    """
    assert scan_text("</div>\n\n- Behaviourism\n") == []


def test_closing_tag_with_attributes_is_not_a_thing_but_does_not_crash():
    assert scan_text("</div >\n- a\n") == [(2, "- a")]


# --- the exception must NOT swallow genuinely self-contained lines -----------


def test_inline_element_closed_on_its_line_still_opens_no_block():
    """Negative control bounding _BARE_CLOSING_TAG.

    `<span>x</span>` ends in `</span>` just like the bare closing tag does. It
    must stay excluded -- markdown-it renders it as a paragraph and the next
    line as a real list. Widening _SELF_CONTAINED carelessly would break this.
    """
    assert scan_text("<span>x</span>\n- Behaviourism\n") == []


def test_self_closing_tag_still_opens_no_block_after_the_widening():
    assert scan_text('<img src="x.png" />\n- a\n') == []


def test_closing_tag_with_trailing_content_is_out_of_scope_not_harmless():
    """A DECLARED scope limit, not a non-defect -- written out so the gap is
    visible instead of implied by a passing test.

    markdown-it DOES swallow here: `</div> et du texte` opens a block just as
    the lone form does, so `- a` comes back literal. The detector still
    ignores it, because the rule it enforces is "a tag ALONE on its line" --
    the same narrowing the opening-tag side already applies (see
    test_tag_with_trailing_content_is_not_a_lone_opening_tag). Widening both
    sides is a separate decision with its own false-positive budget; what
    must not happen is this test reading as though the engine were fine.
    """
    assert scan_text("</div> et du texte\n- a\n") == []
