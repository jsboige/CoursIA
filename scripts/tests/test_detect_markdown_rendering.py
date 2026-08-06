#!/usr/bin/env python3
"""Unit tests for detect_markdown_rendering.py (markdown-rendering guard, #8352).

The corpus carries pre-existing violations baselined in
``markdown_rendering_baseline.json``; this suite pins the DETECTION LOGIC so a
precision/recall regression cannot ship silently. The focal regression here is
the code-fence awareness added for the ``setext_oversized`` rule: a ``---``/``===``
line INSIDE a fenced-code block is literal text (ASCII art, a cryptarithme divider,
a box-drawing rule) and must NOT be flagged as a setext underline.

Run: ``python -m pytest scripts/tests/test_detect_markdown_rendering.py``.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

import detect_markdown_rendering as dmr  # noqa: E402


def _cell(source: str) -> dict:
    """A markdown cell whose source is a single string (the nbformat list form is
    exercised implicitly via ``_as_text``; the detector handles both)."""
    return {"cell_type": "markdown", "source": source}


def _rules(findings: list[dict]) -> set[str]:
    return {f["rule"] for f in findings}


# ---------------------------------------------------------------- scan_cell core


def test_non_markdown_cell_skipped():
    assert dmr.scan_cell({"cell_type": "code", "source": "# x"}) == []


def test_empty_cell_skipped():
    assert dmr.scan_cell(_cell("   ")) == []


# ----------------------------------------------- setext_oversized: fence awareness


def test_setext_inside_code_fence_not_flagged():
    """The canonical false positive: an ASCII-art divider inside a ``` block."""
    src = (
        "```\n"
        "  S E N D\n"
        "+ M O R E\n"
        "---------\n"  # >=3 dashes -> _SETEXT_RE, but inside the fence
        "M O N E Y\n"
        "```\n"
    )
    assert "setext_oversized" not in _rules(dmr.scan_cell(_cell(src)))


def test_setext_outside_code_fence_still_flagged():
    """Regression guard: real prose underlined by --- (outside any fence) IS flagged."""
    src = (
        "Ceci est un long paragraphe de prose pedagogique qui se termine "
        "sans point final avant la regle.\n"
        "---\n"
    )
    assert "setext_oversized" in _rules(dmr.scan_cell(_cell(src)))


def test_setext_after_closed_fence_flagged():
    """--- outside a CLOSED fence underlining real prose is still flagged."""
    src = (
        "```\n"
        "code block\n"
        "```\n"
        "\n"
        "Un paragraphe de prose explicatif assez long pour depasser le seuil.\n"
        "---\n"
    )
    assert "setext_oversized" in _rules(dmr.scan_cell(_cell(src)))


def test_cryptarithmetic_ascii_art_not_flagged():
    """The exact defect family that shipped as FP on the CSP/Sudoku notebooks:
    a multi-line ASCII diagram inside a code fence containing a `---` divider."""
    src = (
        "Voici le cryptarithme SEND + MORE = MONEY :\n\n"
        "```\n"
        "    S E N D\n"
        "  + M O R E\n"
        "  ---------\n"
        "  M O N E Y\n"
        "```\n"
    )
    assert "setext_oversized" not in _rules(dmr.scan_cell(_cell(src)))


def test_equals_rule_inside_fence_not_flagged():
    """The `===` setext variant, inside a fence, is also literal."""
    src = "texte\n```\npara ligne\n=====\n```\n"
    assert "setext_oversized" not in _rules(dmr.scan_cell(_cell(src)))


# ----------------------------------------------------------- _inside_fence_lines


def test_inside_fence_lines_basic_backtick():
    lines = ["```", "a", "---", "b", "```", "c"]
    assert dmr._inside_fence_lines(lines) == {1, 2, 3}


def test_inside_fence_lines_marker_lines_not_inside():
    """The opening and closing marker lines themselves are NOT inside."""
    lines = ["```", "a", "```"]
    assert dmr._inside_fence_lines(lines) == {1}


def test_inside_fence_lines_tilde_fence():
    lines = ["~~~", "x", "y", "~~~"]
    assert dmr._inside_fence_lines(lines) == {1, 2}


def test_inside_fence_lines_unclosed_fence():
    """An unclosed fence leaves every subsequent line inside (defensive)."""
    lines = ["```", "a", "---", "b"]
    assert dmr._inside_fence_lines(lines) == {1, 2, 3}


def test_inside_fence_lines_mixed_chars_do_not_close():
    """A tilde line inside a backtick block is literal text, not a closer."""
    lines = ["```", "~~~", "a", "```"]
    assert dmr._inside_fence_lines(lines) == {1, 2}


def test_inside_fence_lines_indented_fence():
    lines = ["   ```python", "a", "---", "   ```"]
    assert dmr._inside_fence_lines(lines) == {1, 2}


def test_inside_fence_lines_two_separate_blocks():
    lines = ["```", "a", "```", "b", "```", "c", "```"]
    assert dmr._inside_fence_lines(lines) == {1, 5}


def test_no_fence_returns_empty():
    assert dmr._inside_fence_lines(["a", "---", "b"]) == set()


# ---------------------------------------------------- frontmatter still detected


def test_frontmatter_supersize_still_detected():
    """Regression guard: a real frontmatter-supersize block IS still flagged."""
    src = (
        "---\n"
        "title: \"Un notebook\"\n"
        "cost:\n"
        "  api_usd_est: 0.01\n"
        "  cpu_min: 5\n"
        "---\n"  # directly after a text line -> setext H2 supersize
    )
    rules = _rules(dmr.scan_cell(_cell(src)))
    assert "frontmatter_supersize" in rules


def test_frontmatter_rawyaml_still_detected():
    """Regression guard: raw frontmatter (blank line before closing ---) IS flagged."""
    src = (
        "---\n"
        "title: \"Un notebook\"\n"
        "cost:\n"
        "  cpu_min: 5\n"
        "\n"
        "---\n"
    )
    rules = _rules(dmr.scan_cell(_cell(src)))
    assert "frontmatter_rawyaml" in rules


# -------------------------------------------------------------- oversized hint


def test_oversized_hint_still_detected():
    src = "# Indice : pensez a la recursion pour resoudre ce probleme specifique\n"
    assert "oversized_hint" in _rules(dmr.scan_cell(_cell(src)))
