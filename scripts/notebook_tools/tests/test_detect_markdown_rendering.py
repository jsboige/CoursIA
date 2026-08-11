"""Tests for detect_markdown_rendering — frontmatter/setext rendering guard.

This scanner (#8352, HARD-enforced CI gate) catches markdown cells that render
badly: YAML frontmatter dumped into a rendered cell (markdown-it promotes the
``---`` fence to one oversized setext-H2 block) and accidental setext oversize.

These tests pin the precision fix for the prose-section-divider false positive
(c.882, routed by po-2025 c.870): a markdown cell that sandwiches prose between
two ``---`` thematic-break lines (``---\\n\\n### Heading\\n...\\n---``) must NOT
be flagged as frontmatter. The discriminator is the line immediately after the
opening ``---``: real YAML frontmatter starts its content on the very next line
(no blank), whereas a section divider follows the ``---`` hr with a blank line
+ heading.

Covers:
- ``_is_frontmatter_block``: real frontmatter (no blank after ``---``) vs
  section divider (blank after ``---``) vs non-fence cells.
- ``scan_cell``: end-to-end — real frontmatter flagged, prose section divider
  NOT flagged (the founding FP), plain prose/heading cells clean.

All fixtures are synthetic markdown strings — no notebook files, no network.
Runs in well under a second.
"""

from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from detect_markdown_rendering import (  # noqa: E402
    _inside_fence_lines,
    _is_frontmatter_block,
    scan_cell,
)


def _md(source_lines):
    """Build a markdown cell dict from a list of source lines."""
    return {"cell_type": "markdown", "source": source_lines, "metadata": {}}


def _cell(source: str) -> dict:
    """A markdown cell whose source is a single string (the nbformat list form
    is exercised implicitly via ``_as_text``; the detector handles both).
    Ported from the deleted legacy scripts/tests/test_detect_markdown_rendering.py
    shadow (#10066 consolidation)."""
    return {"cell_type": "markdown", "source": source}


def _rules(findings: list[dict]) -> set[str]:
    """Extract the rule names from a list of findings (ported from legacy)."""
    return {f["rule"] for f in findings}


# --- _is_frontmatter_block --------------------------------------------------


class TestIsFrontmatterBlock:
    def test_real_frontmatter_no_blank_after_fence(self):
        # Canonical YAML frontmatter: content starts immediately after `---`.
        lines = [
            "---\n",
            "title: Real Notebook\n",
            "cost:\n",
            "  api_usd_est: 0.0\n",
            "  cpu_min: 3\n",
            "---\n",
        ]
        assert _is_frontmatter_block(lines) is True

    def test_section_divider_blank_after_fence_is_not_frontmatter(self):
        # The founding FP (po-2025 c.870, QC-Py-22 cell#60): a thematic-break
        # section divider `---\n\n### Interprétation\n...prose...\n---`.
        lines = [
            "---\n",
            "\n",
            "### Interprétation\n",
            "Le modèle affiche une précision de 0.82 sur le jeu de test.\n",
            "Voici le détail des résultats ci-dessous.\n",
            "---\n",
        ]
        assert _is_frontmatter_block(lines) is False

    def test_section_divider_with_colon_prose_not_frontmatter(self):
        # Two colon-bearing phrases between two hr lines must not look like YAML.
        lines = [
            "---\n",
            "\n",
            "## Résultats\n",
            "précision : 0.82\n",
            "rappel : 0.79\n",
            "---\n",
        ]
        assert _is_frontmatter_block(lines) is False

    def test_no_leading_fence(self):
        assert _is_frontmatter_block(["# Title\n", "some prose\n"]) is False

    def test_single_fence_no_closer(self):
        # Only one `---` (opening, no closer) -> not a frontmatter block.
        lines = ["---\n", "title: X\n", "cost:\n", "  cpu_min: 3\n"]
        assert _is_frontmatter_block(lines) is False

    def test_empty_cell(self):
        assert _is_frontmatter_block([]) is False
        assert _is_frontmatter_block(["\n", "\n"]) is False

    def test_leading_blank_lines_before_fence(self):
        # Leading blanks then a fence: real frontmatter still detected if the
        # line right after the fence carries content.
        lines = ["\n", "\n", "---\n", "title: X\n", "cost:\n", "  cpu_min: 3\n", "---\n"]
        assert _is_frontmatter_block(lines) is True

    def test_leading_blank_then_section_divider(self):
        # Leading blanks then `---\n\n###` section divider -> not frontmatter.
        lines = ["\n", "---\n", "\n", "### Heading\n", "prose\n", "---\n"]
        assert _is_frontmatter_block(lines) is False


# --- scan_cell (end-to-end) -------------------------------------------------


class TestScanCell:
    def _rules(self, cell):
        return [f["rule"] for f in scan_cell(cell)]

    def test_real_frontmatter_flagged(self):
        cell = _md([
            "---\n", "title: Real\n", "cost:\n", "  api_usd_est: 0.0\n",
            "  cpu_min: 3\n", "  gpu_min: 0\n", "---\n",
        ])
        rules = self._rules(cell)
        assert any(r.startswith("frontmatter") for r in rules), rules

    def test_section_divider_not_flagged_as_frontmatter(self):
        # The exact founding-FP signature (QC-Py-22 cell#60): a thematic-break
        # section divider must NOT be classified as frontmatter. (A closing
        # `---` directly under text may legitimately trip the separate
        # `setext_oversized` rule — that is a different detection, not the FP
        # being fixed here, so we assert no *frontmatter* rule fires.)
        cell = _md([
            "---\n", "\n", "### Interprétation\n",
            "Le modèle affiche : précision 0.82, rappel 0.79.\n",
            "Détail des métriques ci-dessous.\n", "---\n",
        ])
        rules = self._rules(cell)
        assert not any(r.startswith("frontmatter") for r in rules), rules

    def test_plain_heading_prose_clean(self):
        cell = _md(["# Title\n", "\n", "Some paragraph with a colon: value.\n"])
        assert not any(r.startswith("frontmatter") for r in self._rules(cell))

    def test_non_markdown_cell_clean(self):
        assert scan_cell({"cell_type": "code", "source": ["print(1)\n"]}) == []

    def test_empty_markdown_clean(self):
        assert scan_cell(_md([])) == []
        assert scan_cell(_md(["\n"])) == []


# --- oversized_hint fence-awareness ----------------------------------------


class TestOversizedHintFenceAware:
    """A hint keyword (`# Indice`/`# Hint`/`# Astuce`) that appears INSIDE a
    fenced code block is a code comment (e.g. an exercise-scaffold line like
    ``# Indice : reutilisez sf.branching_avalanche_sizes(...)``), NOT a rendered
    markdown heading. The detector must skip fenced lines (parity with the
    already-fence-aware ``setext_oversized`` rule). Founding FP: ICT-7
    ScaleFreeSignatures exercise scaffolds (~14 false oversized_hint hits)."""

    def _rules(self, cell):
        return [f["rule"] for f in scan_cell(cell)]

    def test_hint_comment_inside_backtick_fence_not_flagged(self):
        # Canonical exercise scaffold: `# Indice :` as a Python comment inside a
        # fenced code block -- renders as literal code, not an H1.
        cell = _md([
            "### Exercice 1\n",
            "\n",
            "Calculez la valeur.\n",
            "\n",
            "```\n",
            "# Indice : reutilisez sf.branching_avalanche_sizes(mu, N, rng).\n",
            "# Etape 1 : construire la liste des mu.\n",
            "```\n",
        ])
        assert "oversized_hint" not in self._rules(cell)

    def test_hint_comment_inside_tilde_fence_not_flagged(self):
        # Tilde fences (~~~) are equivalent CommonMark fenced-code markers and
        # must be treated identically.
        cell = _md([
            "### Exercice\n",
            "\n",
            "~~~\n",
            "# Hint : use a heap for O(n log n).\n",
            "~~~\n",
        ])
        assert "oversized_hint" not in self._rules(cell)

    def test_real_hint_heading_outside_fence_still_flagged(self):
        # Regression guard: a genuine `# Indice :` H1 in rendered markdown (no
        # fence) IS a defect and must still be reported.
        cell = _md([
            "## Exercice\n",
            "\n",
            "Calculez.\n",
            "\n",
            "# Indice : pensez a la symetrie du probleme pour simplifier.\n",
        ])
        assert "oversized_hint" in self._rules(cell)

    def test_subsection_hint_outside_fence_still_flagged(self):
        # A `### Astuces` subsection heading outside a fence is still detected
        # (this is the detector's current behaviour for rendered hint headings;
        # the fix only adds fence-skipping, it does not change that policy).
        cell = _md(["### Astuces\n", "\n", "- Utilisez X.\n"])
        assert "oversized_hint" in self._rules(cell)


# =========================================================================== #
# FENCE-AWARENESS + SETEXT/FRONTMATTER RULE COVERAGE
#
# Ported verbatim from the deleted legacy scripts/tests/test_detect_markdown_rendering.py
# shadow (#10066 consolidation). The canon above tests ``_is_frontmatter_block``,
# ``scan_cell`` end-to-end, and ``oversized_hint`` fence-awareness. The legacy
# file uniquely covered three areas the canon entirely lacked:
#
#   1. ``_inside_fence_lines`` — the code-fence detection helper (8 unit tests)
#   2. ``setext_oversized`` — the rule flagging prose underlined by ``---``/``===``
#      outside a fence, with regression guards for the ASCII-art / cryptarithme
#      false-positive family (5 tests)
#   3. ``frontmatter_supersize`` / ``frontmatter_rawyaml`` — the two distinct
#      frontmatter rule names, pinned so a regression cannot merge them (2 tests)
#
# The module collision (both files shared basename ``test_detect_markdown_rendering``)
# meant the canon's 17 tests were DEAD in CI whenever both ran (verified: both-
# together 36 = 18x2, not 17+18=35). Deleting the legacy after porting these 15
# unique tests resurrects the canon's 17 AND unifies fence/rule coverage.
# =========================================================================== #


class TestInsideFenceLines:
    """Unit tests for the ``_inside_fence_lines`` helper (impl L148)."""

    def test_basic_backtick(self):
        lines = ["```", "a", "---", "b", "```", "c"]
        assert _inside_fence_lines(lines) == {1, 2, 3}

    def test_marker_lines_not_inside(self):
        """The opening and closing marker lines themselves are NOT inside."""
        lines = ["```", "a", "```"]
        assert _inside_fence_lines(lines) == {1}

    def test_tilde_fence(self):
        lines = ["~~~", "x", "y", "~~~"]
        assert _inside_fence_lines(lines) == {1, 2}

    def test_unclosed_fence(self):
        """An unclosed fence leaves every subsequent line inside (defensive)."""
        lines = ["```", "a", "---", "b"]
        assert _inside_fence_lines(lines) == {1, 2, 3}

    def test_mixed_chars_do_not_close(self):
        """A tilde line inside a backtick block is literal text, not a closer."""
        lines = ["```", "~~~", "a", "```"]
        assert _inside_fence_lines(lines) == {1, 2}

    def test_indented_fence(self):
        lines = ["   ```python", "a", "---", "   ```"]
        assert _inside_fence_lines(lines) == {1, 2}

    def test_two_separate_blocks(self):
        lines = ["```", "a", "```", "b", "```", "c", "```"]
        assert _inside_fence_lines(lines) == {1, 5}

    def test_no_fence_returns_empty(self):
        assert _inside_fence_lines(["a", "---", "b"]) == set()


class TestSetextOversizedFenceAwareness:
    """The focal regression of the legacy suite: a ``---``/``===`` line INSIDE a
    fenced-code block is literal text (ASCII art, a cryptarithme divider) and
    must NOT be flagged as a setext underline (impl ``setext_oversized`` rule)."""

    def test_inside_code_fence_not_flagged(self):
        """The canonical false positive: an ASCII-art divider inside a ``` block."""
        src = (
            "```\n"
            "  S E N D\n"
            "+ M O R E\n"
            "---------\n"  # >=3 dashes -> _SETEXT_RE, but inside the fence
            "M O N E Y\n"
            "```\n"
        )
        assert "setext_oversized" not in _rules(scan_cell(_cell(src)))

    def test_outside_code_fence_still_flagged(self):
        """Regression guard: real prose underlined by --- (outside any fence)
        IS flagged."""
        src = (
            "Ceci est un long paragraphe de prose pedagogique qui se termine "
            "sans point final avant la regle.\n"
            "---\n"
        )
        assert "setext_oversized" in _rules(scan_cell(_cell(src)))

    def test_after_closed_fence_flagged(self):
        """--- outside a CLOSED fence underlining real prose is still flagged."""
        src = (
            "```\n"
            "code block\n"
            "```\n"
            "\n"
            "Un paragraphe de prose explicatif assez long pour depasser le seuil.\n"
            "---\n"
        )
        assert "setext_oversized" in _rules(scan_cell(_cell(src)))

    def test_cryptarithmetic_ascii_art_not_flagged(self):
        """The exact defect family that shipped as FP on the CSP/Sudoku
        notebooks: a multi-line ASCII diagram inside a code fence containing a
        ``---`` divider."""
        src = (
            "Voici le cryptarithme SEND + MORE = MONEY :\n\n"
            "```\n"
            "    S E N D\n"
            "  + M O R E\n"
            "  ---------\n"
            "  M O N E Y\n"
            "```\n"
        )
        assert "setext_oversized" not in _rules(scan_cell(_cell(src)))

    def test_equals_rule_inside_fence_not_flagged(self):
        """The ``===`` setext variant, inside a fence, is also literal."""
        src = "texte\n```\npara ligne\n=====\n```\n"
        assert "setext_oversized" not in _rules(scan_cell(_cell(src)))


class TestFrontmatterRules:
    """Pin the two distinct frontmatter rule names
    (``frontmatter_supersize`` / ``frontmatter_rawyaml``) so a regression cannot
    merge them. Ported from the deleted legacy shadow."""

    def test_supersize_still_detected(self):
        """Regression guard: a real frontmatter-supersize block IS still flagged
        (the closing ``---`` sits directly after a text line -> setext H2
        supersize)."""
        src = (
            "---\n"
            "title: \"Un notebook\"\n"
            "cost:\n"
            "  api_usd_est: 0.01\n"
            "  cpu_min: 5\n"
            "---\n"  # directly after a text line -> setext H2 supersize
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "frontmatter_supersize" in rules

    def test_rawyaml_still_detected(self):
        """Regression guard: raw frontmatter (blank line before closing ``---``)
        IS flagged as ``frontmatter_rawyaml``."""
        src = (
            "---\n"
            "title: \"Un notebook\"\n"
            "cost:\n"
            "  cpu_min: 5\n"
            "\n"
            "---\n"
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "frontmatter_rawyaml" in rules


# --- source_list_missing_newlines (#10397) ---------------------------------


class TestSourceListMissingNewlines:
    """A markdown cell whose ``source`` is a list of N>=2 elements carrying
    fewer ``\\n`` than the element count implies collapses to one giant line on
    join (``_as_text`` concatenates verbatim) -> every downstream line-based
    rule sees a single line and reports nothing. The structural loss must be
    caught BEFORE normalization. Founding defect: #10305
    ``02-7-CogVideoX-Text-to-Video.ipynb`` cell 21 (23 elements, 0 ``\\n``,
    1509 chars) passed the guard with 0 violations."""

    def _rules(self, cell):
        return [f["rule"] for f in scan_cell(cell)]

    def test_long_list_without_newlines_flagged(self):
        # The canonical malformed case: multi-element list, zero newlines, long.
        cell = _md(["## Titre ", "paragraphe un ", "paragraphe deux ",
                    "paragraphe trois ", "paragraphe quatre fin du bloc"])
        rules = self._rules(cell)
        assert "source_list_missing_newlines" in rules

    def test_well_formed_list_with_newlines_clean(self):
        # Correct nbformat: each non-final element ends with '\n'. Joined text
        # has as many breaks as elements-1 -> NOT flagged.
        cell = _md(["## Titre\n", "paragraphe un\n", "paragraphe deux\n",
                    "paragraphe trois\n", "paragraphe quatre fin du bloc"])
        assert self._rules(cell) == []

    def test_short_list_without_newlines_clean(self):
        # < 40 chars: too short for the loss to matter (avoids noisy flags on
        # trivial cells like ['a', 'b']).
        cell = _md(["a ", "b ", "c"])
        assert self._rules(cell) == []

    def test_string_source_clean(self):
        # String source (not a list) is never subject to the list-collapse bug.
        assert self._rules(_cell("## Titre\ndu texte\nfin")) == []

    def test_single_element_list_clean(self):
        # A 1-element list cannot lose structure.
        assert self._rules(_md(["un seul element assez long pour depasser quarante caracteres"])) == []

    def test_non_markdown_cell_clean(self):
        # Code cells are skipped entirely.
        assert scan_cell({"cell_type": "code", "source": ["a", "b", "c"]}) == []


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
