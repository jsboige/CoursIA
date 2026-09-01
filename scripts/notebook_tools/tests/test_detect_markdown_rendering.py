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

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import detect_markdown_rendering  # noqa: E402
from detect_markdown_rendering import (  # noqa: E402
    _inside_fence_lines,
    _is_frontmatter_block,
    _is_yaml_block_open_no_close,
    _notebook_targets_from_render_list,
    _quarto_render_list,
    _selfcheck,
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


# --- regression guards: real corpus cells cited in #10397 ------------------
#
# Issue #10397 cites three real notebook cells that exhibited the defect at
# the time of the report (multi-element markdown source, 0 '\n' inside the
# joined text, length > 200 chars):
#
#   - MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-7-CogVideoX-Text-to-Video.ipynb c#21
#   - MyIA.AI.Notebooks/Search/Part1-Foundations/Search-5-GeneticAlgorithms.ipynb c#67
#   - MyIA.AI.Notebooks/Sudoku/Sudoku-16-NeuralNetwork-Python.ipynb c#28
#
# PR #10423 + #10446 fixed the detector (multi-element and single-element
# variants). The cells on `main` HEAD may have been re-edited since, but the
# detector MUST continue to flag the shape: if any of these cells (or future
# cells with the same shape) drift back, the gate must catch them.
#
# These tests pin the closure of #10397 — if a regression re-introduces the
# shape on `main`, the test fails (`regression_caught_rule_*`), and if a
# cleanup PR manages to convert the cells to clean nbformat (sufficient
# breaks between elements), the test exits cleanly (`regression_clear_rule_*`)
# and a fresh PR can re-baseline the closure.


_REPO_ROOT = Path(__file__).resolve().parents[3]


def _real_cell(path: str, cell_idx: int):
    """Load a single cell from a real notebook; raises if missing."""
    nb_path = _REPO_ROOT / path
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    return nb["cells"][cell_idx]


class TestRealCorpusRegressionGuards:
    """Pin the closure of #10397 against the three real cells cited in the
    issue body. Each test loads the cell on current `main` and either asserts
    clean nbformat (cell was edited into shape after the fix) OR asserts the
    detector catches the shape (defensive guard against any future re-intro).
    """

    def _rules_for_real_cell(self, path: str, cell_idx: int):
        cell = _real_cell(path, cell_idx)
        return {f["rule"] for f in scan_cell(cell)}

    def test_regression_clear_cogvideox_c21(self):
        # 02-7-CogVideoX c#21 is currently a code cell (not markdown) on main,
        # so the bug shape cannot re-emerge in that cell.
        cell = _real_cell(
            "MyIA.AI.Notebooks/GenAI/Video/02-Advanced/"
            "02-7-CogVideoX-Text-to-Video.ipynb",
            21,
        )
        assert cell["cell_type"] == "code", (
            "CogVideoX c#21 must remain a code cell; if it is markdown, "
            "verify the source list still carries element-terminating '\\n'."
        )

    def test_regression_clear_search5_c67(self):
        # Search-5-GeneticAlgorithms c#67 is markdown on main with 21 source
        # elements and 20 newlines (each non-final element terminates with
        # '\\n'). The detector must NOT flag it.
        rules = self._rules_for_real_cell(
            "MyIA.AI.Notebooks/Search/Part1-Foundations/"
            "Search-5-GeneticAlgorithms.ipynb",
            67,
        )
        assert "source_list_missing_newlines" not in rules, (
            f"Search-5 c#67 regressed into the #10397 shape: {rules}"
        )

    def test_regression_clear_sudoku16_c28(self):
        # Sudoku-16-NeuralNetwork-Python c#28 is markdown on main with 47
        # source elements and 46 newlines.
        rules = self._rules_for_real_cell(
            "MyIA.AI.Notebooks/Sudoku/Sudoku-16-NeuralNetwork-Python.ipynb",
            28,
        )
        assert "source_list_missing_newlines" not in rules, (
            f"Sudoku-16 c#28 regressed into the #10397 shape: {rules}"
        )


class TestYamlBlockOpenNoClose:
    """Pin the new ``yaml_block_open_no_close`` rule (#11630).

    Reproduces the 2026-08-17 main breakage on
    ``MyIA.AI.Notebooks/GenAI/FallacyDetection/02_fallacy_datasets_landscape.ipynb``
    (was ``MyIA.AI.Notebooks/FallacyDetection/`` before tranche 1 of #13581):
    8 of 20 cells started with ``---\\n### Dataset N -- ...`` (no closing
    ``---``), and Pandoc extended the YAML block through every following cell
    until the next ``---``, breaking the whole page. ``_is_frontmatter_block``
    only catches cells with a CLOSING ``---`` -- this rule covers the
    opener-without-closer shape that the previous detector missed entirely.
    """

    def test_positive_control_pre_11629_shape(self):
        """The exact cell shape from pre-#11629 fallacious_datasets_landscape.

        The cell source starts with ``---\\n### Dataset 1 -- ...`` and has
        NO closing ``---``. The detector MUST flag it as
        ``yaml_block_open_no_close`` (this is the angle the previous
        ``_is_frontmatter_block`` missed -- the previous detector required a
        closing ``---``).
        """
        src = (
            "---\n"
            "### Dataset 1 -- Logic / LogicClimate (Jin et al. 2021)\n\n"
            "**Papier** : Jin et al., *Logical Fallacy Detection*, Findings "
            "EMNLP 2021 -- [arXiv:2202.13758](https://arxiv.org/abs/2202.13758). "
            "Premier dataset de fallacies logiques formelles, 7 categories, "
            "environ 2500 exemples."
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "yaml_block_open_no_close" in rules, (
            f"the #11630 pre-fix shape was not flagged: {rules}"
        )

    def test_sl8_form_blank_line_after_opener_is_flagged(self):
        """``---\\n\\n### H`` at the head of a cell IS a YAML opener -- flagged.

        The pre-#11630 exemption claimed a blank line after the opening ``---``
        made it a "thematic break, not a YAML opener". ai-01's arbitration
        (2026-08-18) refuted it empirically: SL-8-KnowledgeGraphs-ILP.ipynb --
        the notebook that took the site down the SECOND time, at 20:27Z, AFTER
        #11629 -- is exactly ``---\\n\\n## Titre`` in all 15 markdown cells,
        and the oracle js-yaml renders ``scanned=1 bad=1`` (*bad indentation of
        a mapping entry*). Pandoc opens the yaml_metadata_block whether or not
        a blank line follows the opener. This pin is the second observed form.
        """
        src = (
            "---\n"
            "\n"
            "### Section heading\n\n"
            "Body of the section follows the YAML opener."
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "yaml_block_open_no_close" in rules, (
            f"the SL-8 form (--- + blank + heading) was not flagged: {rules}"
        )

    def test_bare_divider_alone_not_flagged(self):
        """A cell containing ONLY the ``---`` line is a thematic break.

        Pandoc needs a following non-blank line to start a YAML block; a bare
        ``---`` cell renders as ``<hr>`` and is safe. This is the one
        head-``---`` shape the corrected rule must keep silent on.
        """
        rules = _rules(scan_cell(_cell("---\n")))
        assert "yaml_block_open_no_close" not in rules, (
            f"bare --- divider false-positive: {rules}"
        )

    def test_horizontal_rule_alone_not_flagged(self):
        """A bare ``---`` between two blank lines (thematic break alone)
        must NOT be flagged. The discriminant: a thematic break is followed
        by a blank line OR nothing; a YAML opener is followed by content."""
        src = (
            "Paragraph above.\n"
            "\n"
            "---\n"
            "\n"
            "Paragraph below."
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "yaml_block_open_no_close" not in rules, (
            f"thematic-break false-positive: {rules}"
        )

    def test_complete_frontmatter_still_routed_to_existing_rule(self):
        """A cell with both opening AND closing ``---`` must still go through
        ``frontmatter_supersize`` / ``frontmatter_rawyaml`` -- this new rule
        early-returns so the existing classification wins. Pin: the new rule
        does NOT swallow complete-frontmatter cells (it would be a regression
        of the existing frontmatter_supersize / frontmatter_rawyaml signal).
        """
        src = (
            "---\n"
            "title: A notebook\n"
            "cost:\n"
            "  api_usd_est: 0.01\n"
            "\n"  # blank line before closing ``---`` -> rawyaml shape
            "---\n"
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "yaml_block_open_no_close" not in rules, (
            f"complete-frontmatter was swallowed by the new rule: {rules}"
        )
        assert "frontmatter_rawyaml" in rules, (
            f"complete-frontmatter was not classified: {rules}"
        )

    def test_fenced_dash_not_counted_as_closer(self):
        """A ``---`` inside a fenced code block (verbatim) is literal text,
        not a YAML closer. The cell STARTS with ``---`` only if the first
        line of the cell is ``---`` -- if the first line is a fenced-code
        opener like ``\\`\\`\\`python``, the cell is not a YAML opener
        regardless of what comes later. This test pins the FENCE awareness
        to avoid the false-positive where someone writes ``---`` as ASCII
        art at the start of a notebook before any code block."""
        src = (
            "---\n"  # first line: YAML opener shape
            "```python\n"
            "print('---')\n"  # literal --- inside fenced code, NOT a closer
            "```\n"
            "Body after the code block."
        )
        rules = _rules(scan_cell(_cell(src)))
        # This cell has the YAML-opener shape at the top and a fenced code
        # block containing a ``---`` line -- the fenced closer (```) does not
        # count as a YAML closer, so the YAML block is still open when the
        # cell ends. The detector SHOULD flag it (this is precisely the
        # pattern we want -- opening YAML without a YAML closer anywhere in
        # the cell, regardless of fence contents).
        assert "yaml_block_open_no_close" in rules, (
            f"YAML opener with fenced---only-closer should still flag: {rules}"
        )

    def test_selfcheck_fires_on_both_observed_forms(self):
        """The embedded control game carries BOTH #11630 forms (acceptance).

        The arbitration's core demand: a positive control calibrated on the
        FIRST form (``---`` + immediate content) let the SECOND form (``---`` +
        blank + title, SL-8) pass and took the site down twice. The selfcheck
        must therefore assert both forms fire and the negatives stay silent --
        exit 0 means the game is green. A future refactor that loses a form
        turns this red instead of rendering a cleaner violation count.
        """
        assert _selfcheck() == 0

    def test_yaml_opener_does_not_mask_other_rules(self):
        """#12338: the yaml finding must not stop the scan of the cell body.

        Pre-#12338 the yaml branch ended with ``return findings``, so no rule
        after it ever ran on a yaml cell. Measured on the 8 QC-Py notebooks of
        #12332: all 18 cells carrying ``- # Indice :`` heading_in_list lines
        were yaml cells, and the detector reported ``heading_in_list = 0`` on
        the whole family -- a zero of denominator, not of numerator. This cell
        reproduces the shape: YAML opener + an in-list heading further down.
        Both findings must appear.
        """
        src = (
            "---\n"
            "### Exercice 3 : Sortino Ratio par regime\n"
            "\n"
            "- # Indice : Groupby par label de regime : `df.groupby('regime')`\n"
        )
        rules = _rules(scan_cell(_cell(src)))
        assert "yaml_block_open_no_close" in rules, (
            f"yaml opener lost: {rules}"
        )
        assert "heading_in_list" in rules, (
            f"heading_in_list still masked by the yaml branch: {rules}"
        )


class TestQuartoClosure:
    """Pin the ``--closure`` mode of detect_markdown_rendering.

    The 2026-08-17 main breakage on
    ``MyIA.AI.Notebooks/GenAI/FallacyDetection/02_fallacy_datasets_landscape.ipynb``
    (formerly ``MyIA.AI.Notebooks/FallacyDetection/``, pre-#13581 tranche 1)
    was NOT detectable by a repo-wide scan + filter on the PR's touched
    paths: the PR that broke main (#11480) didn't touch the broken notebook
    -- it added a link from ``GenAI/FallacyDetection/README.md`` (rendered) to the
    notebook (previously unread by Quarto). The closure scan follows
    ``.ipynb`` links one hop out of the render-list, catching exactly the
    set of notebooks that Quarto will *transitively* render.
    """

    def test_render_list_yaml_parse(self, tmp_path):
        yml = tmp_path / "_quarto.yml"
        yml.write_text(
            "project:\n"
            "  type: site\n"
            "  render:\n"
            "    - 'index.qmd'\n"
            "    - 'MyIA.AI.Notebooks/Search/index.qmd'\n"
            "    - '*.qmd'\n"  # globs are skipped (caller decides what to do)
            "    - 'MyIA.AI.Notebooks/Foo.ipynb'\n"
            "    - 'docs/bar.md'\n",
            encoding="utf-8",
        )
        out = _quarto_render_list(yml)
        # Globs are filtered out; only concrete paths remain.
        names = [p.name for p in out]
        assert "index.qmd" in names
        assert "Foo.ipynb" in names
        assert "bar.md" in names
        # The ``*.qmd`` glob is excluded -- the scanner can't expand it.
        assert all("*" not in str(p) for p in out)

    def test_notebook_targets_from_render_list_follows_ipynb_links(self, tmp_path):
        """A rendered README linking to a notebook pulls that notebook into
        the closure, even if it is NOT in the render-list. This is exactly
        the 2026-08-17 failure mode: the broken notebook was added to the
        transitive closure by a link from a rendered README, not by a
        render-list addition.
        """
        # Filesystem scaffold:
        #   <tmp>/_quarto.yml
        #   <tmp>/docs/render.md     (in render-list)
        #   <tmp>/docs/other.ipynb   (link target, NOT in render-list)
        repo = tmp_path
        yml = repo / "_quarto.yml"
        yml.write_text(
            "project:\n  render:\n    - 'docs/render.md'\n",
            encoding="utf-8",
        )
        (repo / "docs").mkdir()
        (repo / "docs" / "render.md").write_text(
            "Some prose linking to [the notebook](other.ipynb).\n",
            encoding="utf-8",
        )
        (repo / "docs" / "other.ipynb").write_text(
            '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}',
            encoding="utf-8",
        )
        render_paths = _quarto_render_list(yml)
        targets = _notebook_targets_from_render_list(repo, render_paths)
        # The notebook linked from the rendered page is in the closure.
        assert Path("docs/other.ipynb") in targets, (
            f"link from render-list did not pull notebook into closure: {targets}"
        )

    def test_ipynb_link_with_html_href(self, tmp_path):
        """An ``href=\".../foo.ipynb\"`` link also pulls the target in."""
        repo = tmp_path
        yml = repo / "_quarto.yml"
        yml.write_text(
            "project:\n  render:\n    - 'docs/render.md'\n",
            encoding="utf-8",
        )
        (repo / "docs").mkdir()
        (repo / "docs" / "render.md").write_text(
            '<a href="linked.ipynb">link</a>\n',
            encoding="utf-8",
        )
        (repo / "docs" / "linked.ipynb").write_text(
            '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}',
            encoding="utf-8",
        )
        targets = _notebook_targets_from_render_list(repo, _quarto_render_list(yml))
        assert Path("docs/linked.ipynb") in targets

    def test_ipynb_link_followed_by_terminal_period(self, tmp_path):
        """A bare notebook link at the END of a sentence (followed by ``.``)
        must still resolve -- the period is sentence punctuation, not part of
        the filename. Without this, the closure silently misses notebooks that
        are only reachable via sentence-final bare links (Hermes FN reserve on
        #11643).

        Motif ``... voir foo.ipynb.`` -- the regex lookahead ``(?=[.,;:!?]|$)``
        lets the regex stop at ``.`` (which becomes the post-match rstrip's
        job to clean). The captured URL is ``foo.ipynb`` -> resolves to the
        file on disk.
        """
        repo = tmp_path
        yml = repo / "_quarto.yml"
        yml.write_text(
            "project:\n  render:\n    - 'docs/render.md'\n",
            encoding="utf-8",
        )
        (repo / "docs").mkdir()
        (repo / "docs" / "render.md").write_text(
            # Sentence-final bare link. The 'voir ' prefix puts a space before
            # the URL; the trailing '.' is sentence punctuation.
            "Pour la suite, voir other.ipynb.\n",
            encoding="utf-8",
        )
        (repo / "docs" / "other.ipynb").write_text(
            '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}',
            encoding="utf-8",
        )
        targets = _notebook_targets_from_render_list(repo, _quarto_render_list(yml))
        # The pin: sentence-final period MUST NOT cause the link to fall out
        # of the closure. Pre-#11643 fix this assertion fails -- the regex
        # stopped on the '.' and the post-match rstrip never fired.
        assert Path("docs/other.ipynb") in targets, (
            f"sentence-final bare link was dropped from the closure: {targets}"
        )

    def test_ipynb_link_followed_by_other_terminal_punctuation(self, tmp_path):
        """Same FN class, but for ``!``, ``?``, ``,``, ``;``, ``:`` -- any
        terminal punctuation that ends a sentence or clause. Each is a real
        shape in prose; each must NOT silently drop the link from closure.
        """
        repo = tmp_path
        yml = repo / "_quarto.yml"
        yml.write_text(
            "project:\n  render:\n    - 'docs/render.md'\n",
            encoding="utf-8",
        )
        (repo / "docs").mkdir()
        # One line per punctuation, comma is mid-clause (not really terminal
        # -- but covered for symmetry since the lookahead accepts it).
        (repo / "docs" / "render.md").write_text(
            "Voir other.ipynb! Aussi other2.ipynb? "
            "Enfin other3.ipynb, ou other4.ipynb; "
            "puis other5.ipynb: c'est tout.\n",
            encoding="utf-8",
        )
        for name in ("other", "other2", "other3", "other4", "other5"):
            (repo / "docs" / f"{name}.ipynb").write_text(
                '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}',
                encoding="utf-8",
            )
        targets = _notebook_targets_from_render_list(repo, _quarto_render_list(yml))
        for name in ("other", "other2", "other3", "other4", "other5"):
            assert Path(f"docs/{name}.ipynb") in targets, (
                f"link '...{name}.ipynb<TP>' was dropped from closure: {targets}"
            )


class TestQuartoClosureDependency:
    """Pin the #11850 fix: a missing pyyaml must never read as an empty render-list.

    Pre-fix, ``_quarto_render_list`` swallowed the ImportError from
    ``import yaml`` behind ``except Exception: return []``, and the CLI
    reported "empty/invalid _quarto.yml" -- on a runner without pyyaml the
    closure scan silently covered 0 of 792 render-list entries while accusing
    a perfectly valid YAML file (the ``handrolled-pattern-set-undercounts-
    silently`` defect class). These controls hold the two causes apart: a
    missing dependency is named as a dependency; only genuinely invalid YAML
    keeps the empty-list path.
    """

    def _write_yml(self, tmp_path: Path) -> Path:
        yml = tmp_path / "_quarto.yml"
        yml.write_text(
            "project:\n  render:\n    - 'docs/render.md'\n",
            encoding="utf-8",
        )
        return yml

    def test_missing_pyyaml_raises_naming_the_dependency(self, tmp_path, monkeypatch):
        # A None entry in sys.modules makes `import yaml` raise ImportError.
        yml = self._write_yml(tmp_path)
        monkeypatch.setitem(sys.modules, "yaml", None)
        with pytest.raises(RuntimeError, match="pyyaml"):
            _quarto_render_list(yml)

    def test_invalid_yaml_still_returns_empty(self, tmp_path):
        # Genuinely unparseable YAML keeps the OLD contract (empty list) --
        # the caller's "empty/invalid" message is the right one for it.
        yml = tmp_path / "_quarto.yml"
        yml.write_text("project: [unclosed\n", encoding="utf-8")
        assert _quarto_render_list(yml) == []

    def test_cli_missing_pyyaml_exits_2_blaming_the_dependency(self, tmp_path):
        # CLI level: run the real script in a subprocess where `import yaml`
        # raises (a fake yaml.py first on sys.path = pyyaml absent, without
        # uninstalling anything). The pin: exit 2 with a message that names
        # the DEPENDENCY, never "empty/invalid".
        yml = self._write_yml(tmp_path)
        (tmp_path / "yaml.py").write_text(
            'raise ImportError("simulated: pyyaml absent")\n', encoding="utf-8"
        )
        env = {**os.environ, "PYTHONPATH": str(tmp_path)}
        script = Path(detect_markdown_rendering.__file__).resolve()
        r = subprocess.run(
            [sys.executable, str(script), "--closure", "--quarto-yml", str(yml),
             str(tmp_path)],
            capture_output=True, text=True, env=env, cwd=tmp_path,
        )
        assert r.returncode == 2, (r.stdout, r.stderr)
        assert "pyyaml" in r.stderr
        assert "empty/invalid" not in r.stderr

    def test_cli_with_pyyaml_reads_the_render_list(self, tmp_path):
        # Positive control: with pyyaml present the CLI reads the render-list
        # and announces its size (the CI log line "--closure: render-list=N").
        yml = self._write_yml(tmp_path)
        script = Path(detect_markdown_rendering.__file__).resolve()
        r = subprocess.run(
            [sys.executable, str(script), "--closure", "--quarto-yml", str(yml),
             str(tmp_path)],
            capture_output=True, text=True, cwd=tmp_path,
        )
        assert r.returncode == 0, (r.stdout, r.stderr)
        assert "--closure: render-list=1" in r.stderr


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
