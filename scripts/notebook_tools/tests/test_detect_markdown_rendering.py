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
    _is_frontmatter_block,
    scan_cell,
)


def _md(source_lines):
    """Build a markdown cell dict from a list of source lines."""
    return {"cell_type": "markdown", "source": source_lines, "metadata": {}}


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


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
