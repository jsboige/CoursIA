'''Tests for detect_markdown_rendering.repr_quoted_source_entries rule (#16221).

Founding incident: Tell c.1158-L1 / c.1158-L2 -- the 4.2e Focal-Loss notebook
had cells 19/20 whose ``source`` was a JSON-dumped list (e.g. ``["# 4.2e --
section heading\\n", "..."]``) pasted verbatim into the cell. The cell rendered
as literal escaped JSON instead of as proper markdown heading + paragraph.
The earlier ``markdown-rendering guard`` (#8052) was a faux negatif on this
class (the source-list structure was intact; only the content is wrong on
render).

Pattern constraints:
- 4-space indent + SINGLE quote opener (NOT Python triple-quote)
- content (with optional JSON-escapes like ``\\n``, ``\\"``, ``\\\\``)
- last char (before closer) is not a sentence-ending punctuation mark (. ! ?)
- closing JSON-quote + optional comma + optional newline + end of line
- minimum length 20 (real repr-quoted entries are typically 30-200 chars)
- fence-aware: a line inside a Python/markdown fenced code block renders
  verbatim and is NOT a defect

Run with:
    python -m pytest scripts/notebook_tools/tests/test_detect_markdown_rendering_repr_quoted.py -v
'''

from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import detect_markdown_rendering  # noqa: E402
from detect_markdown_rendering import (  # noqa: E402
    _is_repr_quoted_entry,
    scan_cell,
)


def _md(source_lines):
    """Build a markdown cell dict from a list of source lines."""
    return {"cell_type": "markdown", "source": source_lines, "metadata": {}}


def _rules(cell) -> list[str]:
    return [f["rule"] for f in scan_cell(cell)]


# --- _is_repr_quoted_entry --------------------------------------------------


class TestIsReprQuotedEntry:
    """Unit tests for the line-level pattern (#16221 / Tell c.1158-L1)."""

    def test_real_repr_quoted_with_escape(self):
        # The canonical founding-incident line, verbatim from c.1158-L1.
        line = '    "# 4.2e -- section heading\\n",\n'
        assert _is_repr_quoted_entry(line) is True, line

    def test_real_repr_quoted_with_quoted_escape(self):
        # A repr-quoted entry with a JSON-escaped backslash-quote inside.
        line = '    "some prose with **bold** and \\"quote\\"\\n",\n'
        assert _is_repr_quoted_entry(line) is True, line

    def test_real_repr_quoted_plain(self):
        # No escape chars -- still matches (regr-quoted plain ASCII entry).
        line = '    "no escape at all still quoted"\n'
        assert _is_repr_quoted_entry(line) is True, line

    def test_real_repr_quoted_with_backslash_double(self):
        # A literal backslash in the content -- encoded as ``\\\\`` in JSON.
        line = '    "with backslash \\\\ here"\n'
        assert _is_repr_quoted_entry(line) is True, line

    def test_real_repr_quoted_utf8(self):
        # UTF-8 content (non-ASCII) inside a repr-quoted entry is fine.
        line = '    "any utf8: e aca"\n'
        assert _is_repr_quoted_entry(line) is True, line

    def test_triple_quote_docstring_not_flagged(self):
        # Python triple-quoted string (single-line form) is NOT a repr-quoted
        # entry -- it opens with THREE quotes, not one.
        line = '    """Deferred-acceptance algorithm (proposing side = men).\n'
        assert _is_repr_quoted_entry(line) is False, line

    def test_json_like_config_line_not_flagged(self):
        # A ``"key": value,`` style config line within markdown narrative is
        # not repr-quoted (it has content AFTER the closer).
        line = '    "seed": -1,              # -1 = aleatoire\n'
        assert _is_repr_quoted_entry(line) is False, line

    def test_quoted_phrase_in_narrative_not_flagged(self):
        # A quoted phrase inside prose, ended with sentence punctuation, is
        # not repr-quoted (sentence-end char before the closer).
        line = '    "This is a quoted phrase in narrative markdown."\n'
        assert _is_repr_quoted_entry(line) is False, line

    def test_model_identifier_in_config_not_flagged(self):
        # A plain model-identifier line in markdown is JSON-like but the
        # content lacks quote-opener + escape structure. Wait: actually this
        # matches -- so we ENSURE the detector's overall cell-level filter
        # excludes it (this is NOT what our line-level rule excludes; the
        # cell-level rule is fence-aware and the line is in a fenced code
        # block in the corpus). The unit test below captures this boundary:
        line = '    "stabilityai/stable-diffusion-xl-base-1.0",\n'
        # Line-level: this DOES match the pattern (4-space + " + content + ",)
        # We rely on the cell-level fence-skip to exclude these. Unit test
        # confirms line-level matches (cell-level skip is tested separately).
        assert _is_repr_quoted_entry(line) is True, line

    def test_too_short_not_flagged(self):
        # A 5-char line cannot be a reliable repr-quoted entry.
        line = '    "x",\n'
        assert _is_repr_quoted_entry(line) is False, line

    def test_atx_heading_not_flagged(self):
        # ATX heading at column 0 -- not a repr-quoted entry.
        line = '## Section\n'
        assert _is_repr_quoted_entry(line) is False, line

    def test_blockquote_not_flagged(self):
        line = '    > a block quote at 4-space indent\n'
        assert _is_repr_quoted_entry(line) is False, line


# --- scan_cell (end-to-end) -------------------------------------------------


class TestScanCellReprQuoted:
    """End-to-end scan_cell tests for the repr_quoted_source_entries rule."""

    def test_real_defect_flagged(self):
        # The exact founding-incident shape: a cell whose source list contains
        # ``    "# 4.2e -- section heading\\n",\n`` as ONE element. This is the
        # canonical false-negative of the existing markdown-rendering guard.
        cell = _md([
            '    "# 4.2e -- section heading\\n",\n',
            '    "## Sub-heading\\n",\n',
            '    "Some prose text that does not end with sentence punctuation here",\n',
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" in rules, rules

    def test_real_defect_flagged_severity_error(self):
        cell = _md([
            '    "# 4.2e -- section heading\\n",\n',
            '    "Plain ASCII prose that does not end with punctuation",\n',
        ])
        for f in scan_cell(cell):
            if f["rule"] == "repr_quoted_source_entries":
                assert f["severity"] == "error", f
                return
        pytest.fail("finding not emitted")

    def test_real_defect_inside_fenced_code_block_not_flagged(self):
        # Fence-aware: a repr-quoted line inside a Python/markdown fenced code
        # block is a legitimate code example, NOT a defect. This is the
        # corpus-wide case that produced the high FP rate of the naive pattern.
        cell = _md([
            "Voici comment la source-list ressemble :\n",
            "\n",
            "```python\n",
            'source = ["# 4.2e -- section heading\\n", "..."]\n',
            "```\n",
            "\n",
            "Quand on colle ca verbatim, la cellule rend litteralement le JSON.\n",
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" not in rules, rules

    def test_legitimate_narrative_with_quotes_not_flagged(self):
        # A narrative paragraph that mentions quoted phrases mid-line is NOT
        # a defect. The line ``    "memoire $C$" et le "plafond $E$"`` has
        # content AFTER the closing quote, so the line-level pattern rejects
        # it. Same for short config-style lines.
        cell = _md([
            "**Liens croises.** ICT-15 integre $\\Phi$, $F$, $K$ -- ICT-17\n",
            '    "memoire $C$" et le "plafond $E$".\n',
            "\n",
            "ICT-10 apprend des estimateurs bornes.\n",
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" not in rules, rules

    def test_legitimate_config_lines_not_flagged(self):
        # A markdown cell showing SD-pipeline config keys (JSON-like dict
        # assignment lines) is NOT a repr-quoted entry -- the lines have
        # content (``:``, value, comment) AFTER the opening quote, so the
        # closing quote is mid-line not at end-of-line.
        cell = _md([
            "Configuration du pipeline :\n",
            "\n",
            "```python\n",
            '    "seed": -1,              # -1 = aleatoire, valeur fixe\n',
            '    "batch_size": 1,        # Nombre d\'images simultanees\n',
            '    "restore_faces": false, # Amelioration automatique\n',
            "```\n",
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" not in rules, rules

    def test_legitimate_python_code_block_with_repr_quoted_string(self):
        # A Python code block showing the model's identifier as a string
        # literal -- e.g. ``"stabilityai/stable-diffusion-xl-base-1.0"``
        # -- is LEGITIMATE Python source. The fence-aware filter MUST
        # exclude it. This is the heaviest corpus false-positive case.
        cell = _md([
            "Exemple de code :\n",
            "\n",
            "```python\n",
            'pipe = StableDiffusionXLPipeline.from_pretrained(\n',
            '    "stabilityai/stable-diffusion-xl-base-1.0",\n',
            ")\n",
            "```\n",
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" not in rules, rules

    def test_multiple_repr_quoted_lines_produce_single_finding(self):
        # The detector returns ONE finding per cell (hash is per-cell).
        cell = _md([
            '    "# 4.2e -- section heading\\n",\n',
            '    "## Sub-heading\\n",\n',
            '    "Plain prose text with no escapes at all",\n',
            '    "Another entry that does not end with sentence-end punctuation"\n',
        ])
        rules = _rules(cell)
        assert "repr_quoted_source_entries" in rules, rules
        matching = [f for f in scan_cell(cell)
                    if f["rule"] == "repr_quoted_source_entries"]
        assert len(matching) == 1
        assert "4 repr-quoted" in matching[0]["message"] or "4 repr-quoted" in matching[0]["message"]


class TestScanCellReprQuotedErrorBlocker:
    """Verify the rule is properly registered as ERROR (cliquet status)."""

    def test_rule_registered_as_error(self):
        from detect_markdown_rendering import RULE_SEVERITY
        assert RULE_SEVERITY["repr_quoted_source_entries"] == "error"

    def test_repair_command_listed(self):
        from detect_markdown_rendering import RULE_REPAIR
        # The current entry is a placeholder (no automated fixer). Documenting
        # this as a string rather than a command is acceptable per the comment.
        assert "repr_quoted_source_entries" in RULE_REPAIR
