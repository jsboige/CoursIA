"""Executable inventory of the markdown-table false-positive families that
mutilated a grain's documents (#15719, #15975).

Provenance -- this file is a MEASUREMENT, not an illustration.
--------------------------------------------------------------
On 2026-09-13 a Mistral Vibe grain (``g1-genai``) was handed 19 scanner
findings and cleared them by escaping pipes in the documents. It rewrote code,
prose and ASCII diagrams; ``git show fe04e1f37`` (worktree ``g1-genai``)
restores 8 files. Running the scanner over that RESTORED, known-correct content
reports **13 findings** -- every one of them a false positive by construction.

Those 13 findings fall into four families. Three are still open; each case
below carries the family's minimal reproduction, and is marked ``xfail`` so the
suite fails loudly the day it is repaired (``strict=True``: an unexpected pass
is a FAILURE, which is the point -- a marker that flips silently is a debt).

Family A (a ``$...$`` math span bridged across a cell delimiter, e.g. the
``($/1M tokens)`` header) was repaired by #15975 and is covered by that PR's
``test_currency_unit_bridged_span_keeps_delimiter``; it is deliberately NOT
duplicated here.

Why the reproductions look the way they do: two of the three families are NOT
locally reproducible. Measured on 2026-09-13, the JS family needs ~793 lines of
preceding fence context (it is a whole-file property of an unpaired fence
delimiter, not a shape in a cell), so it cannot be expressed as a fragment at
all -- it is recorded as ``skip`` with the open arbitrage named. Only the prose
and ASCII families reduce to a fragment, and those are the two ``xfail`` cases.

See #15719, #15975, #15974.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_table_syntax import detect_md_table_syntax  # noqa: E402


def _pathologies(lines, **kw):
    return [
        item["pathology"]
        for item in detect_md_table_syntax(lines, **kw)
    ]


# ---------------------------------------------------------------------------
# Family B -- `||` (logical OR) inside a fenced code block
# ---------------------------------------------------------------------------

@pytest.mark.skip(
    reason=(
        "Not expressible as a fragment: measured 2026-09-13, the false positive "
        "needs ~793 lines of preceding fence context. bonnes-pratiques.md carries "
        "121 fence delimiters (odd -- verified with an independent CommonMark "
        "length-aware scan), so the linear toggler in _build_fence_state / "
        "_find_table_blocks pairs them one shift out and classifies every "
        "following line backwards: JS at L792/793 and L838-840, genuinely inside "
        "a fence, is read as markdown and grouped into a 'table' -> NO_SEP + "
        "NO_BLANK_BEFORE/AFTER. Writing a test requires first deciding what an "
        "unpaired delimiter MEANS (document defect or scanner defect); the "
        "expected value IS that decision, so it cannot precede it. Evidence: "
        "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Roo-Code/05-projets-avances/"
        "integration-outils/bonnes-pratiques.md, restored in fe04e1f37."
    )
)
def test_js_logical_or_in_code_block_is_not_a_table():
    # Shape the grain met and escaped -- `||` became `\|`, which breaks the JS:
    #   if (!issueData.title || issueData.title.length < 3) {
    #   this.counts[counter] = (this.counts[counter] || 0) + 1;
    lines = [
        "```javascript",
        "function validate(issueData) {",
        "  if (!issueData.title || issueData.title.length < 3) {",
        "    throw new Error('titre trop court');",
        "  }",
        "}",
        "```",
    ]
    assert _pathologies(lines) == []


# ---------------------------------------------------------------------------
# Family C -- a bare `|` in PROSE that follows a table
# ---------------------------------------------------------------------------

@pytest.mark.xfail(
    strict=True,
    reason=(
        "ORPHAN_TABLE_ROW on prose. Measured 2026-09-13 on "
        "MyIA.AI.Notebooks/GenAI/FineTuning/FT-04-RLHF-DPO.ipynb cell[12]: the "
        "line 'l'optimum **pi*(y|x) = (1/Z) pi_ref(y|x) exp(r(x,y)/beta)**' is "
        "read as a continuation row of the table 5 lines above, because "
        "_has_delimiter_pipe treats the math bars in pi*(y|x) as cell "
        "delimiters. Retired by #15719 (its exact scope: ORPHAN_TABLE_ROW)."
    ),
)
def test_prose_pipe_after_table_is_not_an_orphan_row():
    lines = [
        "| Aspect | PPO | DPO |",
        "|--------|-----|-----|",
        "| Reward Model | Necessaire | Pas necessaire |",
        "",
        "**Derivation** : partant de l'objectif PPO standard",
        "`max_pi E[r(x,y)] - beta*KL(pi || pi_ref)`, les auteurs montrent que",
        "l'optimum **pi*(y|x) = (1/Z) pi_ref(y|x) exp(r(x,y)/beta)** peut etre",
        "**inverse** pour exprimer le reward en fonction de pi et pi_ref.",
    ]
    assert _pathologies(lines) == []


# ---------------------------------------------------------------------------
# Family D -- an ASCII axis plot read as a table
# ---------------------------------------------------------------------------

@pytest.mark.xfail(
    strict=True,
    reason=(
        "NO_SEP on an ASCII diagram. Measured 2026-09-13 on "
        "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Roo-Code/03-assistant-pro/"
        "presentations/structure-presentation.md L41/L145: the grid lines "
        "'80|', '60|', '40|' are pipe-lines, so a run of >=3 of them with no "
        "separator row is reported as a malformed table. The file has NO fence "
        "at all (6 balanced delimiters), so this family is fully local -- the "
        "grain escaped every axis bar to '\\|' and destroyed the plot. Retired "
        "by #15719 (sweep of scan_md_table_syntax findings)."
    ),
)
def test_ascii_axis_plot_is_not_a_table():
    lines = [
        "Le graphe de charge :",
        "",
        "    80|                             o Concurrent A",
        "    |                         o",
        "    60|                 o               # Concurrent B",
        "    |             o               #",
        "    40|     o       #",
        "    |   o   #                       * Notre entreprise",
        "    20| #   *   *",
        "    |*",
    ]
    assert _pathologies(lines) == []


# ---------------------------------------------------------------------------
# Non-regression controls -- a real defect must STILL be reported.
# A fix that silences these has bought the case file's green at the price of
# the detector, which is the failure mode this whole exercise exists to stop.
# ---------------------------------------------------------------------------

def test_genuine_orphan_row_is_still_flagged():
    lines = [
        "| Aspect | PPO | DPO |",
        "|--------|-----|-----|",
        "| Stabilite | Difficile | Plus stable |",
        "",
        "Fin du paragraphe.",
        "",
        "| cette | ligne | est | orpheline |",
    ]
    assert "ORPHAN_TABLE_ROW" in _pathologies(lines)


def test_genuine_col_mismatch_is_still_flagged():
    lines = [
        "| Modele | Cout |",
        "|---|---|",
        "| a | b | c |",
    ]
    assert "COL_MISMATCH" in _pathologies(lines)
