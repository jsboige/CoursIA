"""Tests for scripts/notebook_tools/scan_md_hierarchy.py.

Locks in the COLLAPSED-MARKDOWN detector added for #3966: a markdown cell
whose newlines were stripped (heading + prose + GFM table separator + fenced
code glued onto ONE line) must be flagged, while legitimate tables, blockquoted
tables, and fenced ASCII art (all with their newlines intact) must stay SILENT.
Also guards the pre-existing H1-DEEP / MULTI-H1 / HINT-AS-HEADING checks.
"""

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_hierarchy import scan_notebook, _has_collapsed_markdown  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source) -> dict:
    # Match the real notebook convention: source is a list of lines (str stayed
    # joined is also accepted by the scanner). Default to list-of-lines.
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "source": source}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": [source], "execution_count": 1, "outputs": []}


def _write_nb(cells: list[dict]) -> str:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
    json.dump(nb, f)
    f.close()
    return f.name


def _kinds(path: str) -> list[str]:
    return [f["kind"] for f in scan_notebook(path)]


# ---------------------------------------------------------------------------
# COLLAPSED-MARKDOWN — true positives (must flag)
# ---------------------------------------------------------------------------

def test_collapsed_heading_plus_table_on_one_line():
    """The canonical #3966 defect: heading + prose + table rows glued."""
    collapsed = (
        "### Analyse### Détail| Méthode | Rôle ||---------|------|"
        "| init() | construit |"
    )
    path = _write_nb([_md(collapsed)])
    assert "COLLAPSED-MARKDOWN" in _kinds(path)


def test_collapsed_heading_plus_fence_on_one_line():
    """Heading + fenced code opener + glued table rows (GenAI payoff diagrams).

    The detector keys on the glued GFM table separator (its documented
    signature); the heading+fence glue alone is a different, out-of-scope
    defect. This cell is flagged because the table rows are also collapsed.
    """
    collapsed = (
        "### Diagramme des payoffs  ``` LONG CALL ... LONG PUT ... ```  "
        "| Stratégie | Payoff ||-----------|--------|| Call | +∞ |"
    )
    assert _has_collapsed_markdown(collapsed)


def test_heading_fence_glue_without_table_out_of_scope():
    """Heading + fence glued but NO table-separator fragment -> not flagged.

    Documents the detector's scope: it catches table-separator collapse
    (#3966), not pure heading/fence gluing. The latter is a separate defect.
    """
    glued = "### Diagramme des payoffs  ``` LONG CALL (Achat d'un Call)"
    assert not _has_collapsed_markdown(glued)


def test_collapsed_multiple_headings_on_one_line():
    """Multiple section headers glued (no table, but separator fragment absent)."""
    # No table-separator fragment here -> NOT a collapsed-markdown case per the
    # detector's signature (it keys on a glued table separator). This documents
    # the detector's scope: it catches table-collapse, not heading-only gluing.
    glued = "## Partie 4### 4.1 Concept Lorem ipsum"
    assert not _has_collapsed_markdown(glued)


# ---------------------------------------------------------------------------
# COLLAPSED-MARKDOWN — false positives (must stay SILENT)
# ---------------------------------------------------------------------------

def test_clean_table_not_flagged():
    """A well-formed GFM table with its separator on its own line is clean."""
    clean = (
        "| Colonne A | Colonne B |\n"
        "|-----------|-----------|\n"
        "| 1         | 2         |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_blockquoted_table_not_flagged():
    """A blockquoted table (`> |---|---|`) is a legit table, not collapsed."""
    clean = (
        "> | Avantage | Inconvénient |\n"
        "> |----------|--------------|\n"
        "> | rapide   | coûteux      |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_aligned_table_not_flagged():
    """Alignment colons in the separator are still a clean separator row."""
    clean = (
        "| Gauche | Centre | Droite |\n"
        "|:-------|:------:|-------:|\n"
        "| a      | b      | c      |\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_table_without_trailing_pipes_not_flagged():
    """GFM allows tables without trailing pipes (`|---|---`, no closing `|`).

    Regression guard: an earlier version of CLEAN_SEP_LINE_RE required a trailing
    pipe and false-positived on these, caught on Sudoku-6 cell 1 (a valid table).
    """
    clean = (
        "| Composant | Description | Taille\n"
        "|-----------|-------------|-------\n"
        "| **Variables** | $X_{i,j}$ | 81\n"
        "| **Domaines** | $D_{i,j}$ | 9\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_table_no_trailing_pipe_and_aligned_not_flagged():
    """Mix: no trailing pipe + alignment colons is still a clean separator."""
    clean = (
        "| Algo | Type\n"
        "|:-----|----:\n"
        "| BT   | Recherche\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_fence_with_table_inside_not_flagged():
    """A fenced code block documenting a table (newlines intact) is clean."""
    clean = (
        "Exemple de tableau markdown :\n"
        "```\n"
        "| a | b |\n"
        "|---|---|\n"
        "| 1 | 2 |\n"
        "```\n"
    )
    assert not _has_collapsed_markdown(clean)


def test_clean_cell_without_any_table_not_flagged():
    """A normal prose+heading cell with no table is never flagged."""
    clean = "## Introduction\n\nDu paragraphe normal ici.\n"
    assert not _has_collapsed_markdown(clean)


# ---------------------------------------------------------------------------
# Integration — scan_notebook end-to-end
# ---------------------------------------------------------------------------

def test_scan_clean_notebook_no_findings():
    cells = [
        _md("# Titre du notebook\n"),
        _md("## Section\n\n| A | B |\n|---|---|\n| 1 | 2 |\n"),
        _code("print('ok')"),
    ]
    assert _kinds(_write_nb(cells)) == []


def test_scan_collapsed_cell_flagged_integration():
    cells = [
        _md("# Titre\n"),
        _md("## Synthèse| Cas | Verdict ||-----|---------|| a | ok |"),
    ]
    kinds = _kinds(_write_nb(cells))
    assert "COLLAPSED-MARKDOWN" in kinds


# ---------------------------------------------------------------------------
# Regression guard — pre-existing checks still work
# ---------------------------------------------------------------------------

def test_h1_deep_still_detected():
    """An H1 in the 2nd markdown cell (not the first) is still H1-DEEP."""
    cells = [
        _md("# Premier titre\n"),
        _md("Texte\n"),
        _md("# Deuxième H1 profond\n"),
    ]
    assert "H1-DEEP" in _kinds(_write_nb(cells))


def test_multi_h1_still_detected():
    cells = [_md("# H1 un\n"), _md("# H1 deux\n")]
    assert "MULTI-H1" in _kinds(_write_nb(cells))


def test_hint_as_heading_still_detected():
    """A bare `## Note` aside is still HINT-AS-HEADING."""
    cells = [_md("# Titre\n"), _md("## Note\n")]
    assert "HINT-AS-HEADING" in _kinds(_write_nb(cells))


def test_titled_step_not_hint():
    """`## Étape 3 : Titre` is a real section header, not a bare aside."""
    cells = [_md("# Titre\n"), _md("## Étape 3 : Installation\n")]
    assert "HINT-AS-HEADING" not in _kinds(_write_nb(cells))
