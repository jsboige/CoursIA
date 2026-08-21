"""Tests for the HEADING-IN-LIST detector (#11829 sous-issue #1).

An ATX heading nested inside a list item / blockquote (`- # Indice : ...`,
`> # Note`, `1. # Astuce`) renders as a REAL heading under CommonMark -- the
same giant font as a bare `# Indice`. The `^`-anchored HEADING_RE of both
scanners never saw those lines, which is how the 6 hits of PR #11823 (and
1325 corpus-wide) survived the #3968 burndown unflagged.

Locks in, for BOTH scan_md_hierarchy.py (kind HEADING-IN-LIST) and
detect_markdown_rendering.py (rule heading_in_list):
  - true positives: every container prefix (- * + > 1. 1)), indent, nesting
  - true negatives: glued `#tag` (no space = not a heading), mid-line `#`,
    in-fence `# comment`, bare headings (stay in their pre-existing kinds)
  - the real-world repro: the 6 QC-Py-Cloud-04-RL-DQN lines of #11823
"""

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_md_hierarchy import scan_notebook  # noqa: E402
from detect_markdown_rendering import scan_notebook as scan_render  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source) -> dict:
    if isinstance(source, str):
        source = [source]
    return {"cell_type": "markdown", "source": source}


def _write_nb(cells: list[dict]) -> str:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    f = tempfile.NamedTemporaryFile(
        mode="w", suffix=".ipynb", delete=False, encoding="utf-8")
    json.dump(nb, f)
    f.close()
    return f.name


def _hier_kinds(path: str) -> list[str]:
    return [f["kind"] for f in scan_notebook(path)]


def _render_rules(path: str) -> list[str]:
    return [f["rule"] for f in scan_render(Path(path))]


# ---------------------------------------------------------------------------
# True positives -- every container prefix form (#11829 acceptance)
# ---------------------------------------------------------------------------

def test_bullet_dash():
    path = _write_nb([_md("- # Indice : choisir argmax(Q)")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)
    assert "heading_in_list" in _render_rules(path)


def test_bullet_star():
    path = _write_nb([_md("* # Astuce : verifier les shapes")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_bullet_plus():
    path = _write_nb([_md("+ # Note : re-exec avant commit")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_blockquote():
    path = _write_nb([_md("> # Rappel : la regle C.2 exige les outputs")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)
    assert "heading_in_list" in _render_rules(path)


def test_ordered_dot():
    path = _write_nb([_md("1. # Etape : implementer le solver")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_ordered_paren():
    path = _write_nb([_md("1) # Etape : valider les bornes")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_indented_two_levels():
    path = _write_nb([_md("  - # Indice : la fonction est concave")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_nested_containers():
    # a quoted list item containing a heading: 2 container markers
    path = _write_nb([_md("> - # Indice : decorreler les evenements")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_three_container_markers():
    path = _write_nb([_md("  - 1. # Hint : three levels deep")])
    assert "HEADING-IN-LIST" in _hier_kinds(path)


def test_level_reported_not_h1_counters():
    """An in-list H1 is HEADING-IN-LIST once -- it must NOT also feed
    MULTI-H1 / H1-DEEP (primary defect reported once, by its own kind)."""
    cells = [_md("# Titre du notebook"),
             _md("- # Indice : premier"),
             _md("- # Indice : second")]
    kinds = _hier_kinds(_write_nb(cells))
    assert kinds.count("HEADING-IN-LIST") == 2
    assert "MULTI-H1" not in kinds
    assert "H1-DEEP" not in kinds


# ---------------------------------------------------------------------------
# True negatives -- forms that are NOT in-list headings
# ---------------------------------------------------------------------------

def test_glued_hash_not_a_heading():
    # CommonMark requires a space after the hashes: `- #tag` is a list item
    # whose text starts with a literal '#', NOT a heading.
    path = _write_nb([_md("- #hashtag pas un heading")])
    assert "HEADING-IN-LIST" not in _hier_kinds(path)
    assert "heading_in_list" not in _render_rules(path)


def test_mid_line_hash_ignored():
    path = _write_nb([_md("Le symbole # en milieu de phrase reste du texte.")])
    assert "HEADING-IN-LIST" not in _hier_kinds(path)


def test_in_fence_not_flagged():
    fenced = ["```python", "- # Indice : ceci est un commentaire python", "```"]
    path = _write_nb([_md(fenced)])
    assert "HEADING-IN-LIST" not in _hier_kinds(path)
    assert "heading_in_list" not in _render_rules(path)


def test_bare_heading_unchanged_behavior():
    """A bare `# Indice :` outside any container keeps its pre-existing kind
    (HINT-AS-HEADING in scan_md_hierarchy) -- the new detector must not
    duplicate or replace the old classification."""
    path = _write_nb([_md("## Indice : pas de spoiler")])
    kinds = _hier_kinds(path)
    assert "HINT-AS-HEADING" in kinds
    assert "HEADING-IN-LIST" not in kinds


# ---------------------------------------------------------------------------
# The real-world repro -- the 6 unflagged hits of PR #11823 (#11829 exhibit)
# ---------------------------------------------------------------------------

QC_PY_CLOUD_04_LINES = [
    "- # Indice : Si random() < epsilon, choisir une action aleatoire, sinon argmax(Q).",
    "- # Indice : Epsilon decroit exponentiellement : eps(t+1) = eps(t) * decay.",
    "- # Indice : Utilisez `collections.deque(maxlen=capacity)` pour un buffer a taille fixe.",
    "- # Indice : `random.sample(buffer, batch_size)` echantillonne sans remplacement.",
    "- # Indice : La fonction est concave : elle croit moins vite pour les grands rendements positifs.",
    "- # Indice : Pour r = 0, les deux fonctions coincident. Pour r < 0, la penalite est plus forte.",
]


def test_qc_py_cloud_04_all_six_hits():
    """The exact exhibit of #11829: 6 in-list H1 hints across 3 cells, each
    cell split into 2 lines as in the real notebook (cells 2, 14, 16).

    Source lines carry their trailing ``\\n`` (as nbformat stores them): a
    newline-stripped fixture would trip ``source_list_missing_newlines``,
    whose early return (line structure lost -> downstream line-based rules
    have nothing to inspect) is a DIFFERENT defect than the one under test.
    """
    def _md_lines(lines: list[str]) -> dict:
        return {"cell_type": "markdown", "source": [ln + "\n" for ln in lines]}

    cells = [
        _md("# QC-Py-Cloud-04 titre"),
        _md_lines(QC_PY_CLOUD_04_LINES[0:2]),
        _md_lines(QC_PY_CLOUD_04_LINES[2:4]),
        _md_lines(QC_PY_CLOUD_04_LINES[4:6]),
    ]
    path = _write_nb(cells)
    findings = [f for f in scan_notebook(path) if f["kind"] == "HEADING-IN-LIST"]
    assert len(findings) == 6
    assert all(f["level"] == 1 for f in findings)
    assert "heading_in_list" in _render_rules(path)
