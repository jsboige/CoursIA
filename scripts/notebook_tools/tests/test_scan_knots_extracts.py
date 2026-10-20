"""Tests for scripts/notebook_tools/scan_knots_extracts.py -- voie (B) KNOTS.

Couvre les 3 classes de defaut documentees dans #21007 :
  - classe 2 : stale identite (FigureEight = 4_1, pas 8_1)
  - classe 3 : stale TODO (knot_11n102_diagram entre au head)

Le test couvre la logique des fonctions scan_classe2 et scan_classe3
en injectant des cellules markdown avec contenu stale ou frais, sur
un repo_root bidon (tmp_path) qui n'a pas besoin d'etre un vrai depot.

Note : le scan reference FIGURE_EIGHT_FILE et LIDMAN_FILE en chemin
absolu depuis le repo root. Les tests creent ces fichiers en local
pour valider la logique end-to-end.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_knots_extracts import (
    FIGURE_EIGHT_FILE,
    LIDMAN_FILE,
    iter_notebook_cells,
    scan_classe2,
    scan_classe3,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source if isinstance(source, list) else [source]}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source if isinstance(source, list) else [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


def _write_ground_truth_files(repo_root: Path) -> None:
    """Pose les 2 fichiers .lean de ground truth a leur chemin canonique."""
    figure_eight = repo_root / FIGURE_EIGHT_FILE
    figure_eight.parent.mkdir(parents=True, exist_ok=True)
    # Le header du module declare explicitement 4_1
    figure_eight.write_text(
        "/-- Knots.FigureEight -- Invariants du noeud 4_1 sur son code PD plan -/\n"
        "namespace Knots\n"
        "def FigureEight : Knot where\n"
        "  pd_code := [[4,2,5,1], [8,6,1,3], [6,4,7,5], [2,8,3,7]]\n",
        encoding="utf-8",
    )
    lidman = repo_root / LIDMAN_FILE
    lidman.parent.mkdir(parents=True, exist_ok=True)
    lidman.write_text(
        "/-- Knots.Lidman -- 11-crossing knots (subset) -/\n"
        "namespace Knots\n"
        "def knot_11n102_diagram : PDCode where\n"
        "  numEdges := 22\n"
        "def knot_11n102 : Knot where\n"
        "  diagram := knot_11n102_diagram\n",
        encoding="utf-8",
    )


# ---------------------------------------------------------------------------
# iter_notebook_cells : smoke test
# ---------------------------------------------------------------------------

class TestIterNotebookCells:
    def test_yields_all_cells(self, tmp_path: Path):
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [_md("a"), _code("b"), _md("c")])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 3
        assert [c[0] for c in cells] == [0, 1, 2]
        assert [c[1] for c in cells] == ["markdown", "code", "markdown"]

    def test_skips_empty_cells(self, tmp_path: Path):
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [_md("a"), _md("   \n  "), _md("c")])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 2

    def test_handles_source_as_list(self, tmp_path: Path):
        # ipynb stores source as a list of strings (one per line)
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [{"cell_type": "markdown", "source": ["line1\n", "line2\n"]}])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 1
        assert "line1" in cells[0][2]
        assert "line2" in cells[0][2]


# ---------------------------------------------------------------------------
# Classe 2 -- scan_classe2 : stale identite FigureEight (4_1 vs 8_1)
# ---------------------------------------------------------------------------

class TestScanClasse2:
    def test_fresh_4_1_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "FigureEight.lean modelise le noeud 4_1 (quatre-un)."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []

    def test_stale_8_1_yields_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "FigureEight.lean (noeud 8_1) -- invariants du twist."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert len(findings) == 1
        assert "STALE_IDENTITY" in findings[0]
        assert "8_1" in findings[0]
        assert "4_1" in findings[0]

    def test_stale_8_2_yields_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "see FigureEight (8_2) for the alternative parameterization."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert len(findings) == 1
        assert "8_2" in findings[0]

    def test_no_figure_eight_mention_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "we discuss knot 4_1 and 3_1 (trefoil) in this cell."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []

    def test_missing_ground_truth_no_finding(self, tmp_path: Path):
        # Pas de _write_ground_truth_files -- FigureEight.lean absent
        src = "FigureEight.lean (noeud 8_1) -- stale."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, tmp_path)
        # Defensif : on ne sait pas conclure, donc pas de finding.
        assert findings == []


# ---------------------------------------------------------------------------
# Classe 3 -- scan_classe3 : stale TODO knot_11n102_diagram
# ---------------------------------------------------------------------------

class TestScanClasse3:
    def test_fresh_no_stale_marker_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = (
            "knot_11n102_diagram est defini dans Lidman.lean (numEdges := 22). "
            "C'est l'etat actuel du head."
        )
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []

    def test_stale_todo_yields_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "11n102_diagram n'est pas entre, c'est un TODO PD-code."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert len(findings) == 1
        assert "STALE_TODO" in findings[0]
        assert "11n102" in findings[0]

    def test_stale_avec_caveat_annule(self, tmp_path: Path):
        # Caveat "au head" doit annuler le finding meme si le marker
        # "manquant" est present.
        _write_ground_truth_files(tmp_path)
        src = (
            "11n102_diagram etait marque manquant mais au head le PD-code "
            "est desormais entre. Voir Lidman.lean l. 67."
        )
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []

    def test_no_lidman_mention_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "we discuss knot 11n_42 (different knot entirely)."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []

    def test_missing_ground_truth_no_finding(self, tmp_path: Path):
        # Lidman.lean absent -- on ne peut pas conclure.
        src = "11n102_diagram n'est pas defini."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, tmp_path)
        assert findings == []


# ---------------------------------------------------------------------------
# scan_notebook : orchestration end-to-end
# ---------------------------------------------------------------------------

class TestScanNotebook:
    def test_clean_notebook_no_findings(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [
            _md("FigureEight.lean = 4_1 (quatre-un)."),
            _md("11n102_diagram est dans Lidman.lean."),
        ])
        findings = scan_notebook(nb, tmp_path)
        assert findings == []

    def test_mixed_stale_yields_both_findings(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [
            _md("FigureEight.lean (noeud 8_1) -- c'est faux, c'est 4_1."),
            _md("11n102_diagram n'est pas entre, c'est un TODO PD-code."),
        ])
        findings = scan_notebook(nb, tmp_path)
        assert len(findings) == 2
        assert any("STALE_IDENTITY" in f for f in findings)
        assert any("STALE_TODO" in f for f in findings)

    def test_load_error_returns_one_finding(self, tmp_path: Path):
        nb = tmp_path / "KNOTS" / "broken.ipynb"
        nb.parent.mkdir(parents=True, exist_ok=True)
        nb.write_text("not a notebook {", encoding="utf-8")
        findings = scan_notebook(nb, tmp_path)
        assert len(findings) == 1
        assert "load_error" in findings[0] or "lecture" in findings[0]
