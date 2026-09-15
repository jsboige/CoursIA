"""Tests for scripts/notebook_tools/generate_parcours.py — student parcours generator.

Tests focus on pure functions: filter_for_parcours, generate_parcours_page,
check_coverage. Uses synthetic catalog entries.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import generate_parcours as gp
from generate_parcours import (
    GENERATED_MARKER,
    GENERATED_MARKER_SCAN_LINES,
    PARCOURS,
    check_coverage,
    filter_for_parcours,
    generate_parcours_page,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

SAMPLE_ENTRIES = [
    {"path": "Search/Part1/Search-1.ipynb", "title": "BFS", "serie": "Search",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "Search/Part2/CSP-1.ipynb", "title": "CSP Intro", "serie": "Search",
     "maturity": "BETA", "status": "READY", "executable_locally": True,
     "sous_serie": "Part2-CSP"},
    {"path": "Sudoku/Sudoku-01.ipynb", "title": "Sudoku Base", "serie": "Sudoku",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "GenAI/Image/GenAI-1.ipynb", "title": "Image Gen", "serie": "GenAI",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "GenAI/Audio/GenAI-10.ipynb", "title": "Audio", "serie": "GenAI",
     "maturity": "ALPHA", "status": "READY", "executable_locally": False},
    {"path": "SymbolicAI/Lean/Lean-1.ipynb", "title": "Lean Intro", "serie": "SymbolicAI",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    {"path": "QuantConnect/QC-1.ipynb", "title": "QC Intro", "serie": "QuantConnect",
     "maturity": "BETA", "status": "READY", "executable_locally": False},
    {"path": "ML/ML-1.ipynb", "title": "ML Intro", "serie": "ML",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "Probas/Probas-1.ipynb", "title": "Probas", "serie": "Probas",
     "maturity": "PRODUCTION", "status": "READY", "executable_locally": True},
    {"path": "IIT/IIT-1.ipynb", "title": "IIT", "serie": "IIT",
     "maturity": "ALPHA", "status": "READY", "executable_locally": True},
    {"path": "RL/RL-1.ipynb", "title": "RL", "serie": "RL",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    {"path": "GameTheory/GT-1.ipynb", "title": "Game Theory", "serie": "GameTheory",
     "maturity": "BETA", "status": "READY", "executable_locally": True},
    # BROKEN — should be excluded
    {"path": "Search/Part3/Broken.ipynb", "title": "Broken", "serie": "Search",
     "maturity": "PRODUCTION", "status": "BROKEN", "executable_locally": False},
    # DRAFT — should be excluded from parcours with maturity_filter PRODUCTION/BETA
    {"path": "Search/Part1/Draft.ipynb", "title": "Draft", "serie": "Search",
     "maturity": "DRAFT", "status": "READY", "executable_locally": True},
]


# ---------------------------------------------------------------------------
# filter_for_parcours
# ---------------------------------------------------------------------------

class TestFilterForParcours:
    def test_ia_classique_search_and_sudoku(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        series = {e["serie"] for e in result}
        assert series == {"Search", "Sudoku"}

    def test_ia_classique_excludes_broken(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        assert not any(e["status"] == "BROKEN" for e in result)

    def test_ia_classique_excludes_draft(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        assert not any(e["maturity"] == "DRAFT" for e in result)

    def test_genai_includes_alpha(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        assert any(e["maturity"] == "ALPHA" for e in result)

    def test_trading_includes_quantconnect_and_ml(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "trading")
        series = {e["serie"] for e in result}
        assert "QuantConnect" in series
        assert "ML" in series

    def test_recherche_includes_probas_iit_rl(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "recherche")
        series = {e["serie"] for e in result}
        assert "Probas" in series
        assert "IIT" in series
        assert "RL" in series
        assert "GameTheory" in series

    def test_ia_symbolique_only_symbolic(self):
        result = filter_for_parcours(SAMPLE_ENTRIES, "ia-symbolique")
        series = {e["serie"] for e in result}
        assert series == {"SymbolicAI"}

    def test_empty_entries(self):
        result = filter_for_parcours([], "ia-classique")
        assert result == []


# ---------------------------------------------------------------------------
# generate_parcours_page
# ---------------------------------------------------------------------------

class TestGenerateParcoursPage:
    def test_has_title(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "# IA Classique" in page

    def test_has_subtitle(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "Recherche, CSP et résolution" in page

    def test_has_statistics(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert "## Statistiques" in page
        assert "| Notebooks |" in page
        assert "| PRODUCTION |" in page

    def test_notebook_count_matches(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "ia-classique")
        page = generate_parcours_page("ia-classique", entries)
        assert f"| Notebooks | {len(entries)} |" in page

    def test_has_table_rows(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        page = generate_parcours_page("genai", entries)
        assert "| Notebook |" in page
        assert "Maturité" in page

    def test_executable_column(self):
        entries = filter_for_parcours(SAMPLE_ENTRIES, "genai")
        page = generate_parcours_page("genai", entries)
        assert "Oui" in page
        assert "Non" in page

    def test_empty_entries(self):
        page = generate_parcours_page("ia-classique", [])
        assert "| Notebooks | 0 |" in page


# ---------------------------------------------------------------------------
# check_coverage
# ---------------------------------------------------------------------------

class TestCheckCoverage:
    def test_coverage_reports(self, capsys):
        check_coverage(SAMPLE_ENTRIES)
        output = capsys.readouterr().out
        assert "Coverage:" in output

    def test_full_coverage_no_uncovered(self, capsys):
        """All PRODUCTION/BETA in SAMPLE_ENTRIES should be covered by some parcours."""
        check_coverage(SAMPLE_ENTRIES)
        output = capsys.readouterr().out
        # Broken is excluded from prod/beta check
        # Search PRODUCTION (BFS) + Sudoku PRODUCTION + GenAI PRODUCTION +
        # SymbolicAI BETA + QC BETA + ML PRODUCTION + Probas PRODUCTION +
        # Search BETA (CSP) + RL BETA + GameTheory BETA = 10
        assert "Coverage:" in output

    def test_empty_entries(self, capsys):
        check_coverage([])
        output = capsys.readouterr().out
        assert "Coverage: 0/0" in output


# ---------------------------------------------------------------------------
# PARCOURS constants
# ---------------------------------------------------------------------------

class TestParcoursConstants:
    def test_five_parcours(self):
        assert len(PARCOURS) == 5

    def test_all_have_required_keys(self):
        for pid, config in PARCOURS.items():
            assert "title" in config, f"{pid} missing title"
            assert "series" in config, f"{pid} missing series"
            assert "maturity_filter" in config, f"{pid} missing maturity_filter"
            assert "description" in config, f"{pid} missing description"

    def test_all_parcours_ids(self):
        expected = {"ia-classique", "ia-symbolique", "genai", "trading", "recherche"}
        assert set(PARCOURS.keys()) == expected

    def test_series_are_valid(self):
        all_series = set()
        for config in PARCOURS.values():
            all_series.update(config["series"])
        # Should cover known series
        assert "Search" in all_series
        assert "GenAI" in all_series
        assert "QuantConnect" in all_series


# ---------------------------------------------------------------------------
# Fail-closed write guard (#15882): refuser d'ecraser une page sans en-tete
# ---------------------------------------------------------------------------

MANUAL_BODY = "# Mon parcours manuel\n\nContenu ecrit a la main.\n"


def _run_main(monkeypatch, tmp_path, argv):
    """Isole le generateur sur tmp_path (catalogue vide + PARCOURS_DIR)."""
    (tmp_path / "catalog.json").write_text(json.dumps([]), encoding="utf-8")
    monkeypatch.setattr(gp, "CATALOG_PATH", tmp_path / "catalog.json")
    monkeypatch.setattr(gp, "PARCOURS_DIR", tmp_path / "curriculum")
    monkeypatch.setattr(sys, "argv", ["generate_parcours.py", *argv])


class TestFailClosedWrite:
    def test_manual_page_without_marker_is_refused_and_preserved(
            self, monkeypatch, tmp_path, capsys):
        _run_main(monkeypatch, tmp_path, [])
        out = tmp_path / "curriculum" / "trading.md"
        out.parent.mkdir(parents=True)
        out.write_text(MANUAL_BODY, encoding="utf-8")

        with pytest.raises(SystemExit) as exc:
            gp.main()
        assert exc.value.code == 2
        err = capsys.readouterr().err
        assert "trading.md" in err, "le message doit nommer le fichier refuse"
        assert "REFUS" in err
        # Fail-closed : le contenu manuel survit integralement.
        assert out.read_text(encoding="utf-8") == MANUAL_BODY

    def test_page_with_marker_is_regenerated(self, monkeypatch, tmp_path):
        _run_main(monkeypatch, tmp_path, ["--parcours", "trading"])
        out = tmp_path / "curriculum" / "trading.md"
        out.parent.mkdir(parents=True)
        # La page existante est une vraie page generee (en-tete marque) mais
        # perimee : la regen doit la reecrire.
        stale = generate_parcours_page("trading", []) + "\nSTALE RESIDU\n"
        out.write_text(stale, encoding="utf-8")

        gp.main()  # pas de SystemExit
        fresh = out.read_text(encoding="utf-8")
        assert "# Trading Algorithmique" in fresh
        assert "STALE RESIDU" not in fresh

    def test_absent_file_is_created(self, monkeypatch, tmp_path):
        _run_main(monkeypatch, tmp_path, ["--parcours", "genai"])
        gp.main()
        out = tmp_path / "curriculum" / "genai.md"
        assert out.exists()
        assert out.read_text(encoding="utf-8").startswith("<!--")

    def test_marker_deep_in_body_does_not_opt_in(
            self, monkeypatch, tmp_path):
        _run_main(monkeypatch, tmp_path, ["--parcours", "genai"])
        out = tmp_path / "curriculum" / "genai.md"
        out.parent.mkdir(parents=True)
        # Le marqueur cite au-dela de la fenetre de scan = prose, pas opt-in.
        pad = "\n".join(f"ligne {i}" for i in range(GENERATED_MARKER_SCAN_LINES + 5))
        out.write_text(
            MANUAL_BODY + pad + f"\nmention tardive : {GENERATED_MARKER}\n",
            encoding="utf-8",
        )

        with pytest.raises(SystemExit) as exc:
            gp.main()
        assert exc.value.code == 2
        assert MANUAL_BODY.splitlines()[0] in out.read_text(encoding="utf-8")

    def test_refused_target_does_not_block_clean_targets(
            self, monkeypatch, tmp_path, capsys):
        _run_main(monkeypatch, tmp_path, [])
        poisoned = tmp_path / "curriculum" / "genai.md"
        poisoned.parent.mkdir(parents=True)
        poisoned.write_text(MANUAL_BODY, encoding="utf-8")

        with pytest.raises(SystemExit) as exc:
            gp.main()
        assert exc.value.code == 2
        # Les cibles propres sont regenerees malgre le refus de la cible sale.
        clean = tmp_path / "curriculum" / "trading.md"
        assert clean.exists()
        assert "# Trading Algorithmique" in clean.read_text(encoding="utf-8")
        assert MANUAL_BODY.splitlines()[0] in poisoned.read_text(encoding="utf-8")
        summary = capsys.readouterr().err
        assert "genai.md" in summary
