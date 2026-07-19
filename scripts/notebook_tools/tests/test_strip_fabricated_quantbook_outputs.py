#!/usr/bin/env python3
"""Pytest roll-out for strip_fabricated_quantbook_outputs.py (cf #6891, sibling detecteur).

Le script lui-meme est verbatim depuis #7439 (soumis pour review). 8 clusters
miroirs de la logique de decision documentee dans le module.

Note : on importe le script via importlib (cf L800-L1 ★ -- conftest pre-existant
ne fait pas de sys.path.insert) pour eviter la collision avec le homonyme
detecteur importe par strip.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent
SCRIPT_PATH = SCRIPTS_DIR / "strip_fabricated_quantbook_outputs.py"

# Charger le module via importlib (cf L800-L1 ★ pattern).
_spec = importlib.util.spec_from_file_location(
    "strip_fabricated_quantbook_outputs", SCRIPT_PATH
)
strip_mod = importlib.util.module_from_spec(_spec)
sys.modules["strip_fabricated_quantbook_outputs"] = strip_mod
_spec.loader.exec_module(strip_mod)


# --- Helpers ---------------------------------------------------------------

def _code_cell(source_lines, outputs=None, execution_count=1):
    """Construit une cellule code avec source (list[str]) + outputs."""
    return {
        "cell_type": "code",
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
        "source": source_lines,
    }


def _markdown_cell(text):
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": text if isinstance(text, list) else [text],
    }


def _row_n_output(n_rows=3):
    """Sortie 'Row N' placeholder (fabrication signature)."""
    return {
        "output_type": "stream",
        "name": "stdout",
        "text": [f"Row {i}\n" for i in range(n_rows)],
    }


def _zero_stats_output():
    """Dataframe stats backtest entierement a 0.0."""
    return {
        "output_type": "execute_result",
        "data": {
            "text/plain": [
                "       Sharpe  CAGR  MaxDD  NetProfit\n"
                "row1    0.0   0.0    0.0        0.0\n"
            ]
        },
    }


def _blank_png_output():
    """Image/png < 200 bytes (axe 1 sibling)."""
    return {
        "output_type": "display_data",
        "data": {"image/png": "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNkYAAAAAYAAjCB0C8AAAAASUVORK5CYII="},
    }


def _write_nb(tmp_path, name, cells):
    """Ecrit un .ipynb avec les cells donnees."""
    nb = {
        "cells": cells,
        "metadata": {
            "kernelspec": {"name": "python3", "display_name": "Python 3"}
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / name
    p.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")
    return p


def _make_root(tmp_path, nb_paths_relative):
    """Construit un mini-repo avec quantbooks/ + notebooks non-cibles.

    Retourne (root, repo_root) ou root contient MyIA.AI.Notebooks/QuantConnect/projects/.
    """
    repo_root = tmp_path
    for rel in nb_paths_relative:
        full = repo_root / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / rel
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text(json.dumps({"cells": [], "metadata": {}, "nbformat": 4}, indent=1), encoding="utf-8")
    return repo_root


# --- Cluster 1 : DEFAULT_TARGETS ------------------------------------------

class TestDefaultTargets:
    """Les 8 quantbooks de #6891 sont listes par defaut."""

    def test_default_targets_contains_eight_quantbooks(self):
        assert len(strip_mod.DEFAULT_TARGETS) == 8

    def test_default_targets_includes_dual_momentum(self):
        assert "DualMomentum" in strip_mod.DEFAULT_TARGETS

    def test_default_targets_includes_all_weather(self):
        assert "AllWeather" in strip_mod.DEFAULT_TARGETS

    def test_default_targets_includes_ema_cross_alpha(self):
        assert "EMA-Cross-Alpha" in strip_mod.DEFAULT_TARGETS

    def test_default_targets_excludes_famafrench(self):
        """FamaFrench est hors scope #6891 (cf detecteur axe 2 le flag, mais
        n'est pas dans la liste body issue). Il sera traite dans un PR separe."""
        assert "FamaFrench" not in strip_mod.DEFAULT_TARGETS


# --- Cluster 2 : _resolve_quantbook_paths ----------------------------------

class TestResolveQuantbookPaths:
    """Resolution des paths vers les 8 quantbooks."""

    def test_resolves_existing_quantbook(self, tmp_path):
        p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "DualMomentum" / "quantbook.ipynb"
        p.parent.mkdir(parents=True)
        p.write_text("{}", encoding="utf-8")
        out = strip_mod._resolve_quantbook_paths(tmp_path, ["DualMomentum"])
        assert len(out) == 1
        assert out[0] == p

    def test_missing_quantbook_warns_to_stderr(self, tmp_path, capsys):
        out = strip_mod._resolve_quantbook_paths(tmp_path, ["Nonexistent"])
        captured = capsys.readouterr()
        assert "Nonexistent" in captured.err
        assert out == []

    def test_returns_empty_when_no_paths(self, tmp_path, capsys):
        out = strip_mod._resolve_quantbook_paths(tmp_path, [])
        assert out == []


# --- Cluster 3 : _strip_cell_outputs --------------------------------------

class TestStripCellOutputs:
    """Vidage des outputs + execution_count."""

    def test_strip_code_cell_with_outputs(self):
        cell = _code_cell(["x = 1"], outputs=[_row_n_output()], execution_count=1)
        changed = strip_mod._strip_cell_outputs(cell)
        assert changed is True
        assert cell["outputs"] == []
        assert cell["execution_count"] is None

    def test_no_change_when_cell_already_stripped(self):
        cell = _code_cell(["x = 1"], outputs=[], execution_count=None)
        changed = strip_mod._strip_cell_outputs(cell)
        assert changed is False

    def test_non_code_cell_ignored(self):
        cell = _markdown_cell("hello")
        changed = strip_mod._strip_cell_outputs(cell)
        assert changed is False

    def test_preserves_source(self):
        cell = _code_cell(["def foo():\n    return 42"], outputs=[_row_n_output()])
        strip_mod._strip_cell_outputs(cell)
        assert cell["source"] == ["def foo():\n    return 42"]


# --- Cluster 4 : _make_warning_cell ---------------------------------------

class TestMakeWarningCell:
    """Cellule markdown d'avertissement inseree apres le strip."""

    def test_creates_markdown_cell(self):
        cell = strip_mod._make_warning_cell("#6891")
        assert cell["cell_type"] == "markdown"

    def test_mentions_issue_reference(self):
        cell = strip_mod._make_warning_cell("#6891")
        src = "".join(cell["source"])
        assert "#6891" in src

    def test_includes_french_warning_text(self):
        """Conformite readme-french-first."""
        cell = strip_mod._make_warning_cell("#6891")
        src = "".join(cell["source"])
        assert "strippee" in src  # FR "strippee" (avec accent)


# --- Cluster 5 : _has_blank_png -------------------------------------------

class TestHasBlankPng:
    """Detection axe 1 blank PNG (cellule dont image/png < 200 bytes)."""

    def test_blank_png_detected(self):
        cell = _code_cell(["plt.show()"], outputs=[_blank_png_output()])
        assert strip_mod._has_blank_png(cell) is True

    def test_real_png_not_detected(self):
        """Un PNG > 200 bytes n'est pas un blank (axe 1 sibling threshold)."""
        real_png = "A" * 500  # bytes fictifs
        cell = _code_cell(["plt.show()"], outputs=[{
            "output_type": "display_data",
            "data": {"image/png": real_png},
        }])
        assert strip_mod._has_blank_png(cell) is False

    def test_no_image_output(self):
        cell = _code_cell(["x = 1"], outputs=[_row_n_output()])
        assert strip_mod._has_blank_png(cell) is False

    def test_threshold_constant_defined(self):
        """Le seuil 200 bytes est explicite (L728-L2 ★ pattern detector-sanity)."""
        assert strip_mod.BLANK_PNG_THRESHOLD == 200


# --- Cluster 6 : _plan_strip ----------------------------------------------

class TestPlanStrip:
    """Planification du strip (sans modification)."""

    def test_plan_includes_fabricated_text_cell(self):
        nb_cells = [_code_cell(["x = 1"], outputs=[_row_n_output()])]
        nb = {"cells": nb_cells}
        plan = strip_mod._plan_strip(nb)
        assert len(plan) == 1
        assert plan[0]["cell_index"] == 0
        assert plan[0]["findings"][0]["signal"] == "row_n_placeholder"

    def test_plan_includes_blank_png_when_requested(self):
        nb_cells = [_code_cell(["plt.show()"], outputs=[_blank_png_output()])]
        nb = {"cells": nb_cells}
        plan = strip_mod._plan_strip(nb, include_blank_png=True)
        assert len(plan) == 1
        signals = [f["signal"] for f in plan[0]["findings"]]
        assert "blank_png_axe1" in signals

    def test_plan_excludes_blank_png_by_default(self):
        """Le blank PNG n'est PAS couvert par defaut (axe 2 strict)."""
        nb_cells = [_code_cell(["plt.show()"], outputs=[_blank_png_output()])]
        nb = {"cells": nb_cells}
        plan = strip_mod._plan_strip(nb)
        assert plan == []

    def test_plan_includes_zero_stats_dataframe(self):
        """Mock le detecteur pour simuler un finding axe 2 'zero_stats_dataframe'.

        On teste l'orchestration de _plan_strip (single-source-of-truth = detector).
        Le detecteur lui-meme a sa propre suite de tests (test_detect_fabricated_outputs).
        """
        # Monkeypatch detector.detect_cell pour retourner un finding axe 2
        original_detect = strip_mod.detector.detect_cell

        def fake_detect(cell):
            if cell.get("outputs"):
                return [{"signal": "zero_stats_dataframe"}]
            return []

        strip_mod.detector.detect_cell = fake_detect
        try:
            nb_cells = [_code_cell(["result"], outputs=[_zero_stats_output()])]
            nb = {"cells": nb_cells}
            plan = strip_mod._plan_strip(nb)
            assert len(plan) == 1
            signals = [f["signal"] for f in plan[0]["findings"]]
            assert "zero_stats_dataframe" in signals
        finally:
            strip_mod.detector.detect_cell = original_detect

    def test_plan_empty_when_clean(self):
        nb_cells = [_code_cell(["x = 1"], outputs=[])]
        nb = {"cells": nb_cells}
        plan = strip_mod._plan_strip(nb, include_blank_png=True)
        assert plan == []

    def test_plan_skips_markdown_cells(self):
        nb_cells = [_markdown_cell("# titre"), _code_cell(["x = 1"], outputs=[_row_n_output()])]
        nb = {"cells": nb_cells}
        plan = strip_mod._plan_strip(nb)
        assert len(plan) == 1
        assert plan[0]["cell_index"] == 1


# --- Cluster 7 : _apply_plan ----------------------------------------------

class TestApplyPlan:
    """Application reelle du plan (strip + insertion markdown)."""

    def test_apply_strips_and_inserts_warning(self):
        nb = {"cells": [_code_cell(["x = 1"], outputs=[_row_n_output()])]}
        plan = strip_mod._plan_strip(nb)
        result = strip_mod._apply_plan(nb, plan, "#6891")
        assert result["n_stripped"] == 1
        assert result["n_inserted"] == 1
        # Cellule code a outputs=[]/execution_count=None
        assert nb["cells"][0]["outputs"] == []
        assert nb["cells"][0]["execution_count"] is None
        # Cellule markdown inseree apres
        assert nb["cells"][1]["cell_type"] == "markdown"

    def test_apply_with_multiple_cells_preserves_order(self):
        """L'insertion en ordre decroissant preserve la coherence des indices."""
        nb = {"cells": [
            _code_cell(["a = 1"], outputs=[_row_n_output(3)]),
            _markdown_cell("# section"),
            _code_cell(["b = 2"], outputs=[_row_n_output(5)]),
        ]}
        plan = strip_mod._plan_strip(nb)
        result = strip_mod._apply_plan(nb, plan, "#6891")
        assert result["n_stripped"] == 2
        assert result["n_inserted"] == 2
        # Cell 0 = code a (striped), Cell 1 = warning, Cell 2 = markdown section,
        # Cell 3 = code b (striped), Cell 4 = warning
        assert nb["cells"][0]["cell_type"] == "code"
        assert nb["cells"][1]["cell_type"] == "markdown"
        assert nb["cells"][2]["cell_type"] == "markdown"  # section preservee
        assert nb["cells"][3]["cell_type"] == "code"
        assert nb["cells"][4]["cell_type"] == "markdown"

    def test_apply_preserves_source_verbatim(self):
        """Stop&Repair : JAMAIS modifier le source."""
        nb = {"cells": [_code_cell(["def foo():\n    return 42"], outputs=[_row_n_output()])]}
        plan = strip_mod._plan_strip(nb)
        strip_mod._apply_plan(nb, plan, "#6891")
        assert nb["cells"][0]["source"] == ["def foo():\n    return 42"]


# --- Cluster 8 : main() argparse + integration ----------------------------

class TestMainCLI:
    """Tests CLI via monkeypatch sys.argv (pattern L728-L2 ★ c.728)."""

    def _run_main(self, argv, capsys, root=None):
        sys_argv_backup = sys.argv
        sys.argv = ["strip_fabricated_quantbook_outputs.py"] + argv
        try:
            rc = strip_mod.main()
        finally:
            sys.argv = sys_argv_backup
        out = capsys.readouterr().out
        return rc, out

    def test_list_outputs_eight_paths(self, tmp_path, capsys):
        """--list imprime les 8 paths relatifs et exit 0."""
        # Mock 8 quantbooks vides (juste pour resoudre les paths)
        for name in strip_mod.DEFAULT_TARGETS:
            p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            p.parent.mkdir(parents=True)
            p.write_text("{}", encoding="utf-8")
        rc, out = self._run_main(["--list", "--root", str(tmp_path)], capsys)
        assert rc == 0
        lines = [l for l in out.splitlines() if l.strip()]
        assert len(lines) == 8
        for name in strip_mod.DEFAULT_TARGETS:
            assert any(name in line for line in lines)

    def test_check_outputs_json_report(self, tmp_path, capsys):
        """--check produit un rapport JSON structuré."""
        for name in strip_mod.DEFAULT_TARGETS:
            cells = []
            if name == "DualMomentum":
                cells = [_code_cell(["x = 1"], outputs=[_row_n_output()])]
            p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            p.parent.mkdir(parents=True)
            p.write_text(json.dumps({"cells": cells, "metadata": {}, "nbformat": 4}), encoding="utf-8")
        rc, out = self._run_main(
            ["--check", "--root", str(tmp_path)],
            capsys,
        )
        assert rc == 0
        report = json.loads(out)
        assert report["issue"] == "#6891"
        assert len(report["notebooks"]) == 8
        # DualMomentum doit etre flagged (Row N)
        dm = next(n for n in report["notebooks"] if "DualMomentum" in n["path"])
        assert dm["n_cells_flagged"] == 1

    def test_check_with_include_blank_png(self, tmp_path, capsys):
        """--include-blank-png flagge aussi les cellules image/png < 200 bytes."""
        cells = [_code_cell(["plt.show()"], outputs=[_blank_png_output()])]
        p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "EMA-Cross-Alpha" / "quantbook.ipynb"
        p.parent.mkdir(parents=True)
        p.write_text(json.dumps({"cells": cells, "metadata": {}, "nbformat": 4}), encoding="utf-8")
        # Stub les autres 7 avec cellules vides pour eviter les faux positifs
        for name in strip_mod.DEFAULT_TARGETS:
            if name == "EMA-Cross-Alpha":
                continue
            q = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            q.parent.mkdir(parents=True)
            q.write_text(json.dumps({"cells": [], "metadata": {}, "nbformat": 4}), encoding="utf-8")
        rc, out = self._run_main(
            ["--check", "--include-blank-png", "--root", str(tmp_path)],
            capsys,
        )
        assert rc == 0
        report = json.loads(out)
        ema = next(n for n in report["notebooks"] if "EMA-Cross-Alpha" in n["path"])
        assert ema["n_cells_flagged"] == 1
        assert ema["include_blank_png"] is True

    def test_apply_strips_and_writes_files(self, tmp_path, capsys):
        """--apply ecrit les .ipynb avec outputs vides + warnings inserees."""
        cells = [_code_cell(["x = 1"], outputs=[_row_n_output()])]
        p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "DualMomentum" / "quantbook.ipynb"
        p.parent.mkdir(parents=True)
        p.write_text(json.dumps({"cells": cells, "metadata": {}, "nbformat": 4}), encoding="utf-8")
        # Stub les autres 7 (sinon Resolution miss -> warning stderr -> potentiellement fail)
        for name in strip_mod.DEFAULT_TARGETS:
            if name == "DualMomentum":
                continue
            q = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            q.parent.mkdir(parents=True)
            q.write_text(json.dumps({"cells": [], "metadata": {}, "nbformat": 4}), encoding="utf-8")
        rc, out = self._run_main(
            ["--apply", "--root", str(tmp_path)],
            capsys,
        )
        assert rc == 0
        result = json.loads(out)
        assert result["total_stripped"] == 1
        assert result["total_inserted"] == 1
        # Verifier le contenu ecrit
        written = json.loads(p.read_text(encoding="utf-8"))
        assert written["cells"][0]["outputs"] == []
        assert written["cells"][0]["execution_count"] is None
        assert written["cells"][1]["cell_type"] == "markdown"
        assert "#6891" in "".join(written["cells"][1]["source"])

    def test_no_args_returns_error(self, capsys):
        """Ni --check ni --apply ni --list = argparse.error() -> SystemExit(2)."""
        sys_argv_backup = sys.argv
        sys.argv = ["strip_fabricated_quantbook_outputs.py"]
        try:
            with pytest.raises(SystemExit) as exc_info:
                strip_mod.main()
            assert exc_info.value.code != 0
        finally:
            sys.argv = sys_argv_backup


# --- Cluster 9 : end-to-end subprocess smoke test --------------------------

class TestEndToEnd:
    """Subprocess smoke test sur mini-repo synthesized (L728-L2 ★ pattern)."""

    def test_subprocess_check_succeeds(self, tmp_path):
        """Le script est executable + produit un rapport JSON valide."""
        for name in strip_mod.DEFAULT_TARGETS:
            p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            p.parent.mkdir(parents=True)
            p.write_text(json.dumps({"cells": [], "metadata": {}, "nbformat": 4}), encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(SCRIPT_PATH), "--check", "--root", str(tmp_path)],
            capture_output=True, text=True, timeout=60,
        )
        assert result.returncode == 0
        report = json.loads(result.stdout)
        assert "notebooks" in report
        assert len(report["notebooks"]) == 8

    def test_subprocess_list_outputs_eight_paths(self, tmp_path):
        for name in strip_mod.DEFAULT_TARGETS:
            p = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name / "quantbook.ipynb"
            p.parent.mkdir(parents=True)
            p.write_text("{}", encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(SCRIPT_PATH), "--list", "--root", str(tmp_path)],
            capture_output=True, text=True, timeout=60,
        )
        assert result.returncode == 0
        lines = [l for l in result.stdout.splitlines() if l.strip()]
        assert len(lines) == 8


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))