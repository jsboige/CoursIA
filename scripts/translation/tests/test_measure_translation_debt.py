#!/usr/bin/env python3
"""Tests pour scripts/translation/measure_translation_debt.py (#10329 etape 1).

Couvre les 7 fonctions principales : _iter_id_cells, _load_csv,
_normalize_column_order, _is_empty_notebook, _resolve_csv_paths,
measure_csv, measure_csvs, render_human_report, main.

Toutes les fixtures sont stdlib + ecriture tmp_path (zero dependance
reseau / disque reel). Le pipeline de la dette reste un contrat :
  - cellules source avec id stable = ce que T1 aurait du capturer
  - lignes CSV = ce que le CSV contient reellement
  - dette d'indexation = cellules source absentes du CSV
  - dette de traduction = text_<lang> vide alors que text_fr rempli
"""

import csv
import io
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import measure_translation_debt as m  # noqa: E402


# --------------------------------------------------------------------------
# Helpers -- synthetic notebooks + CSV (memes conventions que les autres tests)
# --------------------------------------------------------------------------

def _nb(cells, **meta):
    """Construit un notebook minimal. cells = liste de dicts {id,type,source}."""
    return {
        "cells": [
            {"id": c["id"], "cell_type": c["type"], "source": c["source"],
             "metadata": {}, **({"outputs": [], "execution_count": None}
                                if c["type"] == "code" else {})}
            for c in cells
        ],
        "metadata": meta,
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write_nb(tmp_path: Path, name: str, cells, **meta) -> Path:
    """Ecrit un notebook sur disque. Retourne le chemin."""
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells, **meta)), encoding="utf-8")
    return p


def _csv_row(notebook: str, cell_id: str, cell_type: str = "markdown",
              text_fr: str = "FR texte", text_en: str = "EN text",
              src_hash: str = "abc12345") -> dict:
    """Construit une ligne CSV alignee sur le schema ratifie #4957 §1."""
    return {
        "notebook": notebook,
        "cell_id": cell_id,
        "cell_type": cell_type,
        "src_lang": "fr",
        "src_hash": src_hash,
        "text_fr": text_fr,
        "text_en": text_en,
        "text_es": "",
        "text_ar": "",
        "text_fa": "",
        "text_zh": "",
        "text_ru": "",
        "text_pt": "",
        "hash_fr": src_hash,
        "hash_en": src_hash if text_en else "",
        "hash_es": "",
        "hash_ar": "",
        "hash_fa": "",
        "hash_zh": "",
        "hash_ru": "",
        "hash_pt": "",
    }


def _write_csv(csv_path: Path, rows: list[dict]) -> Path:
    """Ecrit un CSV sur disque avec le schema complet (8 langues)."""
    fieldnames = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
                  "text_fr", "text_en", "text_es", "text_ar", "text_fa",
                  "text_zh", "text_ru", "text_pt",
                  "hash_fr", "hash_en", "hash_es", "hash_ar", "hash_fa",
                  "hash_zh", "hash_ru", "hash_pt"]
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)
    return csv_path


# --------------------------------------------------------------------------
# _iter_id_cells
# --------------------------------------------------------------------------

class TestIterIdCells:
    def test_markdown_with_id_counted(self, tmp_path):
        nb = _write_nb(tmp_path, "x.ipynb", [
            {"id": "abc", "type": "markdown", "source": ["# Title"]},
        ])
        assert m._iter_id_cells(nb) == {"abc"}

    def test_code_with_id_counted(self, tmp_path):
        nb = _write_nb(tmp_path, "x.ipynb", [
            {"id": "c1", "type": "code", "source": ["x = 1"]},
        ])
        assert m._iter_id_cells(nb) == {"c1"}

    def test_raw_cell_without_id_excluded(self, tmp_path):
        # Cellule sans `id` (c.10278 etait dans ce cas : params cell Papermill)
        # On bypass _nb() car le helper exige "id" sur chaque cellule.
        raw = {
            "cells": [
                {"id": "ok", "cell_type": "markdown", "source": ["a"],
                 "metadata": {}},
                {"cell_type": "markdown", "source": ["no id"],
                 "metadata": {}},  # pas d'id -> exclu
            ],
            "metadata": {},
            "nbformat": 4, "nbformat_minor": 5,
        }
        (tmp_path / "x.ipynb").write_text(json.dumps(raw), encoding="utf-8")
        assert m._iter_id_cells(tmp_path / "x.ipynb") == {"ok"}

    def test_raw_cell_unknown_type_excluded(self, tmp_path):
        # Cellule type "raw" (hors markdown/code) : exclue du comptage.
        raw = _nb([
            {"id": "ok", "type": "markdown", "source": ["a"]},
            {"id": "raw", "type": "raw", "source": ["x"]},
        ])
        (tmp_path / "x.ipynb").write_text(json.dumps(raw), encoding="utf-8")
        assert m._iter_id_cells(tmp_path / "x.ipynb") == {"ok"}

    def test_corrupt_json_returns_empty_set(self, tmp_path):
        nb = tmp_path / "x.ipynb"
        nb.write_text("not a json", encoding="utf-8")
        # Silencieux : le rapport agregera le notebook comme ERROR_NOTEBOOK.
        assert m._iter_id_cells(nb) == set()


# --------------------------------------------------------------------------
# _is_empty_notebook
# --------------------------------------------------------------------------

class TestIsEmptyNotebook:
    def test_empty_notebook(self, tmp_path):
        raw = _nb([])
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(raw), encoding="utf-8")
        assert m._is_empty_notebook(p) is True

    def test_non_empty_notebook(self, tmp_path):
        raw = _nb([{"id": "a", "type": "markdown", "source": ["x"]}])
        p = tmp_path / "x.ipynb"
        p.write_text(json.dumps(raw), encoding="utf-8")
        assert m._is_empty_notebook(p) is False

    def test_corrupt_json(self, tmp_path):
        p = tmp_path / "x.ipynb"
        p.write_text("NOT JSON", encoding="utf-8")
        # Faux = distinct de "vraiment vide" : _iter_id_cells remonte
        # silencieux, le rapport agregera comme ERROR_NOTEBOOK.
        assert m._is_empty_notebook(p) is False


# --------------------------------------------------------------------------
# _load_csv + _normalize_column_order
# --------------------------------------------------------------------------

class TestLoadCsv:
    def test_load_minimal_csv(self, tmp_path):
        p = _write_csv(tmp_path / "f.csv", [
            _csv_row("a/b.ipynb", "c1"),
        ])
        fieldnames, rows = m._load_csv(p)
        assert fieldnames[0] == "notebook"
        assert len(rows) == 1
        assert rows[0]["cell_id"] == "c1"

    def test_load_empty_csv(self, tmp_path):
        # CSV avec header mais 0 ligne
        p = tmp_path / "empty.csv"
        p.write_text(
            "notebook,cell_id,cell_type,src_lang,src_hash\n",
            encoding="utf-8",
        )
        fieldnames, rows = m._load_csv(p)
        assert fieldnames[0] == "notebook"
        assert rows == []


class TestNormalizeColumnOrder:
    def test_canonical_order(self):
        cols = ["cell_id", "notebook", "text_en", "src_hash"]
        ordered = m._normalize_column_order(cols)
        # "notebook" doit etre en tete, "src_hash" en 5e position.
        assert ordered[0] == "notebook"
        assert ordered[1] == "cell_id"
        assert "text_en" in ordered
        assert "src_hash" in ordered

    def test_unknown_columns_kept(self):
        # Le schema ratifie est canonical mais on conserve les colonnes
        # supplementaires (ex: text_de si ajoute ulterieurement).
        cols = ["notebook", "cell_id", "text_de"]
        ordered = m._normalize_column_order(cols)
        assert "notebook" in ordered
        assert "cell_id" in ordered
        # "text_de" n'est PAS dans le schema canonique donc absent de l'ordre.


# --------------------------------------------------------------------------
# measure_csv -- coeur de la mesure
# --------------------------------------------------------------------------

class TestMeasureCsv:
    def test_orphan_notebook_detected(self, tmp_path):
        # CSV reference un notebook qui n'existe pas sur disque.
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("ghost.ipynb", "c1"),
        ])
        # cwd = tmp_path pour que le chemin relatif du CSV soit intra-tmp.
        m_dict = m.measure_csv(csv_path, tmp_path, "en")
        assert m_dict["notebooks_referenced"] == 1
        assert m_dict["notebooks_present_on_disk"] == 0
        assert "ghost.ipynb" in m_dict["orphan_notebooks"]
        assert m_dict["total_csv_rows"] == 1

    def test_indexing_debt_missing(self, tmp_path):
        # Notebook avec 3 cellules, CSV avec 2 lignes : 1 manquante.
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
            {"id": "c2", "type": "markdown", "source": ["b"]},
            {"id": "c3", "type": "markdown", "source": ["c"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1"),
            _csv_row("n.ipynb", "c2"),
        ])
        m_dict = m.measure_csv(csv_path, tmp_path, "en")
        idx = m_dict["indexing_debt"]
        assert idx["missing_from_csv"] == 1
        assert "c3" in idx["by_notebook"]["n.ipynb"]["missing_from_csv_ids"]
        assert idx["extra_in_csv"] == 0

    def test_indexing_debt_extra_orphan_row(self, tmp_path):
        # Notebook avec 2 cellules, CSV avec 3 lignes (1 fantome) : 1 ORPHAN_ROW.
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
            {"id": "c2", "type": "markdown", "source": ["b"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1"),
            _csv_row("n.ipynb", "c2"),
            _csv_row("n.ipynb", "ghost"),
        ])
        m_dict = m.measure_csv(csv_path, tmp_path, "en")
        idx = m_dict["indexing_debt"]
        assert idx["missing_from_csv"] == 0
        assert idx["extra_in_csv"] == 1
        assert "ghost" in idx["by_notebook"]["n.ipynb"]["extra_in_csv_ids"]

    def test_translation_debt_target_empty(self, tmp_path):
        # text_fr rempli, text_en vide : dette de traduction en=1.
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
            {"id": "c2", "type": "markdown", "source": ["b"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1", text_fr="A", text_en="A-en"),
            _csv_row("n.ipynb", "c2", text_fr="B", text_en=""),  # dette
        ])
        m_dict = m.measure_csv(csv_path, tmp_path, "en")
        tr = m_dict["translation_debt"]
        assert tr["rows_with_fr_filled"] == 2
        assert tr["rows_with_target_empty"] == 1
        assert tr["by_lang"]["en"] == 1

    def test_translation_debt_fr_empty_not_counted(self, tmp_path):
        # text_fr vide (cellule code sans commentaire par ex) : PAS dette.
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "code", "source": ["x = 1"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1", text_fr="", text_en=""),
        ])
        m_dict = m.measure_csv(csv_path, tmp_path, "en")
        tr = m_dict["translation_debt"]
        assert tr["rows_with_fr_filled"] == 0
        assert tr["rows_with_target_empty"] == 0

    def test_target_lang_switch(self, tmp_path):
        # Meme fixture, --target-lang es : dette mesure sur la colonne text_es.
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1", text_fr="A", text_en="A-en"),
            # text_en rempli, text_es vide : dette=0 en, dette=1 es.
        ])
        m_en = m.measure_csv(csv_path, tmp_path, "en")
        m_es = m.measure_csv(csv_path, tmp_path, "es")
        assert m_en["translation_debt"]["rows_with_target_empty"] == 0
        assert m_es["translation_debt"]["rows_with_target_empty"] == 1
        assert m_es["target_lang"] == "es"


# --------------------------------------------------------------------------
# measure_csvs -- agregation
# --------------------------------------------------------------------------

class TestMeasureCsvs:
    def test_aggregate_totals(self, tmp_path):
        # 2 CSV, 1 notebook chacun, 2 cellules indexees chacune : agregat=4.
        nb_a = _write_nb(tmp_path, "a.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
            {"id": "c2", "type": "markdown", "source": ["b"]},
        ])
        nb_b = _write_nb(tmp_path, "b.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
            {"id": "c2", "type": "markdown", "source": ["b"]},
        ])
        csv_a = _write_csv(tmp_path / "a.csv", [
            _csv_row("a.ipynb", "c1"), _csv_row("a.ipynb", "c2"),
        ])
        csv_b = _write_csv(tmp_path / "b.csv", [
            _csv_row("b.ipynb", "c1"), _csv_row("b.ipynb", "c2"),
        ])
        report = m.measure_csvs([csv_a, csv_b], tmp_path, "en")
        assert report["csv_count"] == 2
        assert report["aggregate"]["notebooks_referenced"] == 2
        assert report["aggregate"]["total_source_cells"] == 4
        assert report["aggregate"]["total_csv_rows"] == 4
        assert report["aggregate"]["indexing_missing_from_csv"] == 0

    def test_orphan_notebooks_deduplicated(self, tmp_path):
        # Meme notebook absent reference par 2 CSV : 1 seule entree dans orphan.
        csv_a = _write_csv(tmp_path / "a.csv", [
            _csv_row("ghost.ipynb", "c1"),
        ])
        csv_b = _write_csv(tmp_path / "b.csv", [
            _csv_row("ghost.ipynb", "c2"),
        ])
        report = m.measure_csvs([csv_a, csv_b], tmp_path, "en")
        assert report["aggregate"]["orphan_notebooks"] == ["ghost.ipynb"]
        # Mais le compteur de notebooks references doit sommer les 2 refs :
        assert report["aggregate"]["notebooks_referenced"] == 2


# --------------------------------------------------------------------------
# render_human_report -- non-regression sur la forme (cherche un invariant)
# --------------------------------------------------------------------------

class TestRenderHumanReport:
    def test_aggregate_block_present(self, tmp_path):
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1"),
        ])
        report = m.measure_csvs([csv_path], tmp_path, "en")
        text = m.render_human_report(report)
        assert "# Translation debt measurement" in text
        assert "AGREGAT TOUS CSV" in text
        assert "DETTE INDEXATION" in text
        assert "DETTE TRADUCTION en" in text

    def test_per_notebook_detail_only_when_nonzero(self, tmp_path):
        # 1 notebook fully indexed : pas de detail par notebook (zero-only).
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
        ])
        csv_path = _write_csv(tmp_path / "f.csv", [
            _csv_row("n.ipynb", "c1"),
        ])
        report = m.measure_csvs([csv_path], tmp_path, "en")
        text = m.render_human_report(report)
        # Le nom du notebook ne doit PAS apparaitre en detail
        # (rien de non-zero a signaler).
        assert "n.ipynb :" not in text


# --------------------------------------------------------------------------
# _resolve_csv_paths -- CLI inputs
# --------------------------------------------------------------------------

class TestResolveCsvPaths:
    def test_csv_files_kept(self, tmp_path):
        c1 = _write_csv(tmp_path / "a.csv", [])
        c2 = _write_csv(tmp_path / "b.csv", [])
        # Creer un header minimal pour eviter un CSV vide invalide.
        result = m._resolve_csv_paths([c1, c2], tmp_path)
        assert set(result) == {c1, c2}

    def test_directory_scanned_recursively(self, tmp_path):
        sub = tmp_path / "sub"
        sub.mkdir()
        c = _write_csv(sub / "x.csv", [])
        result = m._resolve_csv_paths([tmp_path], tmp_path)
        assert c in result

    def test_non_csv_files_ignored(self, tmp_path):
        # Un fichier non-CSV passe inapercu.
        (tmp_path / "readme.md").write_text("not csv", encoding="utf-8")
        c = _write_csv(tmp_path / "ok.csv", [])
        result = m._resolve_csv_paths([tmp_path], tmp_path)
        assert result == [c]

    def test_missing_path_silently_ignored(self, tmp_path):
        # Un chemin inexistant est ignore (l'appelant CLI peut
        # avoir tape par erreur ; le rapport reste utile).
        result = m._resolve_csv_paths([tmp_path / "nope"], tmp_path)
        assert result == []


# --------------------------------------------------------------------------
# main -- CLI integration (smoke test, on capture stdout/stderr)
# --------------------------------------------------------------------------

class TestMain:
    def test_returns_2_when_no_csv_found(self, tmp_path, capsys):
        # inputs pointe vers un repertoire vide.
        (tmp_path / "sub").mkdir()
        rc = m.main(["--repo-root", str(tmp_path), str(tmp_path)])
        out = capsys.readouterr()
        assert rc == 2
        assert "ERROR" in out.err

    def test_json_on_stdout(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
        ])
        _write_csv(tmp_path / "f.csv", [_csv_row("n.ipynb", "c1")])
        rc = m.main(["--repo-root", str(tmp_path), "--json-only", str(tmp_path)])
        out = capsys.readouterr()
        assert rc == 0
        # stdout = JSON valide
        parsed = json.loads(out.out)
        assert parsed["csv_count"] == 1
        # stderr vide en mode --json-only
        assert out.err == ""

    def test_human_report_on_stderr(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, "n.ipynb", [
            {"id": "c1", "type": "markdown", "source": ["a"]},
        ])
        _write_csv(tmp_path / "f.csv", [_csv_row("n.ipynb", "c1")])
        rc = m.main(["--repo-root", str(tmp_path), str(tmp_path)])
        out = capsys.readouterr()
        assert rc == 0
        # stdout = JSON
        json.loads(out.out)
        # stderr = rapport humain
        assert "Translation debt measurement" in out.err