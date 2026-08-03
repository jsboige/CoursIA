#!/usr/bin/env python3
"""Tests pour scripts/translation/check_translation_sync.py — T2 du pipeline de
synchro traduction (Epic #4957 / #1650). Détecteur NON-BLOQUANT de drift entre
notebooks et le CSV de synchro maintenu par T1 (extract_cells_to_csv.py).

Couvre les 6 verdicts (SRC_DRIFT, TRAD_DRIFT, MISSING_LANG, ORPHAN_ROW,
FR_CONTAM, WRONG_SCRIPT) + les fonctions pures de support (détection de script
Unicode, contamination FR, taux de remplissage avec discipline floor) + main()
exit codes. stdlib-only (csv/hashlib/json/math/pathlib/argparse), hermétique.

Complément du test T1 (test_extract_cells_to_csv.py) : T2 LIT les hashes CSV
produits par T1 → verrouiller les deux verrouille le contrat drift-detection
complet du pipeline (hash byte-identique cross-module, cf docstring T2 L54).
"""

import csv
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_translation_sync as t  # noqa: E402


# --------------------------------------------------------------------------
# Helpers — synthetic notebooks + CSV
# --------------------------------------------------------------------------

def _nb(cells):
    """Construit un notebook minimal. cells = liste de dicts {id,type,source}."""
    return {
        "cells": [
            {"id": c["id"], "cell_type": c["type"], "source": c["source"],
             "metadata": {}, **({"outputs": [], "execution_count": None}
                                if c["type"] == "code" else {})}
            for c in cells
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }


def _write_nb(repo_root, name, cells):
    """Écrit un notebook sous repo_root. cells = [{id,type,source}]."""
    p = repo_root / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(_nb(cells)), encoding="utf-8")
    return p


def _write_csv(path, rows):
    """rows = liste de dicts. Écrit un CSV avec exactement les clés des dicts."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()), quoting=csv.QUOTE_MINIMAL)
        writer.writeheader()
        writer.writerows(rows)
    return path


def _row(cell_id, src_hash, **extra):
    """Ligne CSV minimale. extra = hash_<lang>/text_<lang> optionnels."""
    r = {"notebook": "nb.ipynb", "cell_id": cell_id, "cell_type": "markdown",
         "src_lang": "fr", "src_hash": src_hash, "text_fr": "", "hash_fr": src_hash}
    r.update(extra)
    return r


# --------------------------------------------------------------------------
# normalize / cell_hash — contrat byte-identique avec T1 (anti faux-drift)
# --------------------------------------------------------------------------

def test_cell_hash_16_hex_deterministic():
    h = t.cell_hash("texte")
    assert len(h) == 16
    assert h == t.cell_hash("texte")


def test_cell_hash_insensitive_to_cosmetic_whitespace():
    # normalize rstrip/ligne + strip newline final -> pas de faux drift.
    assert t.cell_hash("ligne   \n") == t.cell_hash("ligne")


def test_cell_hash_contract_identical_to_t1_extract_module():
    """CRITIQUE (#4957) : T2 LIT les hashes écrits par T1. Les deux modules
    DOIVENT produire le même hash pour le même texte, sinon T2 génère des
    faux TRAD_DRIFT/SRC_DRIFT. On verrouille le contrat cross-module."""
    import extract_cells_to_csv as t1  # noqa: E402 (même dir)
    samples = ["bonjour le monde", "# Titre\n\nUn paragraphe.", "code = 1\n",
               "  spaced  \n\n line\t"]
    for s in samples:
        assert t.cell_hash(s) == t1.cell_hash(s), f"hash mismatch on {s!r}"


# --------------------------------------------------------------------------
# _has_expected_script — détection Unicode déterministe (WRONG_SCRIPT)
# --------------------------------------------------------------------------

def test_expected_script_latin_langs_always_true():
    # en/es/pt absents de LANG_SCRIPT_RANGES -> pas de verdict WRONG_SCRIPT.
    assert t._has_expected_script("en", "hello world") is True
    assert t._has_expected_script("es", "bonjour") is True  # FR leaké, mais Latin
    assert t._has_expected_script("pt", "olá mundo") is True


def test_expected_script_empty_text_true():
    # Texte vide = état attendu pre-T3, rien à checker.
    for lang in ["ar", "zh", "ru", "fa"]:
        assert t._has_expected_script(lang, "") is True


def test_expected_script_ascii_only_in_non_latin_is_false():
    # Code/nombres purs (ASCII) dans une colonne ar/zh/ru = WRONG_SCRIPT :
    # une vraie traduction contient AUSSI un caractère du script cible.
    assert t._has_expected_script("ar", "1234567890") is False
    assert t._has_expected_script("zh", "print('hello')") is False


def test_expected_script_fr_leaked_into_non_latin_is_false():
    # FR copier-coller dans la colonne ar/zh/ru (aucun caractère du script).
    assert t._has_expected_script("ar", "bonjour le monde") is False
    assert t._has_expected_script("zh", "bonjour") is False
    assert t._has_expected_script("ru", "bonjour") is False


def test_expected_script_legit_translation_is_true():
    # Vraie traduction : contient des chiffres/code (ASCII) MAIS aussi un
    # caractère du script cible.
    assert t._has_expected_script("ar", "مرحبا 123") is True
    assert t._has_expected_script("zh", "你好 world") is True
    assert t._has_expected_script("ru", "Привет 42") is True


def test_expected_script_persian_uses_arabic_ranges():
    # fa partage les plages Arabic (le persan s'écrit en script arabe).
    assert t._has_expected_script("fa", "سلام") is True


# --------------------------------------------------------------------------
# _is_fr_contam — contamination FR (Argumentum 5-classes, 4e)
# --------------------------------------------------------------------------

def test_fr_contam_identical_long_text_true():
    src = "bonjour le monde entier"
    assert t._is_fr_contam(src, src) is True  # identique, len >= 4


def test_fr_contam_identical_short_text_false():
    # Garde len >= 4 : supprime les correspondances triviales (token unique).
    assert t._is_fr_contam("abc", "abc") is False


def test_fr_contam_different_text_false():
    assert t._is_fr_contam("bonjour le monde", "hello world") is False


def test_fr_contam_normalizes_before_compare():
    # Egalité post-normalisation : whitespace cosmétique ne masque pas la contam.
    assert t._is_fr_contam("bonjour le monde", "bonjour le monde  \n") is True


# --------------------------------------------------------------------------
# load_notebook_cells / load_notebook_cell_texts
# --------------------------------------------------------------------------

def test_load_notebook_cells_returns_hash_map(tmp_path):
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["bonjour"]},
        {"id": "c2", "type": "code", "source": ["print(1)"]},
    ])
    cells = t.load_notebook_cells(p)
    assert set(cells.keys()) == {"c1", "c2"}
    assert cells["c1"] == t.cell_hash("bonjour")


def test_load_notebook_cells_skips_no_id_and_non_md_code(tmp_path):
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["x"]},
        {"id": None, "type": "markdown", "source": ["skip"]},
        {"id": "r1", "type": "raw", "source": ["skip"]},
    ])
    cells = t.load_notebook_cells(p)
    assert list(cells.keys()) == ["c1"]


def test_load_notebook_cells_none_on_unreadable(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not json", encoding="utf-8")
    assert t.load_notebook_cells(p) is None


def test_load_notebook_cells_none_on_missing_file(tmp_path):
    assert t.load_notebook_cells(tmp_path / "ghost.ipynb") is None


def test_load_notebook_cell_texts_returns_raw_text(tmp_path):
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["ligne1\n", "ligne2"]},
    ])
    texts = t.load_notebook_cell_texts(p)
    assert texts["c1"] == "ligne1\nligne2"  # texte brut, non haché


# --------------------------------------------------------------------------
# translated_notebook_path — convention #1650 (xxx_<lang>.ipynb)
# --------------------------------------------------------------------------

def test_translated_notebook_path_appends_lang_suffix():
    p = t.translated_notebook_path("dir/foo.ipynb", "en", Path("/repo"))
    assert p == Path("/repo/dir/foo_en.ipynb")


def test_translated_notebook_path_nested_dir():
    p = t.translated_notebook_path("a/b/c.ipynb", "ar", Path("/repo"))
    assert p == Path("/repo/a/b/c_ar.ipynb")


# --------------------------------------------------------------------------
# check_csv — LE CŒUR : déclenche chaque verdict via fixtures synthétiques
# --------------------------------------------------------------------------

def test_check_csv_in_sync_no_anomaly(tmp_path):
    # src_hash matche le notebook courant ; aucune traduction déposée -> rien.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["bonjour"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", t.cell_hash("bonjour"))])
    assert t.check_csv(csv_path, tmp_path) == []


def test_check_csv_src_drift(tmp_path):
    # Le source a bougé depuis la dernière synchro (csv src_hash périmé).
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["nouveau"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", "stale_hash_00000")])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert len(anomalies) == 1
    assert anomalies[0]["verdict"] == "SRC_DRIFT"


def test_check_csv_orphan_row_cell_absent(tmp_path):
    # cell_id du CSV absent du notebook source (cellule supprimée).
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["x"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("ghost", "abc")])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert [a["verdict"] for a in anomalies] == ["ORPHAN_ROW"]


def test_check_csv_orphan_row_notebook_unreadable(tmp_path):
    # Notebook source illisible -> ORPHAN_ROW (graceful, ne crash pas).
    (tmp_path / "nb.ipynb").write_text("{broken", encoding="utf-8")
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", "abc")])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert anomalies[0]["verdict"] == "ORPHAN_ROW"


def test_check_csv_trad_drift(tmp_path):
    # hash_en déposé, notebook_en existe, mais son hash != csv hash_en.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["fr"]}])
    _write_nb(tmp_path, "nb_en.ipynb", [{"id": "c1", "type": "markdown", "source": ["hello"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("fr"), hash_en="stale_en_hash_0"),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    verdicts = [a["verdict"] for a in anomalies]
    assert "TRAD_DRIFT" in verdicts


def test_check_csv_missing_lang_file_absent(tmp_path):
    # hash_en déposé mais nb_en.ipynb n'existe pas.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["fr"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("fr"), hash_en="some_hash_en_0"),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert [a["verdict"] for a in anomalies] == ["MISSING_LANG"]


def test_check_csv_missing_lang_cell_absent(tmp_path):
    # nb_en.ipynb existe mais n'a pas la cell_id c1.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["fr"]}])
    _write_nb(tmp_path, "nb_en.ipynb", [{"id": "other", "type": "markdown", "source": ["y"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("fr"), hash_en="some_hash_en_0"),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert [a["verdict"] for a in anomalies] == ["MISSING_LANG"]


def test_check_csv_trad_in_sync_when_hash_matches(tmp_path):
    # hash_en déposé ET nb_en hash matche csv hash_en -> pas de TRAD_DRIFT.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["fr"]}])
    _write_nb(tmp_path, "nb_en.ipynb", [{"id": "c1", "type": "markdown", "source": ["hello"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("fr"), hash_en=t.cell_hash("hello")),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert anomalies == []  # traduction cohérente, aucun drift


def test_check_csv_wrong_script(tmp_path):
    # text_ar déposé avec du FR (aucun caractère arabe) -> WRONG_SCRIPT.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["fr"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("fr"), text_ar="bonjour le monde"),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert [a["verdict"] for a in anomalies] == ["WRONG_SCRIPT"]
    assert anomalies[0]["lang"] == "ar"


def test_check_csv_fr_contam(tmp_path):
    # Traduction en IDENTIQUE au source fr (non traduite, len >= 4).
    src = "bonjour le monde"
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": [src]}])
    _write_nb(tmp_path, "nb_en.ipynb", [{"id": "c1", "type": "markdown", "source": [src]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        # hash_en = hash du texte en (= hash fr car identique) -> pas de TRAD_DRIFT.
        _row("c1", t.cell_hash(src), hash_en=t.cell_hash(src)),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert [a["verdict"] for a in anomalies] == ["FR_CONTAM"]


def test_check_csv_real_translation_no_fr_contam(tmp_path):
    # Traduction réelle (différente du fr) -> pas de FR_CONTAM.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["bonjour le monde"]}])
    _write_nb(tmp_path, "nb_en.ipynb", [{"id": "c1", "type": "markdown", "source": ["hello world"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [
        _row("c1", t.cell_hash("bonjour le monde"), hash_en=t.cell_hash("hello world")),
    ])
    anomalies = t.check_csv(csv_path, tmp_path)
    assert anomalies == []  # traduction légitime, in-sync


def test_check_csv_skips_rows_without_notebook_or_cell_id(tmp_path):
    # Lignes mal formées (notebook/cell_id vides) -> ignorées silencieusement.
    csv_path = tmp_path / "sync.csv"
    csv_path.write_text(
        "notebook,cell_id,src_hash\n, ,abc\nnb.ipynb,,abc\n",
        encoding="utf-8",
    )
    assert t.check_csv(csv_path, tmp_path) == []


# --------------------------------------------------------------------------
# csv_fill_stats — taux de remplissage par langue (#6949 point 1)
# --------------------------------------------------------------------------

def test_csv_fill_stats_counts_non_empty_text_columns(tmp_path):
    csv_path = _write_csv(tmp_path / "s.csv", [
        _row("c1", "h", text_fr="fr1", text_en="en1", text_es=""),
        _row("c2", "h", text_fr="fr2", text_en="", text_es="es2"),
    ])
    stats = t.csv_fill_stats(csv_path)
    assert stats["fr"] == {"filled": 2, "total": 2}
    assert stats["en"] == {"filled": 1, "total": 2}
    assert stats["es"] == {"filled": 1, "total": 2}
    # total identique pour toutes les langues (dénominateur commun).
    assert all(s["total"] == 2 for s in stats.values())


def test_csv_fill_stats_strips_whitespace_only(tmp_path):
    # text_<lang> avec espaces seulement -> non compté comme rempli.
    csv_path = _write_csv(tmp_path / "s.csv", [
        _row("c1", "h", text_en="   "),
    ])
    stats = t.csv_fill_stats(csv_path)
    assert stats["en"]["filled"] == 0


def test_csv_fill_stats_excludes_malformed_rows(tmp_path):
    # Lignes sans notebook/cell_id -> hors dénominateur.
    csv_path = tmp_path / "s.csv"
    csv_path.write_text(
        "notebook,cell_id,src_hash,text_fr\nnb,c1,h,fr\n,,h,skip\n",
        encoding="utf-8",
    )
    stats = t.csv_fill_stats(csv_path)
    assert stats["fr"] == {"filled": 1, "total": 1}  # seule la ligne valide


# --------------------------------------------------------------------------
# _fill_pct — discipline floor (jamais arrondi vers le haut, #6949)
# --------------------------------------------------------------------------

def test_fill_pct_floors_never_rounds_up():
    # 24469/24470 = 99.9959% -> floor 99.9, PAS 100.0 (anti fausse complétude).
    assert t._fill_pct(24469, 24470) == 99.9


def test_fill_pct_hundred_only_on_exact_full():
    assert t._fill_pct(10, 10) == 100.0      # exact
    assert t._fill_pct(999, 1000) == 99.9     # floor, pas 100.0


def test_fill_pct_zero_total():
    assert t._fill_pct(5, 0) == 0.0


def test_fill_pct_simple_halves():
    assert t._fill_pct(1, 2) == 50.0
    assert t._fill_pct(0, 4) == 0.0
    assert t._fill_pct(1, 3) == 33.3   # 33.333 -> floor 33.3


# --------------------------------------------------------------------------
# _format_fill_line — signal honnête stderr
# --------------------------------------------------------------------------

def test_format_fill_line_includes_all_target_langs():
    stats = {lang: {"filled": 0, "total": 10} for lang in t.ALL_LANGS}
    line = t._format_fill_line(stats)
    for lang in t.TARGET_LANGS:
        assert f"{lang}=0.0%" in line
    assert "10 cellules" in line


def test_format_fill_line_none_suffix_when_all_targets_zero():
    stats = {lang: {"filled": 0, "total": 5} for lang in t.ALL_LANGS}
    line = t._format_fill_line(stats)
    assert "AUCUNE traduction déposée" in line


def test_format_fill_line_no_suffix_when_some_filled():
    stats = {lang: {"filled": 0, "total": 5} for lang in t.ALL_LANGS}
    stats["en"] = {"filled": 1, "total": 5}
    line = t._format_fill_line(stats)
    assert "AUCUNE" not in line


# --------------------------------------------------------------------------
# iter_csvs
# --------------------------------------------------------------------------

def test_iter_csvs_file_returns_singleton(tmp_path):
    p = tmp_path / "a.csv"
    p.write_text("x\n", encoding="utf-8")
    assert t.iter_csvs(p) == [p]


def test_iter_csvs_dir_recursive_sorted(tmp_path):
    (tmp_path / "b.csv").write_text("x\n", encoding="utf-8")
    sub = tmp_path / "sub"
    sub.mkdir()
    (sub / "a.csv").write_text("x\n", encoding="utf-8")
    out = t.iter_csvs(tmp_path)
    # tri déterministe par chemin complet (Path), récursif (rglob descend sub/).
    assert out == sorted(out)
    assert {p.name for p in out} == {"a.csv", "b.csv"}


# --------------------------------------------------------------------------
# main() — exit codes (2 missing, 0 no-csv/in-sync/--check, 1 drift)
# --------------------------------------------------------------------------

def test_main_missing_input_returns_2(tmp_path, monkeypatch):
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(tmp_path / "ghost.csv"),
    ])
    assert t.main() == 2


def test_main_empty_dir_returns_0(tmp_path, monkeypatch, capsys):
    # Aucun CSV sous le dir = phase pre-T1, CI verte.
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(tmp_path), "--repo-root", str(tmp_path),
    ])
    rc = t.main()
    assert rc == 0
    out = capsys.readouterr().out
    report = json.loads(out)
    assert report["csvs_checked"] == 0


def test_main_in_sync_returns_0(tmp_path, monkeypatch):
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["bonjour"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", t.cell_hash("bonjour"))])
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(csv_path), "--repo-root", str(tmp_path),
    ])
    assert t.main() == 0


def test_main_drift_returns_1(tmp_path, monkeypatch):
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["nouveau"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", "stale_hash_00000")])
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(csv_path), "--repo-root", str(tmp_path),
    ])
    assert t.main() == 1


def test_main_drift_with_check_returns_0(tmp_path, monkeypatch):
    # --check = mode CI non-bloquant : exit 0 même si drift.
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["nouveau"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", "stale_hash_00000")])
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(csv_path), "--repo-root", str(tmp_path), "--check",
    ])
    assert t.main() == 0


def test_main_emits_json_stdout_with_anomalies(tmp_path, monkeypatch, capsys):
    _write_nb(tmp_path, "nb.ipynb", [{"id": "c1", "type": "markdown", "source": ["nouveau"]}])
    csv_path = _write_csv(tmp_path / "sync.csv", [_row("c1", "stale_hash_00000")])
    monkeypatch.setattr(sys, "argv", [
        "check_translation_sync.py", str(csv_path), "--repo-root", str(tmp_path), "--check",
    ])
    t.main()
    report = json.loads(capsys.readouterr().out)
    assert report["anomaly_count"] == 1
    assert report["anomalies"][0]["verdict"] == "SRC_DRIFT"
    assert "fill_rate" in report  # signal de remplissage présent (#6949)
