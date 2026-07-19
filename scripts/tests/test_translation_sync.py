"""Tests for the translation sync scripts (Epic #4957 / #1650).

Covers the two scripts that maintain the translation sync CSV:

  - ``scripts/translation/extract_cells_to_csv.py`` (T1) : extracts notebook
    cells into the CSV pivot (langue pivot ``fr``).
  - ``scripts/translation/check_translation_sync.py`` (T2) : detects drift
    between the notebooks and the CSV (non-bloquant, CI).

Avant ce fichier, ces deux scripts etaient **orphelins de test** (la veine
translation est une jambe durable de po-2023, cf
``translation-drift-resync-durable-vein``). Ce fichier pose le garde-fou
anti-regression sur le **contrat de hash partage T1<->T2** (``normalize`` +
``cell_hash`` doivent etre byte-identiques entre les deux modules — un drift
silencieux entre les deux casserait toute la detection de drift) et sur la
logique de detection (SRC_DRIFT / TRAD_DRIFT / MISSING_LANG / ORPHAN_ROW).

Les tests construisent des notebooks + CSV synthetiques dans ``tmp_path``
(aucune dependance a un vrai notebook du depot). CPU-only, stdlib + pytest.

Run with: pytest scripts/tests/test_translation_sync.py -v
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import pytest

# Les modules sous test vivent dans scripts/translation/ ; ce test dans
# scripts/tests/. On ajoute scripts/translation/ au path.
_TRANSLATION_DIR = Path(__file__).resolve().parent.parent / "translation"
sys.path.insert(0, str(_TRANSLATION_DIR))

import check_translation_sync as t2  # noqa: E402
import extract_cells_to_csv as t1  # noqa: E402


# --------------------------------------------------------------------------- #
#  Helpers : notebooks + CSV synthetiques                                      #
# --------------------------------------------------------------------------- #


def _make_cell(cell_id: str, cell_type: str, source: str | list[str]) -> dict:
    """Construit une cellule nbformat avec id stable."""
    src = source if isinstance(source, list) else [source]
    return {"cell_type": cell_type, "id": cell_id, "source": src,
            "metadata": {}, "execution_count": None, "outputs": []}


def _write_notebook(path: Path, cells: list[dict]) -> Path:
    """Ecrit un notebook .ipynb minimal (nbformat 4) avec les cellules donnees."""
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"display_name": "Python 3", "language": "python", "name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _write_csv(path: Path, rows: list[dict]) -> Path:
    """Ecrit un CSV de synchro avec le schema COLUMNS de T1."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=t1.COLUMNS)
        writer.writeheader()
        for r in rows:
            # Toutes les colonnes absentes -> vide (schema complet).
            full = {col: r.get(col, "") for col in t1.COLUMNS}
            writer.writerow(full)
    return path


# --------------------------------------------------------------------------- #
#  normalize + cell_hash (contrat partage T1 <-> T2)                           #
# --------------------------------------------------------------------------- #


def test_normalize_strips_trailing_whitespace_per_line():
    """rstrip par ligne : un espace en fin de ligne ne change pas le hash."""
    base = "ligne un\nligne deux"
    padded = "ligne un \nligne deux "
    assert t1.normalize(base) == t1.normalize(padded)
    assert t2.normalize(base) == t2.normalize(padded)


def test_normalize_strips_leading_trailing_blank_lines():
    """Les lignes vides de tete/queue sont eliminees (anti faux-drift)."""
    base = "contenu"
    padded = "\n\ncontenu\n\n"
    assert t1.normalize(padded) == base
    assert t2.normalize(padded) == base


def test_normalize_empty_string():
    """normalize('') == '' (pas de crash sur cellule vide)."""
    assert t1.normalize("") == ""
    assert t2.normalize("") == ""


def test_cell_hash_is_16_hex_chars():
    """Le hash est tronque a 16 hex (64 bits, birthday bound ~4e9 cellules)."""
    h = t1.cell_hash("n'importe quel texte")
    assert len(h) == 16
    assert all(c in "0123456789abcdef" for c in h)


def test_cell_hash_deterministic():
    """Meme texte -> meme hash (sur re-run, T1 est byte-identique)."""
    text = "print('hello')\n# commentaire"
    assert t1.cell_hash(text) == t1.cell_hash(text)
    assert t2.cell_hash(text) == t2.cell_hash(text)


def test_cell_hash_distinct_for_distinct_text():
    """Deux textes differents -> deux hash differents."""
    assert t1.cell_hash("aaa") != t1.cell_hash("bbb")


@pytest.mark.parametrize("text", [
    "simple",
    "ligne1\nligne2\nligne3",
    "  indentation\n    plus profonde  ",
    "accentué et emoji 🎯",
    "",
])
def test_hash_agreement_t1_t2(text):
    """CONTRAT CRITIQUE : T1 et T2 doivent produire le meme hash (byte-identique).

    Le commentaire de check_translation_sync.py l'explicite : normalize/cell_hash
    "doivent rester coherents avec extract_cells_to_csv.py". Un drift silencieux
    entre les deux modules casserait toute la detection de drift (SRC_DRIFT
    comparerait des hash calcules avec deux normalisations differentes).
    """
    assert t1.normalize(text) == t2.normalize(text), (
        f"normalize drift entre T1 et T2 sur {text!r}"
    )
    assert t1.cell_hash(text) == t2.cell_hash(text), (
        f"cell_hash drift entre T1 et T2 sur {text!r}"
    )


# --------------------------------------------------------------------------- #
#  extract_notebook (T1)                                                       #
# --------------------------------------------------------------------------- #


def test_extract_notebook_skips_cells_without_id(tmp_path):
    """Les cellules sans id nbformat stable sont sautees (non traduisibles fiablement)."""
    repo = tmp_path
    nb = _write_notebook(repo / "series" / "Foo.ipynb", [
        _make_cell("cell-1", "markdown", "# Titre"),
        {"cell_type": "markdown", "source": ["pas d'id"], "metadata": {}},  # pas d'id
        _make_cell("cell-2", "code", "print(1)"),
    ])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    ids = [r["cell_id"] for r in rows]
    assert ids == ["cell-1", "cell-2"]


def test_extract_notebook_only_markdown_and_code(tmp_path):
    """raw_cell (et autres types) sont exclus : markdown + code uniquement."""
    repo = tmp_path
    nb = _write_notebook(repo / "Foo.ipynb", [
        _make_cell("c-md", "markdown", "texte"),
        _make_cell("c-code", "code", "1+1"),
        {**_make_cell("c-raw", "raw", "raw"), "cell_type": "raw"},
    ])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    types = {r["cell_id"]: r["cell_type"] for r in rows}
    assert types == {"c-md": "markdown", "c-code": "code"}


def test_extract_notebook_src_hash_matches_cell_hash(tmp_path):
    """src_hash d'une ligne == cell_hash(texte de la cellule)."""
    repo = tmp_path
    text = "print('hello')"
    nb = _write_notebook(repo / "Foo.ipynb", [_make_cell("c1", "code", text)])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    assert rows[0]["src_hash"] == t1.cell_hash(text)


def test_extract_notebook_pivot_hash_equals_src_hash(tmp_path):
    """A l'extraction T1, hash_{src_lang} == src_hash (le pivot EST la source)."""
    repo = tmp_path
    nb = _write_notebook(repo / "Foo.ipynb", [_make_cell("c1", "markdown", "# X")])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    assert rows[0]["hash_fr"] == rows[0]["src_hash"]
    assert rows[0]["text_fr"] == "# X"


def test_extract_notebook_relative_path_posix(tmp_path):
    """notebook est le chemin relatif au repo en format POSIX (cross-platform)."""
    repo = tmp_path
    nb = _write_notebook(repo / "Search" / "Part1" / "Foo.ipynb", [
        _make_cell("c1", "markdown", "x")
    ])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    assert rows[0]["notebook"] == "Search/Part1/Foo.ipynb"


def test_extract_notebook_empty_cells_included(tmp_path):
    """Une cellule avec id mais texte vide est incluse (son texte peut etre traduit)."""
    repo = tmp_path
    nb = _write_notebook(repo / "Foo.ipynb", [_make_cell("c1", "markdown", "")])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    assert len(rows) == 1
    assert rows[0]["src_hash"] == t1.cell_hash("")


# --------------------------------------------------------------------------- #
#  translated_notebook_path (T2)                                               #
# --------------------------------------------------------------------------- #


def test_translated_notebook_path_convention(tmp_path):
    """dir/foo.ipynb + 'en' -> dir/foo_en.ipynb (convention notebooks #1650)."""
    p = t2.translated_notebook_path("Series/Foo.ipynb", "en", tmp_path)
    assert p == tmp_path / "Series" / "Foo_en.ipynb"


def test_translated_notebook_path_each_lang(tmp_path):
    """La convention s'applique a toutes les langues cibles."""
    for lang in t2.TARGET_LANGS:
        p = t2.translated_notebook_path("S/F.ipynb", lang, tmp_path)
        assert p.name == f"F_{lang}.ipynb"


# --------------------------------------------------------------------------- #
#  load_notebook_cells (T2)                                                    #
# --------------------------------------------------------------------------- #


def test_load_notebook_cells_returns_id_to_hash(tmp_path):
    """Retourne {cell_id: hash} pour les cellules markdown/code avec id."""
    repo = tmp_path
    nb = _write_notebook(repo / "Foo.ipynb", [
        _make_cell("c1", "markdown", "# Titre"),
        _make_cell("c2", "code", "print(1)"),
    ])
    cells = t2.load_notebook_cells(nb)
    assert cells == {"c1": t2.cell_hash("# Titre"), "c2": t2.cell_hash("print(1)")}


def test_load_notebook_cells_unreadable_returns_none(tmp_path):
    """Un notebook illisible (JSON casse) retourne None (pas une exception)."""
    bad = tmp_path / "Broken.ipynb"
    bad.write_text("{ ce n'est pas du json valide", encoding="utf-8")
    assert t2.load_notebook_cells(bad) is None


def test_load_notebook_cells_missing_file_returns_none(tmp_path):
    """Un chemin inexistant retourne None (pas une exception)."""
    assert t2.load_notebook_cells(tmp_path / "Absent.ipynb") is None


# --------------------------------------------------------------------------- #
#  check_csv (T2) — detection de drift                                         #
# --------------------------------------------------------------------------- #


def _row(notebook: str, cell_id: str, src_hash: str, **lang_hashes) -> dict:
    """Construit une ligne CSV avec src_hash + hashes de langues optionnels."""
    r = {"notebook": notebook, "cell_id": cell_id, "src_hash": src_hash}
    r.update(lang_hashes)
    return r


def test_check_csv_in_sync_no_anomaly(tmp_path):
    """src_hash CSV == hash actuel -> aucune anomalie (IN_SYNC)."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "bonjour")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("bonjour"))
    ])
    assert t2.check_csv(csv, repo) == []


def test_check_csv_src_drift_detected(tmp_path):
    """Le source a bouge : csv src_hash != hash actuel -> SRC_DRIFT."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "nouveau")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("ancien"))  # different du courant
    ])
    anomalies = t2.check_csv(csv, repo)
    assert len(anomalies) == 1
    assert anomalies[0]["verdict"] == "SRC_DRIFT"
    assert anomalies[0]["cell_id"] == "c1"


def test_check_csv_orphan_row_cell_deleted(tmp_path):
    """Le cell_id CSV n'existe plus dans le source -> ORPHAN_ROW."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "x")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "cell-supprimee", t2.cell_hash("x"))
    ])
    anomalies = t2.check_csv(csv, repo)
    assert len(anomalies) == 1
    assert anomalies[0]["verdict"] == "ORPHAN_ROW"


def test_check_csv_orphan_row_notebook_unreadable(tmp_path):
    """Le notebook source est illisible -> ORPHAN_ROW (detail 'illisible')."""
    repo = tmp_path
    (repo / "S").mkdir(parents=True)
    (repo / "S" / "Foo.ipynb").write_text("{ invalide", encoding="utf-8")
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("x"))
    ])
    anomalies = t2.check_csv(csv, repo)
    assert len(anomalies) == 1
    assert anomalies[0]["verdict"] == "ORPHAN_ROW"


def test_check_csv_missing_lang_translation_file_absent(tmp_path):
    """Un hash_<lang> est depose mais le fichier traduit n'existe pas -> MISSING_LANG."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "bonjour")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("bonjour"),
             **{"hash_en": t2.cell_hash("hello")})  # trad deposee mais fichier absent
    ])
    anomalies = t2.check_csv(csv, repo)
    # SRC est in sync ; seule l'anomalie MISSING_LANG sur 'en' est remontee.
    verdicts = [a["verdict"] for a in anomalies]
    assert "MISSING_LANG" in verdicts
    miss = next(a for a in anomalies if a["verdict"] == "MISSING_LANG")
    assert miss["lang"] == "en"


def test_check_csv_trad_drift_translation_edited(tmp_path):
    """Le fichier traduit existe mais son hash != hash CSV -> TRAD_DRIFT."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "bonjour")])
    # Fichier traduit EN present, avec un texte dont le hash != celui depose.
    _write_notebook(repo / "S" / "Foo_en.ipynb", [_make_cell("c1", "markdown", "hello-edited")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("bonjour"),
             **{"hash_en": t2.cell_hash("hello-original")})  # different du courant EN
    ])
    anomalies = t2.check_csv(csv, repo)
    verdicts = [a["verdict"] for a in anomalies]
    assert "TRAD_DRIFT" in verdicts


def test_check_csv_trad_in_sync_no_anomaly(tmp_path):
    """Le fichier traduit existe ET son hash == hash CSV -> pas de TRAD_DRIFT."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "bonjour")])
    _write_notebook(repo / "S" / "Foo_en.ipynb", [_make_cell("c1", "markdown", "hello")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("bonjour"),
             **{"hash_en": t2.cell_hash("hello")})  # match le fichier EN courant
    ])
    anomalies = t2.check_csv(csv, repo)
    assert anomalies == []


def test_check_csv_skips_empty_lang_hash(tmp_path):
    """Pas de hash_<lang> depose (pre-T3) -> pas d'anomalie (etat attendu)."""
    repo = tmp_path
    _write_notebook(repo / "S" / "Foo.ipynb", [_make_cell("c1", "markdown", "x")])
    csv = _write_csv(tmp_path / "drift.csv", [
        _row("S/Foo.ipynb", "c1", t2.cell_hash("x"))  # aucune trad deposee
    ])
    assert t2.check_csv(csv, repo) == []


# --------------------------------------------------------------------------- #
#  iter_csvs (T2)                                                              #
# --------------------------------------------------------------------------- #


def test_iter_csvs_single_file(tmp_path):
    """Un fichier -> [ce fichier]."""
    f = tmp_path / "a.csv"
    f.write_text("x", encoding="utf-8")
    assert t2.iter_csvs(f) == [f]


def test_iter_csvs_directory_sorted(tmp_path):
    """Un repertoire -> tous les .csv tries (rglob)."""
    (tmp_path / "b.csv").write_text("x", encoding="utf-8")
    (tmp_path / "a.csv").write_text("x", encoding="utf-8")
    (tmp_path / "not_csv.txt").write_text("x", encoding="utf-8")
    sub = tmp_path / "sub"
    sub.mkdir()
    (sub / "c.csv").write_text("x", encoding="utf-8")
    result = t2.iter_csvs(tmp_path)
    names = [p.name for p in result]
    assert names == sorted(names)  # trie
    assert "not_csv.txt" not in names
    assert set(names) == {"a.csv", "b.csv", "c.csv"}


# --------------------------------------------------------------------------- #
#  Roundtrip determinisme (T1 write -> T2 check) — anti-regression global      #
# --------------------------------------------------------------------------- #


def test_roundtrip_extract_then_check_in_sync(tmp_path):
    """Extraire (T1) un notebook vers un CSV puis verifier (T2) -> IN_SYNC.

    C'est l'invariant fondamental de la veine translation : un CSV fraichement
    extrait par T1 ne doit produire AUCUN drift quand T2 le verifie contre le
    meme notebook source (les deux modules partagent normalize/cell_hash).
    """
    repo = tmp_path
    nb = _write_notebook(repo / "S" / "Foo.ipynb", [
        _make_cell("c1", "markdown", "# Titre"),
        _make_cell("c2", "code", "print('bonjour')"),
        _make_cell("c3", "markdown", "Texte avec accents : éàü 🎯"),
    ])
    rows = t1.extract_notebook(nb, repo, src_lang="fr")
    csv = _write_csv(tmp_path / "drift.csv", rows)
    # T2 doit trouver 0 anomalie sur ce CSV fraichement extrait de T1.
    assert t2.check_csv(csv, repo) == []
