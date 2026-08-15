#!/usr/bin/env python3
"""Tests pour scripts/translation/extract_cells_to_csv.py — T1 du pipeline de
synchro traduction (Epic #4957 / #1650). Extrait les cellules notebook vers un
CSV langue-pivot avec hashes bidirectionnels (drift-detection).

Couvre les 8 fonctions pures (stdlib only, hermétiques) : normalize, cell_hash,
extract_notebook, iter_notebooks, load_existing_csv, update_existing_csv,
write_csv, main. Aucune dépendance externe (csv/hashlib/io/json/pathlib stdlib).

main() utilise argparse sur sys.argv -> patch via monkeypatch.
"""

import csv
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import extract_cells_to_csv as e  # noqa: E402


# --------------------------------------------------------------------------
# Helpers — synthetic notebooks + CSV
# --------------------------------------------------------------------------

def _nb(cells, **meta):
    """Construit un notebook minimal. cells = liste de dicts {id,type,source}.

    Chaque dict de cellule peut optionnellement porter ``meta`` (dict) qui sera
    pose sur ``cell.metadata`` — utile pour tester la lecture de
    ``cell.metadata.translate`` (#10326).
    """
    return {
        "cells": [
            {"id": c["id"], "cell_type": c["type"], "source": c["source"],
             "metadata": dict(c.get("meta", {})),
             **({"outputs": [], "execution_count": None}
                if c["type"] == "code" else {})}
            for c in cells
        ],
        "metadata": meta,
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write_nb(tmp_path, name, cells, **meta):
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells, **meta)), encoding="utf-8")
    return p


# --------------------------------------------------------------------------
# normalize — strip trailing whitespace per line, strip leading/trailing newlines
# --------------------------------------------------------------------------

def test_normalize_strips_trailing_whitespace_per_line():
    assert e.normalize("ligne1   \nligne2\t\n") == "ligne1\nligne2"


def test_normalize_strips_leading_trailing_empty_lines():
    assert e.normalize("\n\n\ntexte\n\n") == "texte"


def test_normalize_preserves_internal_blank_lines():
    # Les lignes vides internes sont préservées (pas collapsées).
    assert e.normalize("a\n\nb") == "a\n\nb"


def test_normalize_idempotent():
    s = "  a  \n\n b\t"
    once = e.normalize(s)
    assert e.normalize(once) == once


# --------------------------------------------------------------------------
# cell_hash — sha256[:16], déterministe, insensible au whitespace cosmétique
# --------------------------------------------------------------------------

def test_cell_hash_is_16_hex_chars():
    h = e.cell_hash("texte")
    assert len(h) == 16
    int(h, 16)  # hex valide


def test_cell_hash_deterministic():
    assert e.cell_hash("abc") == e.cell_hash("abc")


def test_cell_hash_insensitive_to_trailing_whitespace():
    # Via normalize : "a " et "a" donnent le même hash (pas de faux drift).
    assert e.cell_hash("texte   ") == e.cell_hash("texte")


def test_cell_hash_differs_on_semantic_change():
    assert e.cell_hash("texte A") != e.cell_hash("texte B")


# --------------------------------------------------------------------------
# extract_notebook — skip no-id, skip non-md/code, pivot columns filled
# --------------------------------------------------------------------------

def test_extract_notebook_skips_cells_without_id(tmp_path):
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["# Titre"]},
        {"id": None, "type": "markdown", "source": ["pas d'id"]},
        {"id": "c3", "type": "code", "source": ["print(1)"]},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    ids = [r["cell_id"] for r in rows]
    assert ids == ["c1", "c3"]  # la cellule sans id est skipée


def test_extract_notebook_skips_non_markdown_code_types(tmp_path):
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["md"]},
        {"id": "c2", "type": "raw", "source": ["raw"]},  # raw -> skippé
        {"id": "c3", "type": "code", "source": ["code"]},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    assert [r["cell_type"] for r in rows] == ["markdown", "code"]


def test_extract_notebook_relative_path_posix(tmp_path):
    sub = tmp_path / "SymbolicAI"
    sub.mkdir()
    p = _write_nb(sub, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["x"]},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    # Chemin relatif POSIX (forward slashes) quelle que soit la plateforme.
    assert rows[0]["notebook"] == "SymbolicAI/nb.ipynb"


def test_extract_notebook_pivot_hash_equals_src_hash(tmp_path):
    """Intentionnel (cf docstring) : hash_{src_lang} == src_hash à l'extraction."""
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["bonjour"]},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    r = rows[0]
    assert r["hash_fr"] == r["src_hash"]
    assert r["text_fr"] == "bonjour"
    assert r["src_lang"] == "fr"


def test_extract_notebook_malformed_json_returns_empty(tmp_path, capsys):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not valid json", encoding="utf-8")
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    assert rows == []
    captured = capsys.readouterr()
    assert "ignoré" in captured.err or "ignore" in captured.err.lower()


# --------------------------------------------------------------------------
# iter_notebooks — file/dir, dedup, exclude _output/_agent, warn on missing
# --------------------------------------------------------------------------

def test_iter_notebooks_file_and_dir(tmp_path, capsys):
    p1 = _write_nb(tmp_path, "a.ipynb", [{"id": "c", "type": "markdown", "source": ["x"]}])
    sub = tmp_path / "sub"
    sub.mkdir()
    p2 = _write_nb(sub, "b.ipynb", [{"id": "c", "type": "markdown", "source": ["y"]}])
    out = e.iter_notebooks([p1, sub])
    assert p1 in out and p2 in out


def test_iter_notebooks_excludes_output_and_agent(tmp_path):
    _write_nb(tmp_path, "ok.ipynb", [{"id": "c", "type": "markdown", "source": ["x"]}])
    _write_nb(tmp_path, "paper_output.ipynb", [{"id": "c", "type": "markdown", "source": ["x"]}])
    _write_nb(tmp_path, "gen_agent.ipynb", [{"id": "c", "type": "markdown", "source": ["x"]}])
    out = e.iter_notebooks([tmp_path])
    names = {p.name for p in out}
    assert "ok.ipynb" in names
    assert "paper_output.ipynb" not in names
    assert "gen_agent.ipynb" not in names


def test_iter_notebooks_dedups_overlapping_inputs(tmp_path):
    p = _write_nb(tmp_path, "a.ipynb", [{"id": "c", "type": "markdown", "source": ["x"]}])
    # Même notebook passé deux fois + le dir qui le contient -> 1 seule fois.
    out = e.iter_notebooks([p, p, tmp_path])
    assert out.count(p) == 1


def test_iter_notebooks_warns_on_missing_path(tmp_path, capsys):
    missing = tmp_path / "nexiste.pas"
    out = e.iter_notebooks([missing])
    assert out == []
    assert "introuvable" in capsys.readouterr().err.lower()


# --------------------------------------------------------------------------
# load_existing_csv — setdefault colonnes manquantes (compat ancien CSV)
# --------------------------------------------------------------------------

def test_load_existing_csv_preserves_filled_columns(tmp_path):
    p = tmp_path / "ex.csv"
    # CSV avec colonnes cibles T3 déjà remplies (text_en, hash_en).
    p.write_text(
        "notebook,cell_id,cell_type,src_lang,src_hash,text_fr,hash_fr,text_en,hash_en\n"
        "nb.ipynb,c1,markdown,fr,abc,texte fr,abc,text en,def\n",
        encoding="utf-8",
    )
    rows = e.load_existing_csv(p)
    assert len(rows) == 1
    assert rows[0]["text_en"] == "text en"
    assert rows[0]["hash_en"] == "def"


def test_load_existing_csv_setdefaults_missing_columns(tmp_path):
    p = tmp_path / "old.csv"
    # Ancien CSV sans toutes les colonnes du schéma ratifié.
    p.write_text("notebook,cell_id,cell_type,src_lang,src_hash\nnb.ipynb,c1,markdown,fr,abc\n",
                 encoding="utf-8")
    rows = e.load_existing_csv(p)
    # Les colonnes manquantes sont remplies avec "" (compatible DictWriter).
    assert rows[0]["text_fr"] == ""
    assert rows[0]["text_en"] == ""
    assert "hash_pt" in rows[0]  # toutes les langues cibles présentes


# --------------------------------------------------------------------------
# update_existing_csv — PRÉ-update stats, preserve T3 cols, append, orphan
# --------------------------------------------------------------------------

def _row(nb, cid, src_hash="abc", text_fr="texte", cell_type="markdown", **extra):
    r = {col: "" for col in e.COLUMNS}
    r.update(notebook=nb, cell_id=cid, cell_type=cell_type, src_lang="fr",
             src_hash=src_hash, text_fr=text_fr, hash_fr=src_hash)
    r.update(extra)
    return r


def test_update_existing_csv_preserves_t3_columns_on_pivot_change():
    """Si src_hash change, on update les colonnes pivot MAIS préserve text_en/hash_en."""
    existing = [_row("nb.ipynb", "c1", src_hash="OLD", text_en="trad en", hash_en="hash_en_old")]
    fresh = [_row("nb.ipynb", "c1", src_hash="NEW")]
    updated, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 1
    r = updated[0]
    assert r["src_hash"] == "NEW"  # pivot rafraîchi
    assert r["hash_fr"] == "NEW"
    assert r["text_en"] == "trad en"  # colonne T3 PRÉSERVÉE
    assert r["hash_en"] == "hash_en_old"  # colonne T3 PRÉSERVÉE


def test_update_existing_csv_unchanged_when_already_in_sync():
    existing = [_row("nb.ipynb", "c1", src_hash="abc", text_fr="t", cell_type="markdown")]
    fresh = [_row("nb.ipynb", "c1", src_hash="abc", text_fr="t", cell_type="markdown")]
    _, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 0
    assert stats["unchanged"] == 1


def test_update_existing_csv_appends_new_cells():
    existing = [_row("nb.ipynb", "c1")]
    fresh = [_row("nb.ipynb", "c1"), _row("nb.ipynb", "c2", src_hash="xyz")]
    updated, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["appended"] == 1
    assert len(updated) == 2
    assert updated[1]["cell_id"] == "c2"


def test_update_existing_csv_preserves_other_notebooks_verbatim():
    """Les lignes d'autres notebooks (hors cible) sont conservées verbatim."""
    existing = [
        _row("nb.ipynb", "c1", src_hash="abc"),
        _row("other.ipynb", "x1", src_hash="keep_me", text_en="trad"),
    ]
    fresh = [_row("nb.ipynb", "c1", src_hash="CHANGED")]
    updated, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["kept_other"] == 1
    other = [r for r in updated if r["notebook"] == "other.ipynb"][0]
    assert other["src_hash"] == "keep_me"  # non touché
    assert other["text_en"] == "trad"


def test_update_existing_csv_keeps_orphan_rows():
    """Cellule supprimée du notebook -> ligne orpheline conservée (pas détruite)."""
    existing = [
        _row("nb.ipynb", "c1", src_hash="abc"),
        _row("nb.ipynb", "deleted", src_hash="old"),  # plus dans fresh
    ]
    fresh = [_row("nb.ipynb", "c1", src_hash="abc")]
    _, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["kept_orphan"] == 1


def test_update_existing_csv_stats_are_pre_update():
    """Les compteurs updated/unchanged reflètent l'état AVANT mutation (actionnable)."""
    existing = [_row("nb.ipynb", "c1", src_hash="OLD")]
    fresh = [_row("nb.ipynb", "c1", src_hash="NEW")]
    # Après update, existing est muté. Les stats doivent quand même dire updated=1.
    updated, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 1  # pré-update, pas post-update (0)


def test_update_existing_csv_mutates_existing_in_place():
    """La fonction mute la liste existing_rows en place et la retourne."""
    existing = [_row("nb.ipynb", "c1", src_hash="OLD")]
    fresh = [_row("nb.ipynb", "c1", src_hash="NEW")]
    returned, _ = e.update_existing_csv(existing, fresh, {"nb.ipynb"})
    assert returned is existing  # même objet (mutation in-place)


# --------------------------------------------------------------------------
# write_csv — LF-only, header, QUOTE_MINIMAL
# --------------------------------------------------------------------------

def test_write_csv_to_file_is_lf_only(tmp_path):
    rows = [_row("nb.ipynb", "c1", text_fr="ligne1\nligne2")]
    out = tmp_path / "out.csv"
    e.write_csv(rows, out)
    raw = out.read_bytes()
    assert b"\r" not in raw  # LF-only strict (pas de \r\n)


def test_write_csv_header_and_quoting(tmp_path):
    rows = [_row("nb.ipynb", "c1", text_fr="avec, virgule")]
    out = tmp_path / "out.csv"
    e.write_csv(rows, out)
    with out.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        hdr = reader.fieldnames
        data = list(reader)
    assert hdr == e.COLUMNS
    assert data[0]["text_fr"] == "avec, virgule"  # quoting préserve la virgule


def test_write_csv_creates_parent_dirs(tmp_path):
    rows = [_row("nb.ipynb", "c1")]
    out = tmp_path / "subdir" / "nested" / "out.csv"
    e.write_csv(rows, out)
    assert out.exists()


def test_write_csv_stdout(capsys):
    rows = [_row("nb.ipynb", "c1", text_fr="x")]
    sink = e.write_csv(rows, None)
    assert sink == "stdout"
    captured = capsys.readouterr()
    assert "notebook" in captured.out  # header écrit sur stdout
    assert "nb.ipynb" in captured.out


# --------------------------------------------------------------------------
# _read_translate_policy + colonne translate_policy (#10326 tranche 2)
# --------------------------------------------------------------------------

def test_read_translate_policy_verbatim():
    """cell.metadata.translate = "verbatim" -> lu verbatim."""
    cell = {"metadata": {"translate": "verbatim"}}
    assert e._read_translate_policy(cell) == "verbatim"


def test_read_translate_policy_missing_defaults_empty():
    """Pas de clé metadata.translate -> chaîne vide (default = traduire)."""
    assert e._read_translate_policy({"metadata": {}}) == ""
    assert e._read_translate_policy({}) == ""  # pas de metadata du tout


def test_read_translate_policy_non_string_defaults_empty():
    """Valeur non-string (None, int, list, dict) -> chaîne vide (defensive)."""
    for bad in (None, 0, 1, ["verbatim"], {"k": "v"}, True):
        assert e._read_translate_policy({"metadata": {"translate": bad}}) == ""


def test_read_translate_policy_strips_whitespace():
    """Whitespace autour de "verbatim" -> strippé."""
    assert e._read_translate_policy({"metadata": {"translate": "  verbatim  "}}) == "verbatim"


def test_extract_metadata_translate_verbatim_propagates_to_csv(tmp_path):
    """Une cellule avec metadata.translate="verbatim" -> row translate_policy=verbatim."""
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["une citation Hugo"],
         "meta": {"translate": "verbatim"}},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    assert rows[0]["translate_policy"] == "verbatim"


def test_extract_no_metadata_translate_defaults_to_empty(tmp_path):
    """Cellule standard (pas de metadata.translate) -> translate_policy=""

    Le défaut sémantique = "traduire" (T3 se comporte comme avant)."""
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["du contenu normal"]},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    assert rows[0]["translate_policy"] == ""


def test_extract_unknown_policy_value_falls_back_to_empty(tmp_path):
    """Valeur inconnue (ex. "verbatim-with-gloss") -> chaîne vide.

    T1 ne connaît pas la sémantique future — son rôle = transporter un marqueur.
    Une valeur non-reconnue EST le défaut chaîne vide pour T3 (qui lit
    explicitement == "verbatim" ; toute autre valeur = défaut "traduire").
    Une politique additionnelle ne casse pas les anciennes extractions."""
    p = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["x"],
         "meta": {"translate": "verbatim-with-gloss"}},
    ])
    rows = e.extract_notebook(p.resolve(), tmp_path.resolve(), "fr")
    # Transport strict : la valeur déclarée est transportée telle quelle.
    assert rows[0]["translate_policy"] == "verbatim-with-gloss"


def test_extract_translate_policy_is_pivot_in_update(tmp_path):
    """translate_policy rejoint PIVOT_COLS — un changement de politique
    propage dans le CSV existant (sinon l'éditeur du notebook ajoute
    "verbatim" et la politique ne s'applique jamais)."""
    existing = [_row("nb.ipynb", "c1")]   # translate_policy = ""
    fresh = [_row("nb.ipynb", "c1", translate_policy="verbatim")]
    _, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 1  # compté comme un vrai changement


def test_extract_translate_policy_unchanged_is_in_sync(tmp_path):
    """Pas de changement de politique -> unchanged.

    Sans ce test, un run qui ne touche pas au notebook signalerait des
    « updated » fantômes."""
    existing = [_row("nb.ipynb", "c1", translate_policy="verbatim")]
    fresh = [_row("nb.ipynb", "c1", translate_policy="verbatim")]
    _, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 0
    assert stats["unchanged"] == 1


def test_extract_translate_policy_drops_when_metadata_removed():
    """Retirer metadata.translate du notebook -> CSV sync sur "" également.

    L'auteur du notebook a explicitement enlevé la politique ; le CSV doit le
    suivre (et T3 retombera sur le défaut « traduire »)."""
    existing = [_row("nb.ipynb", "c1", translate_policy="verbatim")]
    fresh = [_row("nb.ipynb", "c1", translate_policy="")]
    _, stats = e.update_existing_csv(list(existing), fresh, {"nb.ipynb"})
    assert stats["updated"] == 1


# --------------------------------------------------------------------------
# Constants — schéma ratifié #4957
# --------------------------------------------------------------------------

def test_pivot_lang_is_fr():
    assert e.PIVOT_LANG == "fr"


def test_target_langs_seven():
    assert e.TARGET_LANGS == ["en", "es", "ar", "fa", "zh", "ru", "pt"]


def test_columns_order_and_completeness():
    # Schéma ratifié : notebook, cell_id, cell_type, src_lang, src_hash, puis
    # text_<lang> pour [fr]+TARGET, puis hash_<lang> pour [fr]+TARGET, puis
    # translate_policy (#10326 : politique per-row, lue par T1 depuis
    # cell.metadata.translate, honorée par T3) en queue pour rester
    # rétro-compatible avec les CSV générés par la tranche 1.
    expected = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash"]
    expected += [f"text_{l}" for l in ["fr"] + e.TARGET_LANGS]
    expected += [f"hash_{l}" for l in ["fr"] + e.TARGET_LANGS]
    expected += ["translate_policy"]
    assert e.COLUMNS == expected


# --------------------------------------------------------------------------
# main() — exit codes (0 clean, 2 no-input, 1 0-cells, --update mode)
# --------------------------------------------------------------------------

def test_main_clean_extract_returns_0(tmp_path, monkeypatch, capsys):
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["# Titre"]},
    ])
    out = tmp_path / "out.csv"
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py", str(nb), "-o", str(out),
        "--repo-root", str(tmp_path),
    ])
    rc = e.main()
    assert rc == 0
    assert out.exists()


def test_main_no_valid_input_returns_2(tmp_path, monkeypatch):
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py", str(tmp_path / "missing.ipynb"),
    ])
    rc = e.main()
    assert rc == 2


def test_main_zero_cells_returns_1(tmp_path, monkeypatch):
    # Notebook valide mais 0 cellules extractibles (aucune avec id + type md/code).
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps({"cells": [
        {"id": None, "cell_type": "markdown", "source": ["x"]},
    ], "nbformat": 4}), encoding="utf-8")
    monkeypatch.setattr(sys, "argv", ["extract_cells_to_csv.py", str(p),
                                      "--repo-root", str(tmp_path)])
    rc = e.main()
    assert rc == 1


def test_main_update_mode_preserves_other_entries(tmp_path, monkeypatch):
    nb = _write_nb(tmp_path, "nb.ipynb", [
        {"id": "c1", "type": "markdown", "source": ["nouveau texte"]},
    ])
    existing = tmp_path / "existing.csv"
    # CSV existant avec une entrée d'un AUTRE notebook + l'entrée cible ancienne.
    existing.write_text(
        "notebook,cell_id,cell_type,src_lang,src_hash,text_fr,hash_fr,text_en,hash_en\n"
        "other.ipynb,x1,markdown,fr,keep,autre,keep,trad en,hash_en\n"
        "nb.ipynb,c1,markdown,fr,OLD,ancien texte,OLD,,\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(sys, "argv", [
        "extract_cells_to_csv.py", str(nb), "--update", str(existing),
        "--repo-root", str(tmp_path),
    ])
    rc = e.main()
    assert rc == 0
    # Le CSV mis à jour contient l'autre notebook intact + la cible rafraîchie.
    with existing.open(encoding="utf-8", newline="") as f:
        rows = list(csv.DictReader(f))
    notebooks = {r["notebook"] for r in rows}
    assert "other.ipynb" in notebooks  # préservé
    assert "nb.ipynb" in notebooks  # cible
    # L'entrée other a gardé sa traduction en.
    other = [r for r in rows if r["notebook"] == "other.ipynb"][0]
    assert other["text_en"] == "trad en"
