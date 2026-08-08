#!/usr/bin/env python3
"""Tests pour scripts/translation/translate_csv.py — T3 du pipeline de synchro
traduction (Epic #4957 / #1650, issue #6949). Moteur de traduction FR -> 7
langues cibles, fork d'Argumentum `translate_game_rules.py`.

Ferme l'unité pipeline complète T1+T2+T3 : T1 (extract_cells_to_csv, #9265) +
T2 (check_translation_sync, #9266) + T3 (ce fichier). Le contrat hash est
CRITIQUE — T3 ÉCRIT les hash_<lang> que T2 LIT pour le drift-detection.

Couvre les fonctions pures hermétiques (le moteur est GATED : ENABLED=False par
défaut, --dry-run défaut, clés API env-only -> aucune fonction réseau n'est
exercée). stdlib-only (csv/hashlib/os/json/sys/argparse/urllib), hermétique.
"""

import csv
import os
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import translate_csv as t3  # noqa: E402


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

def _row(cell_id="c1", cell_type="markdown", text_fr="", **extra):
    """Ligne CSV minimale avec toutes les colonnes canoniques vides."""
    r = {col: "" for col in t3.CSV_COLUMNS}
    r.update(notebook="nb.ipynb", cell_id=cell_id, cell_type=cell_type,
             src_lang="fr", text_fr=text_fr)
    r.update(extra)
    return r


def _write_csv(path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=t3.CSV_COLUMNS, lineterminator="\n")
        w.writeheader()
        for row in rows:
            w.writerow({c: row.get(c, "") for c in t3.CSV_COLUMNS})
    return path


# --------------------------------------------------------------------------
# normalize / cell_hash — contrat byte-identique avec T1 ET T2 (anti faux-drift)
# --------------------------------------------------------------------------

def test_cell_hash_16_hex_deterministic():
    h = t3.cell_hash("texte")
    assert len(h) == 16
    assert h == t3.cell_hash("texte")


def test_cell_hash_insensitive_to_cosmetic_whitespace():
    assert t3.cell_hash("ligne   \n") == t3.cell_hash("ligne")


def test_cell_hash_contract_identical_to_t1_and_t2():
    """CRITIQUE (#4957) : T3 ÉCRIT hash_<lang> que T2 LIT. Les trois modules
    DOIVENT produire le même hash, sinon T2 génère des faux TRAD_DRIFT."""
    import extract_cells_to_csv as t1
    import check_translation_sync as t2
    samples = ["bonjour le monde", "# Titre\n\nParagraphe.", "code = 1\n",
               "  spaced  \n\n line\t", "مرحبا", "你好"]
    for s in samples:
        h3 = t3.cell_hash(s)
        assert h3 == t1.cell_hash(s), f"T3!=T1 on {s!r}"
        assert h3 == t2.cell_hash(s), f"T3!=T2 on {s!r}"


# --------------------------------------------------------------------------
# Gate de sécurité (HARD) — ENABLED=False par défaut
# --------------------------------------------------------------------------

def test_enabled_gate_is_false_by_default():
    """Le moteur T3 est GATED : ENABLED=False au chargement du module. Aucun
    appel API / mutation possible tant que non flippé en source (GO user)."""
    assert t3.ENABLED is False


# --------------------------------------------------------------------------
# CSV I/O — load_csv (utf-8-sig BOM-tolerant) + write_csv (LF, ordre colonnes)
# --------------------------------------------------------------------------

def test_load_csv_returns_rows(tmp_path):
    p = _write_csv(tmp_path / "s.csv", [_row("c1", text_fr="bonjour")])
    rows = t3.load_csv(str(p))
    assert len(rows) == 1
    assert rows[0]["text_fr"] == "bonjour"


def test_load_csv_tolerates_utf8_bom(tmp_path):
    """utf-8-sig : un CSV avec BOM (export Excel) doit charger sans fuite du
    BOM dans le premier nom de colonne."""
    p = tmp_path / "bom.csv"
    p.write_bytes(b"\xef\xbb\xbfnotebook,cell_id,text_fr\nnb,c1,salut\n")
    rows = t3.load_csv(str(p))
    assert rows[0]["notebook"] == "nb"  # pas "﻿nb"
    assert rows[0]["text_fr"] == "salut"


def test_write_csv_canonical_column_order(tmp_path):
    p = tmp_path / "out.csv"
    t3.write_csv(str(p), [_row("c1", text_fr="x")])
    with p.open(encoding="utf-8", newline="") as f:
        hdr = next(csv.reader(f))
    assert hdr == t3.CSV_COLUMNS


def test_write_csv_is_lf_only(tmp_path):
    p = tmp_path / "out.csv"
    t3.write_csv(str(p), [_row("c1", text_fr="ligne1\nligne2")])
    assert b"\r" not in p.read_bytes()


def test_write_csv_ignores_extra_columns_and_fills_missing(tmp_path):
    """Garde-fou (L114) : ne perdre aucune colonne canonique, ignore les extras."""
    row = _row("c1", text_fr="x")
    row["extra_noncanonical"] = "drop me"  # ignorée
    del row["text_pt"]  # manquante -> remplie ""
    p = tmp_path / "out.csv"
    t3.write_csv(str(p), [row])
    with p.open(encoding="utf-8", newline="") as f:
        data = list(csv.DictReader(f))
    assert "extra_noncanonical" not in data[0]
    assert data[0]["text_pt"] == ""


def test_load_write_roundtrip_preserves_data(tmp_path):
    rows = [_row("c1", text_fr="fr1", text_en="en1", hash_en="h"),
            _row("c2", text_fr="fr2")]
    p = tmp_path / "rw.csv"
    _write_csv(p, rows)
    loaded = t3.load_csv(str(p))
    p2 = tmp_path / "out.csv"
    t3.write_csv(str(p2), loaded)
    loaded2 = t3.load_csv(str(p2))
    assert [r["text_fr"] for r in loaded2] == ["fr1", "fr2"]
    assert loaded2[0]["text_en"] == "en1"
    assert loaded2[0]["hash_en"] == "h"


# --------------------------------------------------------------------------
# translation_plan — éligibilité (markdown par défaut, cache, include_code gate)
# --------------------------------------------------------------------------

def test_translation_plan_yields_empty_lang_cells():
    rows = [
        _row("c1", text_fr="bonjour"),                # toutes langues vides
        _row("c2", text_fr="salut", text_en="hello"),  # en rempli -> skip en
    ]
    plan = list(t3.translation_plan(rows, ["en", "es"]))
    # c1 -> en, c1 -> es, c2 -> es (c2->en skip car déjà rempli = cache)
    assert (0, "en") in plan
    assert (0, "es") in plan
    assert (1, "es") in plan
    assert (1, "en") not in plan  # déjà traduit = pas re-planifié


def test_translation_plan_skips_empty_fr():
    rows = [_row("c1", text_fr=""), _row("c2", text_fr="   ")]
    assert list(t3.translation_plan(rows, ["en"])) == []


def test_translation_plan_skips_code_by_default():
    rows = [_row("c1", cell_type="code", text_fr="print(1)")]
    assert list(t3.translation_plan(rows, ["en"])) == []


def test_translation_plan_includes_code_when_flagged():
    rows = [_row("c1", cell_type="code", text_fr="print(1)")]
    plan = list(t3.translation_plan(rows, ["en"], include_code=True))
    assert plan == [(0, "en")]


def test_translation_plan_skips_unknown_cell_types():
    rows = [_row("c1", cell_type="raw", text_fr="x")]
    assert list(t3.translation_plan(rows, ["en"])) == []


def test_translation_plan_all_seven_targets():
    rows = [_row("c1", text_fr="bonjour")]
    plan = list(t3.translation_plan(rows, t3.TARGETS))
    langs = {lang for _, lang in plan}
    assert langs == set(t3.TARGETS)


# --------------------------------------------------------------------------
# _provider_keys — env-only (mocked, jamais de réseau)
# --------------------------------------------------------------------------

def test_provider_keys_empty_when_no_env(monkeypatch):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    assert t3._provider_keys() == []


def test_provider_keys_openai_primary(monkeypatch):
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    providers = t3._provider_keys()
    assert len(providers) == 1
    model, key, base = providers[0]
    assert key == "fake-key-for-testing"
    assert base == t3.DEFAULT_BASE_URL


def test_provider_keys_openrouter_fallback(monkeypatch):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.setenv("OPENROUTER_API_KEY", "fake-router-key")
    providers = t3._provider_keys()
    assert len(providers) == 1
    model, key, base = providers[0]
    assert base == t3.OPENROUTER_BASE_URL


def test_provider_keys_both_when_both_env(monkeypatch):
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")
    monkeypatch.setenv("OPENROUTER_API_KEY", "fake-router-key")
    assert len(t3._provider_keys()) == 2  # primaire + fallback


# --------------------------------------------------------------------------
# run_translations — ValueError si aucune clé (jamais de réseau)
# --------------------------------------------------------------------------

def test_run_translations_raises_without_keys(monkeypatch, tmp_path):
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    rows = [_row("c1", text_fr="bonjour")]
    with pytest.raises(ValueError, match="Aucune clé API"):
        t3.run_translations(rows, ["en"], False, str(tmp_path / "o.csv"), False)


# --------------------------------------------------------------------------
# main() — dry-run no-mutation, --apply ENABLED=False gated no-op, exit codes
# --------------------------------------------------------------------------

def test_main_dry_run_returns_0_no_mutation(tmp_path, monkeypatch, capsys):
    csv_path = _write_csv(tmp_path / "in.csv", [_row("c1", text_fr="bonjour")])
    original = csv_path.read_bytes()
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path)])
    rc = t3.main()
    assert rc == 0
    assert csv_path.read_bytes() == original  # dry-run = aucune mutation
    err = capsys.readouterr().err
    assert "dry-run" in err.lower()


def test_main_apply_gated_noop_when_disabled(tmp_path, monkeypatch, capsys):
    """--apply + ENABLED=False = GATED no-op (aucun appel API, aucune mutation)."""
    csv_path = _write_csv(tmp_path / "in.csv", [_row("c1", text_fr="bonjour")])
    original = csv_path.read_bytes()
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path), "--apply"])
    rc = t3.main()
    assert rc == 0
    assert csv_path.read_bytes() == original  # gated = aucune mutation
    err = capsys.readouterr().err
    assert "GATED" in err
    assert "ENABLED=False" in err


def test_main_smoke_restricts_to_first_cell(tmp_path, monkeypatch, capsys):
    csv_path = _write_csv(tmp_path / "in.csv", [
        _row("c1", text_fr="un"), _row("c2", text_fr="deux"), _row("c3", text_fr="trois"),
    ])
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path), "--smoke"])
    rc = t3.main()
    assert rc == 0
    err = capsys.readouterr().err
    # smoke = 1 cellule x 7 langues = 7 traductions planifiées (pas 21).
    assert "7 traductions" in err or " 7 " in err


def test_main_limit_bounds_plan(tmp_path, monkeypatch, capsys):
    # 5 cells markdown x 1 langue = 5 traductions ; --limit 2 borne a 2 (#6949).
    csv_path = _write_csv(tmp_path / "in.csv", [
        _row(f"c{i}", text_fr=f"cellule {i}") for i in range(5)
    ])
    monkeypatch.setattr(sys, "argv", [
        "translate_csv.py", "--csv", str(csv_path), "--lang", "es", "--limit", "2"])
    rc = t3.main()
    assert rc == 0
    err = capsys.readouterr().err
    assert "2 traductions nécessaires" in err  # borne par --limit, pas 5


def test_main_single_lang(tmp_path, monkeypatch, capsys):
    csv_path = _write_csv(tmp_path / "in.csv", [_row("c1", text_fr="bonjour")])
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path), "--lang", "es"])
    rc = t3.main()
    assert rc == 0
    err = capsys.readouterr().err
    assert "1 langue" in err  # --lang es = 1 langue


def test_main_include_code_flag_plans_code_cells(tmp_path, monkeypatch, capsys):
    csv_path = _write_csv(tmp_path / "in.csv", [
        _row("c1", cell_type="code", text_fr="print(1)"),
        _row("c2", text_fr="markdown"),
    ])
    monkeypatch.setattr(sys, "argv",
                        ["translate_csv.py", "--csv", str(csv_path), "--include-code"])
    rc = t3.main()
    assert rc == 0
    err = capsys.readouterr().err
    # include_code=True : 2 cellules x 7 langues = 14 (vs 7 sans le flag).
    assert "14 traductions" in err or " 14 " in err
    assert "include_code=True" in err


def test_main_load_report(tmp_path, monkeypatch, capsys):
    csv_path = _write_csv(tmp_path / "in.csv", [
        _row("c1", cell_type="markdown", text_fr="md"),
        _row("c2", cell_type="code", text_fr="code"),
    ])
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path)])
    t3.main()
    err = capsys.readouterr().err
    assert "2 lignes" in err
    assert "1 markdown" in err
    assert "1 code" in err


# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------

def test_targets_are_seven_langs():
    assert set(t3.TARGETS) == {"en", "ru", "pt", "es", "ar", "fa", "zh"}


def test_lang_names_covers_all_targets():
    for lang in t3.TARGETS:
        assert lang in t3.LANG_NAMES


def test_csv_columns_match_pipeline_schema():
    """T3 DOIT utiliser le même schéma de colonnes que T1/T2 (contrat pipeline)."""
    import extract_cells_to_csv as t1
    # T3 CSV_COLUMNS doit être un sous-ensemble cohérent du schéma ratifié T1.
    for col in t3.CSV_COLUMNS:
        assert col in t1.COLUMNS, f"T3 column {col} not in T1 schema"
