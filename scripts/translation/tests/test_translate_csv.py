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
import urllib.error
from pathlib import Path

import pytest

# importlib used by test_enabled_false_by_default_fresh_reload (ported from
# legacy shadow) to read the module's pristine ENABLED default.
import importlib  # noqa: E402

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


def _stub_translator(records):
    """Remplaçant de translate_markdown qui enregistre (lang, texte) sans appeler l'API.

    Sert aux tests du cap (--max-cells), du cache (0 appels sur lot inchangé) et de
    la dégradation propre (échec simulé) — grain D #10043. Aucun réseau.
    """
    def _fake(fr_text, target_lang, model, key, base_url, **kw):
        records.append((target_lang, fr_text))
        return f"[{target_lang}] {fr_text[:12]}", 0.01, 0
    return _fake


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
    """--apply + TRANSLATE_ENABLED inactif = GATED no-op (aucun appel API, aucune mutation).

    Grain D #10043 : la gate est désormais env-controlled (TRANSLATE_ENABLED),
    CI-callable sans monkeypatch source. On force la gate fermée pour un test
    déterministe quel que soit l'environnement d'exécution.
    """
    csv_path = _write_csv(tmp_path / "in.csv", [_row("c1", text_fr="bonjour")])
    original = csv_path.read_bytes()
    monkeypatch.setattr(t3, "ENABLED", False)  # gate fermée, déterministe
    monkeypatch.setattr(sys, "argv", ["translate_csv.py", "--csv", str(csv_path), "--apply"])
    rc = t3.main()
    assert rc == 0
    assert csv_path.read_bytes() == original  # gated = aucune mutation
    err = capsys.readouterr().err
    assert "GATED" in err
    assert "TRANSLATE_ENABLED inactif" in err


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
    # 5 cells markdown x 1 langue = 5 traductions. --limit 2 (alias de --max-cells,
    # grain D #10043) borne l'EXÉCUTION --apply à 2 ; le dry-run affiche le plan
    # complet (5) + signale le cap.
    csv_path = _write_csv(tmp_path / "in.csv", [
        _row(f"c{i}", text_fr=f"cellule {i}") for i in range(5)
    ])
    monkeypatch.setattr(sys, "argv", [
        "translate_csv.py", "--csv", str(csv_path), "--lang", "es", "--limit", "2"])
    rc = t3.main()
    assert rc == 0
    err = capsys.readouterr().err
    assert "5 traductions nécessaires" in err  # dry-run = plan complet (informatif)
    assert "borné à 2" in err  # cap --limit=2 signalé pour --apply


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


# --------------------------------------------------------------------------
# Grain D #10043 — activation env + cap + dégradation propre + cache
# --------------------------------------------------------------------------

def test_activation_env_flag(monkeypatch):
    """TRANSLATE_ENABLED contrôle la gate (CI-callable, sans monkeypatch source).

    Grain D #10043 acceptance #1 : T3 activable sans éditer la source. La CI
    positionne TRANSLATE_ENABLED=1 dans son env au lieu du workaround importlib
    de #10032.
    """
    monkeypatch.delenv("TRANSLATE_ENABLED", raising=False)
    assert t3._enabled_from_env() is False
    for v in ("1", "true", "TRUE", "Yes", "on"):
        monkeypatch.setenv("TRANSLATE_ENABLED", v)
        assert t3._enabled_from_env() is True, f"{v!r} should enable"
    for v in ("0", "false", "no", "off", "", "random", "2"):
        monkeypatch.setenv("TRANSLATE_ENABLED", v)
        assert t3._enabled_from_env() is False, f"{v!r} should NOT enable"


def test_max_cells_caps_api_calls(tmp_path, monkeypatch):
    """--max-cells borne le nombre d'appels API (grain D #10043 acceptance #3).

    5 cellules éligibles, cap=2 => exactement 2 appels provider (pas 5). Protège
    contre un bug de hash qui déclencherait une passe complète.
    """
    rows = [_row(f"c{i}", text_fr=f"cellule {i}") for i in range(5)]
    monkeypatch.setattr(t3, "_provider_keys", lambda: [("stub-model", "k", "http://x")])
    calls = []
    monkeypatch.setattr(t3, "translate_markdown", _stub_translator(calls))
    done, fails = t3.run_translations(rows, ["es"], False, str(tmp_path / "out.csv"), False, limit=2)
    assert done == 2 and fails == 0
    assert len(calls) == 2  # cap respecté : 2 appels, pas 5


def test_graceful_degradation_no_source_copy(tmp_path, monkeypatch):
    """Échec provider => text_<lang> RESTE VIDE (jamais recopiée depuis text_fr).

    Grain D #10043 acceptance #4 : pas de falsification (récopie du source dans la
    colonne cible = même faute que la règle 6 sur les sorties de cellules).
    """

    def _fail(fr_text, target_lang, model, key, base_url, **kw):
        raise urllib.error.HTTPError("http://x", 500, "server err", {}, None)

    rows = [_row("c1", text_fr="contenu source français secret")]
    monkeypatch.setattr(t3, "_provider_keys", lambda: [("stub", "k", "http://x")])
    monkeypatch.setattr(t3, "translate_markdown", _fail)
    done, fails = t3.run_translations(rows, ["es"], False, str(tmp_path / "out.csv"), False, limit=5)
    assert done == 0 and fails == 1
    assert rows[0]["text_es"] == ""  # resté vide, pas recopié depuis text_fr
    assert "secret" not in rows[0]["text_es"]
    assert rows[0]["hash_es"] == ""


def test_cache_zero_calls_on_unchanged_lot(tmp_path, monkeypatch):
    """Cache (text_<lang> rempli) : 2e passe sur lot inchangé = 0 appel provider.

    Grain D #10043 acceptance #2 : la propriété qui rend l'automatisation (grain C)
    soutenable — les cellules déjà traduites ne sont jamais re-soumises.
    """
    rows = [_row(f"c{i}", text_fr=f"cellule {i}") for i in range(3)]
    monkeypatch.setattr(t3, "_provider_keys", lambda: [("stub", "k", "http://x")])
    calls1 = []
    monkeypatch.setattr(t3, "translate_markdown", _stub_translator(calls1))
    out = str(tmp_path / "out.csv")
    t3.run_translations(rows, ["es"], False, out, False, limit=10)  # 1re passe
    assert len(calls1) == 3  # 3 cellules traduites
    # 2e passe : text_es rempli pour les 3 => plan vide => 0 appel (cache)
    calls2 = []
    monkeypatch.setattr(t3, "translate_markdown", _stub_translator(calls2))
    done2, fails2 = t3.run_translations(rows, ["es"], False, out, False, limit=10)
    assert done2 == 0 and fails2 == 0
    assert len(calls2) == 0  # cache : 0 appel provider sur lot inchangé


# =========================================================================== #
# Ported verbatim from the deleted legacy scripts/tests/test_translate_csv.py
# shadow (#10066 consolidation, tranche 7). Unlike the 5 collision tranches of
# this campaign, the two files did NOT collide here (both-together = 58 = 35+23,
# additive, not N×2): the canon was LIVE in CI. So deleting the legacy without
# porting would have dropped 23 real tests. Per-test intent reconciliation
# ([[consolidate-test-files-verify-per-test-not-count]]) found 16 of the 23
# already covered by the canon (often more granularly); these 7 are the UNIQUE
# coverages the canon entirely lacked:
#
#   - normalize() never tested (canon tests cell_hash, not its normalize feeder)
#   - run_translations write-contract (text_<lang> + hash_<lang> = cell_hash)
#   - CRLF-vs-LF hash stability (cross-OS checkout drift guard)
#   - anchored hash regression value (ec9615f904e04755 locks the algorithm)
#   - ENABLED=False read via module RELOAD (pristine default, not a monkeypatch)
#   - per-language text_/hash_ column existence (schema completeness)
#   - source secrets-hygiene scan (no os.getenv("KEY", "<literal>") fallback)
# =========================================================================== #


# --------------------------------------------------------------------------
# normalize — the cell_hash feeder (canon tested cell_hash but never normalize)
# --------------------------------------------------------------------------
def test_normalize_rstrips_lines_and_trailing_newline():
    # Trailing whitespace + final newline must NOT create faux drift.
    assert t3.normalize("line   \nsecond\t\n") == "line\nsecond"
    assert t3.normalize("single") == "single"
    assert t3.normalize("") == ""


# --------------------------------------------------------------------------
# run_translations write-contract (hash_<lang> = cell_hash(text_<lang>))
# --------------------------------------------------------------------------
def test_run_translations_writes_text_and_hash_coherent(monkeypatch, tmp_path):
    """run_translations MUST write text_<lang> AND hash_<lang> = cell_hash of that
    text. T2 reads hash_<lang> for drift-detection, so a stale/empty hash breaks
    the pipeline. The canon tested stubs but never the write-side contract."""

    def fake_call(messages, model, key, base_url, max_tokens, reasoning_effort="low", timeout=240):
        um = next(m["content"] for m in messages if m["role"] == "user")
        lang_name = um.split("into ")[1].split(".")[0]
        return f"[{lang_name}] translated", 0.1, 5

    monkeypatch.setattr(t3, "call_chat", fake_call)
    monkeypatch.setenv("OPENAI_API_KEY", "fake-key-for-testing")

    rows = [_row("c1", text_fr="Bonjour le monde")]
    csv_path = tmp_path / "x.csv"
    _write_csv(csv_path, rows)
    loaded = t3.load_csv(str(csv_path))
    done, fails = t3.run_translations(loaded, ["en"], include_code=False,
                                      out_path=str(csv_path), smoke=False)
    assert done == 1 and fails == 0
    result = t3.load_csv(str(csv_path))
    assert result[0]["text_en"] == "[English] translated"
    # hash_en MUST equal cell_hash of the written text (T2 coherence contract).
    assert result[0]["hash_en"] == t3.cell_hash("[English] translated")


# --------------------------------------------------------------------------
# Hash stability + anchored regression value
# --------------------------------------------------------------------------
def test_cell_hash_ignores_crlf_vs_lf():
    # CRLF vs LF must NOT create faux drift across Windows/POSIX checkouts.
    assert t3.cell_hash("ligne un\r\nligne deux") == t3.cell_hash("ligne un\nligne deux")


def test_cell_hash_anchored_value():
    # Anchored regression value : locks the hash algorithm itself (16 hex sha256
    # of the normalized text). Changing normalize/cell_hash breaks drift-detection
    # parity with T1/T2, so this must stay stable.
    assert t3.cell_hash("## Introduction au machine learning") == "ec9615f904e04755"


# --------------------------------------------------------------------------
# ENABLED=False pristine default via module RELOAD (not a possibly-patched global)
# --------------------------------------------------------------------------
def test_enabled_false_by_default_fresh_reload():
    # Reload the module to read its pristine default (a prior test may have
    # monkeypatched t3.ENABLED). The gate must ship disabled.
    fresh = importlib.reload(t3)
    assert fresh.ENABLED is False


# --------------------------------------------------------------------------
# Schema completeness — every target has a text_ and hash_ column
# --------------------------------------------------------------------------
def test_every_target_has_text_and_hash_column():
    for lang in t3.TARGETS:
        assert f"text_{lang}" in t3.CSV_COLUMNS, f"missing text_{lang}"
        assert f"hash_{lang}" in t3.CSV_COLUMNS, f"missing hash_{lang}"


# --------------------------------------------------------------------------
# Source secrets-hygiene scan — never os.getenv("KEY", "<literal>")
# --------------------------------------------------------------------------
def test_provider_keys_have_no_literal_default_in_source():
    # secrets-hygiene rule 1-3 : never os.getenv("KEY", "<literal>"). The key
    # must come from env only (no inline fallback that could leak a real secret).
    src = Path(t3.__file__).read_text(encoding="utf-8")
    assert 'getenv("OPENAI_API_KEY"' in src
    assert 'getenv("OPENAI_API_KEY", "' not in src  # no literal default
