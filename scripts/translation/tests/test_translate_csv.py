"""Tests for translate_csv.py (T3 fork, #6949 PR #2 acceptance).

Fixture-first round-trip : un CSV canonique `fixtures/sample.csv` est lu,
réécrit via write_csv, et la perte doit être nulle. Couvre aussi le hash
contract T3↔T2 (cell_hash recompute), l'éligibilité du translation_plan,
la sécurité env-only des clés provider, et le gate ENABLED.

Le moteur n'appelle jamais l'API dans ces tests (ENABLED=False, aucune clé).
"""
import csv
import importlib
import os
import sys

import pytest

# Add parent dir so `import translate_csv` resolves (convention scripts/notebook_tools/tests).
sys.path.insert(0, str(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

import translate_csv as t3

FIXTURE = os.path.join(os.path.dirname(__file__), "fixtures", "sample.csv")


# ---------------------------------------------------------------------------
# Hash contract — T3 doit reproduire exactement le hash de T1/T2 (cell_hash).
# ---------------------------------------------------------------------------
class TestHashContract:
    def test_cell_hash_is_16_hex(self):
        h = t3.cell_hash("anything")
        assert len(h) == 16
        int(h, 16)  # raises if not hex

    def test_normalize_strips_trailing_whitespace_per_line(self):
        assert t3.normalize("a   \nb\t\n") == "a\nb"

    def test_cell_hash_ignores_trailing_whitespace(self):
        # Faux-drift cosmétique : trailing space ne change pas le hash.
        assert t3.cell_hash("hello   ") == t3.cell_hash("hello")

    def test_cell_hash_ignores_crlf_vs_lf(self):
        assert t3.cell_hash("a\r\nb") == t3.cell_hash("a\nb")

    def test_cell_hash_stable(self):
        # Valeur ancrée pour bloquer une régression du hash (drift-detection).
        assert t3.cell_hash("## Introduction au machine learning") == "ec9615f904e04755"


# ---------------------------------------------------------------------------
# CSV round-trip — load_csv -> write_csv lossless (BOM toléré en lecture).
# ---------------------------------------------------------------------------
class TestCsvRoundTrip:
    def test_load_csv_reads_fixture(self):
        rows = t3.load_csv(FIXTURE)
        assert len(rows) == 4
        assert rows[0]["cell_id"] == "abc12345"
        assert rows[0]["cell_type"] == "markdown"

    def test_load_csv_tolerates_utf8_bom(self, tmp_path):
        # Un CSV avec BOM ne doit pas fuir le BOM dans le premier champ.
        p = tmp_path / "bom.csv"
        p.write_bytes(b"\xef\xbb\xbfnotebook,cell_id\r\nx.ipynb,c1\r\n")
        rows = t3.load_csv(str(p))
        assert rows[0]["notebook"] == "x.ipynb"  # PAS '﻿x.ipynb'

    def test_write_then_reload_is_lossless_on_canonical_columns(self, tmp_path):
        rows = t3.load_csv(FIXTURE)
        out = tmp_path / "rt.csv"
        t3.write_csv(str(out), rows)
        rows2 = t3.load_csv(str(out))
        assert len(rows2) == len(rows)
        for a, b in zip(rows, rows2):
            for col in t3.CSV_COLUMNS:
                assert a.get(col, "") == b.get(col, ""), f"column {col} diverged"

    def test_write_csv_preserves_column_order(self, tmp_path):
        rows = t3.load_csv(FIXTURE)
        out = tmp_path / "order.csv"
        t3.write_csv(str(out), rows)
        with open(out, encoding="utf-8") as f:
            header = next(csv.reader(f))
        assert header == t3.CSV_COLUMNS

    def test_write_csv_uses_lf_line_endings(self, tmp_path):
        rows = t3.load_csv(FIXTURE)
        out = tmp_path / "lf.csv"
        t3.write_csv(str(out), rows)
        raw = out.read_bytes()
        assert b"\r\n" not in raw  # LF uniquement (lineterminator='\n')


# ---------------------------------------------------------------------------
# translation_plan — éligibilité markdown x langue cible vide.
# ---------------------------------------------------------------------------
class TestTranslationPlan:
    def test_plan_excludes_already_translated_language(self):
        rows = t3.load_csv(FIXTURE)
        # abc12345 (row 0) a text_en rempli -> 'en' exclu pour cette ligne ;
        # def67890 (row 1) a text_en vide -> 'en' inclus.
        plan = list(t3.translation_plan(rows, ["en"]))
        idxs = {i for i, _ in plan}
        assert 0 not in idxs
        assert 1 in idxs

    def test_plan_yields_non_en_targets_for_partially_translated_cell(self):
        rows = t3.load_csv(FIXTURE)
        # abc12345 n'est traduit qu'en 'en' -> es/ar/fa/zh/ru/pt toutes vides.
        plan = list(t3.translation_plan(rows, ["es", "ar", "fa", "zh", "ru", "pt"]))
        idxs = {i for i, _ in plan}
        # Les 2 lignes markdown (0 et 1) sont éligibles pour ces 6 langues.
        assert idxs == {0, 1}

    def test_plan_skips_code_cells_by_default(self):
        rows = t3.load_csv(FIXTURE)
        plan = list(t3.translation_plan(rows, t3.TARGETS))
        idxs = {i for i, _ in plan}
        assert 2 not in idxs  # code1111 = code, skippé

    def test_plan_includes_code_when_flag_set(self):
        rows = t3.load_csv(FIXTURE)
        plan = list(t3.translation_plan(rows, ["en"], include_code=True))
        assert (2, "en") in plan  # code1111 maintenant éligible

    def test_plan_skips_empty_fr(self):
        rows = t3.load_csv(FIXTURE)
        plan = list(t3.translation_plan(rows, t3.TARGETS))
        idxs = {i for i, _ in plan}
        assert 3 not in idxs  # empty222 = text_fr vide


# ---------------------------------------------------------------------------
# Sécurité — clés provider depuis l'env uniquement, gate ENABLED.
# ---------------------------------------------------------------------------
class TestSecurity:
    def test_provider_keys_empty_without_env(self, monkeypatch):
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
        assert t3._provider_keys() == []

    def test_provider_keys_reads_openai_env(self, monkeypatch):
        monkeypatch.setenv("OPENAI_API_KEY", "sk-test")
        monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
        provs = t3._provider_keys()
        assert len(provs) == 1
        model, key, base = provs[0]
        assert key == "sk-test"
        assert base == "https://api.openai.com/v1"

    def test_provider_keys_no_literals(self):
        # La clé ne doit JAMAIS venir d'un littéral dans le module (secrets-hygiene).
        src = open(t3.__file__, encoding="utf-8").read()
        # Pas de pattern os.getenv("KEY", "<défaut>") avec littéral inline.
        assert 'getenv("OPENAI_API_KEY"' in src
        assert 'getenv("OPENAI_API_KEY", "' not in src  # pas de default littéral

    def test_enabled_gate_is_false_by_default(self):
        # Module chargé frais (jamais muté par un test précédent).
        importlib.reload(t3)
        assert t3.ENABLED is False

    def test_run_translations_raises_without_keys(self, monkeypatch):
        # Même si ENABLED était True, pas de clé -> erreur claire (pas de fuite).
        monkeypatch.delenv("OPENAI_API_KEY", raising=False)
        monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
        with pytest.raises(ValueError, match="Aucune clé API"):
            t3.run_translations([], ["en"], False, "/tmp/x.csv", False)


# ---------------------------------------------------------------------------
# Conformité schéma — 7 langues cibles, alignées T1/T2.
# ---------------------------------------------------------------------------
class TestSchemaAlignment:
    def test_targets_are_seven_canonical_languages(self):
        assert t3.TARGETS == ["en", "ru", "pt", "es", "ar", "fa", "zh"]

    def test_every_target_has_text_and_hash_column(self):
        for lang in t3.TARGETS:
            assert f"text_{lang}" in t3.CSV_COLUMNS
            assert f"hash_{lang}" in t3.CSV_COLUMNS
