#!/usr/bin/env python3
"""Unit tests for ``multilingual_drift_audit.py`` (fork of Argumentum #192 audit).

Covers the 4 drift classes (MISSING / ORPHAN / FR_CONTAM / WRONG_SCRIPT), the
script-detection helpers, the FR_CONTAM min-length threshold, the empty-FR edge
case, and aggregation across multiple CSVs. Synthetic CSV fixtures via tmp_path.
See #6949 grain 1.
"""

from __future__ import annotations

import csv
import os
import sys

import pytest

# Make the sibling module importable.
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

import multilingual_drift_audit as mda  # noqa: E402

FIELDS = [
    "notebook", "cell_id", "cell_type", "src_lang", "src_hash",
    "text_fr", "text_en", "text_es", "text_ar", "text_fa",
    "text_zh", "text_ru", "text_pt",
    "hash_fr", "hash_en", "hash_es", "hash_ar", "hash_fa",
    "hash_zh", "hash_ru", "hash_pt",
]


def _write_csv(path, rows):
    with open(path, "w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        w.writeheader()
        for r in rows:
            w.writerow(r)


def _row(fr="", en="", es="", ar="", fa="", zh="", ru="", pt="", cell="cell1"):
    return {
        "notebook": "nb.ipynb", "cell_id": cell, "cell_type": "markdown",
        "src_lang": "fr", "src_hash": "x",
        "text_fr": fr, "text_en": en, "text_es": es, "text_ar": ar,
        "text_fa": fa, "text_zh": zh, "text_ru": ru, "text_pt": pt,
        "hash_fr": "", "hash_en": "", "hash_es": "", "hash_ar": "",
        "hash_fa": "", "hash_zh": "", "hash_ru": "", "hash_pt": "",
    }


# --- script detection -------------------------------------------------------

@pytest.mark.parametrize("lang,val,expected", [
    ("ru", "привет", True),       # Cyrillic present
    ("ru", "hello", False),       # Latin only, no Cyrillic
    ("ar", "مرحبا", True),        # Arabic present
    ("fa", "سلام", True),         # Arabic script (Persian)
    ("fa", "salâm (translit)", False),  # Latin translit, no Arabic glyph
    ("zh", "你好", True),          # CJK present
    ("zh", "ni hao", False),      # Latin only, no CJK
    ("en", "hello", True),        # Latin langs always pass
    ("pt", "olá", True),
])
def test_has_expected_script(lang, val, expected):
    assert mda.has_expected_script(lang, val) is expected


@pytest.mark.parametrize("lang,val,expected", [
    ("ru", "hello world", True),          # Latin leak into Cyrillic col
    ("ru", "привет world", False),         # has Cyrillic => not wrong-script
    ("zh", "not translated", True),        # Latin leak into CJK col
    ("zh", "未翻译 notrans", False),        # has CJK => not wrong-script
    ("ar", "", False),                     # empty => not flagged
    ("en", "anything", False),             # Latin lang => never wrong-script
    ("pt", "português", False),
])
def test_is_wrong_script(lang, val, expected):
    assert mda.is_wrong_script(lang, val) is expected


def test_norm_collapses_whitespace():
    assert mda.norm("  a\n  b  ") == "a b"
    assert mda.norm(None) == ""
    assert mda.norm("\t\t") == ""


# --- drift classification on a synthetic CSV --------------------------------

def test_missing_fr_filled_lang_empty(tmp_path):
    p = tmp_path / "t.csv"
    _write_csv(p, [_row(fr="Bonjour le monde", en="")])
    res = mda.audit_csv(str(p))
    assert res["counts"]["en"]["MISSING"] == 1
    assert res["counts"]["en"]["FR_CONTAM"] == 0
    # every other lang also MISSING (all empty)
    for lang in mda.LANGS:
        assert res["counts"][lang]["MISSING"] == 1


def test_fr_contam_untranslated_copy(tmp_path):
    p = tmp_path / "t.csv"
    text = "Ceci est un texte non traduit"   # len >= 4, identical
    _write_csv(p, [_row(fr=text, en=text)])
    res = mda.audit_csv(str(p))
    assert res["counts"]["en"]["FR_CONTAM"] == 1
    assert res["counts"]["en"]["MISSING"] == 0


def test_fr_contam_short_coincidence_not_drift(tmp_path):
    """A <=3-char identical value (e.g. 'ok', '1.') is not real FR_CONTAM."""
    p = tmp_path / "t.csv"
    _write_csv(p, [_row(fr="ok", en="ok")])   # len 2 < FR_CONTAM_MIN_LEN
    res = mda.audit_csv(str(p))
    assert res["counts"]["en"]["FR_CONTAM"] == 0


def test_orphan_lang_filled_fr_empty(tmp_path):
    p = tmp_path / "t.csv"
    _write_csv(p, [_row(fr="", en="orphan translation")])
    res = mda.audit_csv(str(p))
    assert res["counts"]["en"]["ORPHAN"] == 1
    assert res["counts"]["en"]["MISSING"] == 0  # FR empty => not MISSING


def test_empty_fr_empty_lang_neither(tmp_path):
    """Row with both FR and lang empty => neither MISSING nor ORPHAN."""
    p = tmp_path / "t.csv"
    _write_csv(p, [_row(fr="", en="")])
    res = mda.audit_csv(str(p))
    assert res["counts"]["en"]["MISSING"] == 0
    assert res["counts"]["en"]["ORPHAN"] == 0


def test_wrong_script_latin_leak_in_cjk(tmp_path):
    p = tmp_path / "t.csv"
    # FR present (so not MISSING), zh carries Latin leak (so WRONG_SCRIPT)
    _write_csv(p, [_row(fr="Texte français", zh="still in French")])
    res = mda.audit_csv(str(p))
    assert res["counts"]["zh"]["WRONG_SCRIPT"] == 1
    assert res["counts"]["zh"]["MISSING"] == 0


def test_genuine_translation_not_flagged(tmp_path):
    """A real translation (differs from FR, correct script) => no drift."""
    p = tmp_path / "t.csv"
    _write_csv(p, [_row(fr="Bonjour", en="Hello", zh="你好", ru="Привет")])
    res = mda.audit_csv(str(p))
    for lang in ["en", "zh", "ru"]:
        for cls in mda.CLASSES:
            assert res["counts"][lang][cls] == 0, f"{lang}/{cls} should be 0"


# --- aggregation ------------------------------------------------------------

def test_aggregate_sums_across_csvs(tmp_path):
    p1 = tmp_path / "a.csv"
    p2 = tmp_path / "b.csv"
    _write_csv(p1, [_row(fr="un", en=""), _row(fr="deux", en="")])
    _write_csv(p2, [_row(fr="trois", en="")])
    r1 = mda.audit_csv(str(p1))
    r2 = mda.audit_csv(str(p2))
    total = mda.aggregate([r1, r2])
    assert total["en"]["MISSING"] == 3
