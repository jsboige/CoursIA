"""Regression suite for ``scripts/translation/check_translation_sync.py`` (c.734, #6949).

Background. ``check_translation_sync.py`` (notre T2 de l EPIC #6949) detectait
4 classes de drift (IN_SYNC / SRC_DRIFT / TRAD_DRIFT / MISSING_LANG / ORPHAN_ROW)
mais manquait la 3e des 5 classes Argumentum : **WRONG_SCRIPT** -- un contenu
``text_<lang>`` depose pour une langue non-Latine (ar/fa/zh/ru) sans AUCUN
caractere du script Unicode attendu (typiquement un copier-coller de FR ou d EN
dans la mauvaise colonne). C.734 ajoute le verdict ``WRONG_SCRIPT`` via la
detection deterministe ``_has_expected_script`` (plages Unicode UCD).

Cette suite couvre :

  * ``_has_expected_script`` (unite) : chaque langue non-Latine OK/WRONG,
    ASCII-seul = WRONG, langues Latines (en/es/pt) jamais WRONG, texte vide = OK.
  * ``check_csv`` (integration) : un CSV synthetique avec ``text_zh="bonjour"``
    produit un verdict ``WRONG_SCRIPT`` ; avec ``text_zh="你好"`` -> aucun.

G.9 non-vacuous : contre le ``check_translation_sync.py`` d origin/main (sans le
verdict WRONG_SCRIPT ni la fonction ``_has_expected_script``), les tests
d import et de detection FAIL (ImportError sur ``_has_expected_script`` /
aucune anomalie WRONG_SCRIPT remontee), donc la suite garde le fix.

Run: ``python -m pytest scripts/tests/test_check_translation_sync.py -q``
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "translation"))

import check_translation_sync as C  # noqa: E402


def test_arabic_text_has_arabic_script():
    assert C._has_expected_script("ar", "مرحبا بكم") is True


def test_chinese_text_has_cjk_script():
    assert C._has_expected_script("zh", "你好世界") is True


def test_russian_text_has_cyrillic_script():
    assert C._has_expected_script("ru", "Привет мир") is True


def test_persian_text_has_arabic_script():
    assert C._has_expected_script("fa", "سلام دنیا") is True


def test_non_latin_text_with_ascii_payload_still_ok():
    assert C._has_expected_script("zh", "你好 world 123") is True
    assert C._has_expected_script("ar", "code: print(x) مرحبا") is True


def test_zh_latin_only_is_wrong_script():
    assert C._has_expected_script("zh", "bonjour") is False


def test_ar_latin_only_is_wrong_script():
    assert C._has_expected_script("ar", "bonjour") is False


def test_ru_latin_only_is_wrong_script():
    assert C._has_expected_script("ru", "bonjour") is False


def test_fa_latin_only_is_wrong_script():
    assert C._has_expected_script("fa", "bonjour") is False


def test_ascii_only_payload_is_wrong_script():
    assert C._has_expected_script("zh", "123 hello **bold**") is False


def test_markdown_wrapped_latin_is_wrong_script():
    assert C._has_expected_script("zh", "# Titre\n\n- item\n- item") is False


def test_latin_langs_never_wrong_script():
    for lang in ("en", "es", "pt"):
        assert C._has_expected_script(lang, "anything in French here") is True


def test_empty_text_is_not_wrong_script():
    for lang in ("ar", "zh", "ru", "fa", "en"):
        assert C._has_expected_script(lang, "") is True


def test_unknown_lang_is_not_wrong_script():
    assert C._has_expected_script("xx", "anything") is True


def _write_source_notebook(repo_root, nb_name, cell_id, source):
    nb_rel = f"tmp_{nb_name}.ipynb"
    (repo_root / nb_rel).write_text(
        json.dumps(
            {"cells": [{"id": cell_id, "cell_type": "markdown", "source": [source]}],
             "metadata": {}, "nbformat": 4, "nbformat_minor": 5},
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )
    return nb_rel


def _write_csv(csv_path, nb_rel, cell_id, texts):
    row = {
        "notebook": nb_rel, "cell_id": cell_id, "cell_type": "markdown",
        "src_lang": "fr", "src_hash": "", "text_fr": "Bonjour",
    }
    for lang in C.ALL_LANGS:
        row.setdefault(f"text_{lang}", "")
        row.setdefault(f"hash_{lang}", "")
    for lang, txt in texts.items():
        row[f"text_{lang}"] = txt
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(row.keys()))
        w.writeheader()
        w.writerow(row)


def test_check_csv_flags_wrong_script_zh(tmp_path):
    nb_rel = _write_source_notebook(tmp_path, "nb1", "abc", "Bonjour")
    csv_path = tmp_path / "sync.csv"
    _write_csv(csv_path, nb_rel, "abc", {"zh": "bonjour"})
    anomalies = C.check_csv(csv_path, tmp_path)
    wrong = [a for a in anomalies if a["verdict"] == "WRONG_SCRIPT"]
    assert len(wrong) == 1, f"expected 1 WRONG_SCRIPT, got {anomalies}"
    assert wrong[0]["lang"] == "zh"


def test_check_csv_no_wrong_script_for_correct_zh(tmp_path):
    nb_rel = _write_source_notebook(tmp_path, "nb2", "abc", "Bonjour")
    csv_path = tmp_path / "sync.csv"
    _write_csv(csv_path, nb_rel, "abc", {"zh": "你好"})
    anomalies = C.check_csv(csv_path, tmp_path)
    assert not any(a["verdict"] == "WRONG_SCRIPT" for a in anomalies)


def test_check_csv_wrong_script_all_non_latin(tmp_path):
    nb_rel = _write_source_notebook(tmp_path, "nb3", "abc", "Bonjour")
    csv_path = tmp_path / "sync.csv"
    _write_csv(csv_path, nb_rel, "abc", {"ar": "bonjour", "fa": "bonjour",
                                          "zh": "bonjour", "ru": "bonjour",
                                          "en": "bonjour", "es": "bonjour", "pt": "bonjour"})
    anomalies = C.check_csv(csv_path, tmp_path)
    wrong = [a for a in anomalies if a["verdict"] == "WRONG_SCRIPT"]
    wrong_langs = sorted(a["lang"] for a in wrong)
    assert wrong_langs == ["ar", "fa", "ru", "zh"], (
        f"expected ar/fa/ru/zh flagged, got {wrong_langs} (full={anomalies})"
    )


def test_check_csv_empty_text_no_wrong_script(tmp_path):
    nb_rel = _write_source_notebook(tmp_path, "nb4", "abc", "Bonjour")
    csv_path = tmp_path / "sync.csv"
    _write_csv(csv_path, nb_rel, "abc", {"zh": ""})
    anomalies = C.check_csv(csv_path, tmp_path)
    assert not any(a["verdict"] == "WRONG_SCRIPT" for a in anomalies)
