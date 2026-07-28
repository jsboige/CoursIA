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

Extension #6949 point 1 (signal honnete de taux de remplissage) : un
``SRC_DRIFT=0`` sur une table 0% traduite se lisait a tort comme « a jour ».
``csv_fill_stats`` + ``_format_fill_line`` exposent le taux de remplissage par
langue a cote du compte de drift, pour qu'un compteur nu cesse d'etre lu comme
un achevement. Couverture : denominateur (rows bien formees seules), pivot fr
toujours 100%, suffixe « AUCUNE traduction deposee » quand toutes cibles a 0%.

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


# ---------------------------------------------------------------------------
# #6949 point 1 — taux de remplissage (signal honnete)
# ---------------------------------------------------------------------------

def _write_fill_csv(csv_path, rows):
    """Ecrit un CSV multi-rows pour ``csv_fill_stats``.

    ``rows`` = liste de dicts ``{lang: text}``. Le pivot ``fr`` est toujours
    rempli (notebook source) ; les cibles ne le sont que si la row le dit.
    Une row ``None`` produit une ligne malformee (``cell_id`` vide) pour tester
    l'exclusion du denominateur.
    """
    fields = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash"]
    fields += [f"text_{l}" for l in C.ALL_LANGS]
    fields += [f"hash_{l}" for l in C.ALL_LANGS]
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for i, row in enumerate(rows):
            d = {k: "" for k in fields}
            d["notebook"] = "nb.ipynb"
            if row is None:  # row malformée (cell_id vide) -> doit etre exclue du denominateur
                d["cell_id"] = ""
                w.writerow(d)
                continue
            d["cell_id"] = f"cell{i}"
            d["text_fr"] = "source fr"  # pivot toujours rempli
            for lang, txt in row.items():
                d[f"text_{lang}"] = txt
            w.writerow(d)


def test_csv_fill_stats_all_zero(tmp_path):
    """Table sans aucune traduction : pivot 100%, toutes cibles 0%."""
    csv_path = tmp_path / "fill.csv"
    _write_fill_csv(csv_path, [{}, {}])  # 2 rows, fr seulement
    stats = C.csv_fill_stats(csv_path)
    assert stats["fr"] == {"filled": 2, "total": 2}
    for lang in C.TARGET_LANGS:
        assert stats[lang] == {"filled": 0, "total": 2}, f"{lang} should be 0/2"


def test_csv_fill_stats_fully_translated(tmp_path):
    """Table 100% traduite sur 2 cibles : 2/2 pour ces cibles."""
    csv_path = tmp_path / "fill.csv"
    _write_fill_csv(csv_path, [{"en": "x", "es": "y"}, {"en": "x", "es": "y"}])
    stats = C.csv_fill_stats(csv_path)
    assert stats["en"] == {"filled": 2, "total": 2}
    assert stats["es"] == {"filled": 2, "total": 2}
    # les autres cibles restent à 0
    assert stats["zh"] == {"filled": 0, "total": 2}


def test_csv_fill_stats_partial(tmp_path):
    """1 traduction en sur 2 rows -> 1/2 (le denominateur se voit)."""
    csv_path = tmp_path / "fill.csv"
    _write_fill_csv(csv_path, [{"en": "x"}, {}])
    stats = C.csv_fill_stats(csv_path)
    assert stats["en"] == {"filled": 1, "total": 2}


def test_csv_fill_stats_malformed_rows_excluded(tmp_path):
    """Une row malformée (cell_id vide) n'entre pas dans le dénominateur.

    Discipline #6949 : le dénominateur = cellules bien formées que le CSV
    référence. Une row cassée ne gonfle pas artificiellement le total.
    """
    csv_path = tmp_path / "fill.csv"
    _write_fill_csv(csv_path, [{}, None, {}])  # 2 valides + 1 malformée
    stats = C.csv_fill_stats(csv_path)
    assert stats["fr"]["total"] == 2  # pas 3


def test_format_fill_line_zero_suffix(tmp_path):
    """Toutes cibles à 0% -> suffixe 'AUCUNE traduction déposée'."""
    stats = {lang: {"filled": 0, "total": 5} for lang in C.ALL_LANGS}
    stats["fr"] = {"filled": 5, "total": 5}
    line = C._format_fill_line(stats)
    assert "AUCUNE traduction déposée" in line
    assert "en=0.0%" in line
    assert "5 cellules" in line


def test_format_fill_line_no_suffix_when_translated():
    """Au moins une cible > 0% -> pas de suffixe, pct réelle affichée."""
    stats = {lang: {"filled": 0, "total": 2} for lang in C.ALL_LANGS}
    stats["fr"] = {"filled": 2, "total": 2}
    stats["en"] = {"filled": 1, "total": 2}
    line = C._format_fill_line(stats)
    assert "AUCUNE" not in line
    assert "en=50.0%" in line


# ──────────────────────────────────────────────────────────────────────────
# _fill_pct — floor anti-arrondi (ride ai-01 c.33 : fr=100.0% pour 24469/24470)
# ──────────────────────────────────────────────────────────────────────────

def test_fill_pct_floors_below_100_when_not_complete():
    """24469/24470 ne doit PAS s'afficher 100.0% (ride #6949, ai-01 c.33).

    ``round(99.9959, 1)`` -> ``100.0`` : dans un outil dont la raison d'être
    est qu'un compteur n'affirme plus faussement la complétude, l'arrondi
    refait le défaut un ordre plus bas. Le floor garde le pct sous le seuil.
    """
    assert C._fill_pct(24469, 24470) == 99.9
    assert C._fill_pct(24469, 24470) != 100.0


def test_fill_pct_100_only_when_complete():
    """100.0 uniquement si filled == total exactement."""
    assert C._fill_pct(24470, 24470) == 100.0
    assert C._fill_pct(2, 2) == 100.0
    # un de moins -> déjà sous le seuil
    assert C._fill_pct(1, 2) == 50.0


def test_fill_pct_zero_when_no_total():
    """total=0 (table vide) -> 0.0, pas de ZeroDivisionError."""
    assert C._fill_pct(0, 0) == 0.0


def test_format_fill_line_floors_incomplete_target_below_100():
    """Une cible à 24469/24470 s'affiche ``99.9%``, jamais ``100.0%``.

    Exerce le path stderr ``_format_fill_line`` (qui n'affiche que les cibles,
    pas le pivot fr) avec le floor anti-arrondi. Reproduit la ride #6949
    signalée par ai-01 c.33 au niveau de la ligne lisible.
    """
    stats = {lang: {"filled": 0, "total": 24470} for lang in C.ALL_LANGS}
    stats["fr"] = {"filled": 24470, "total": 24470}
    stats["en"] = {"filled": 24469, "total": 24470}
    line = C._format_fill_line(stats)
    assert "en=99.9%" in line
    assert "en=100.0%" not in line
