"""Tests pour scripts/translation/sync_translation_perimeter.py (c.199 / #10329 etape 2).

Couvre les fonctions pures (stdlib only, hermetiques via tmp_path) :
- _resolve_perimeter : LCP depth-first, coverage 100% requise
- _target_cols_lost : aucune traduction T3 perdue sur update legitime
- _target_cols_lost : detecte une perte simulee (defense anti-regression)

Les fonctions qui dependent du repo reel (measure_csvs) sont integrees via
DRY-RUN dans le test smoke ; les tests purs ci-dessous couvrent les invariants.
"""

import csv
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import sync_translation_perimeter as s  # noqa: E402


# --------------------------------------------------------------------------
# Helpers — synthetic CSV with controlled notebook paths
# --------------------------------------------------------------------------

def _write_csv(tmp_path, name, notebooks):
    """Construit un CSV minimal avec une colonne 'notebook' par ligne."""
    p = tmp_path / name
    fieldnames = ["notebook", "cell_id", "cell_type", "src_lang", "src_hash",
                  "text_fr", "hash_fr", "text_en", "hash_en",
                  "text_es", "hash_es", "text_ar", "hash_ar",
                  "text_fa", "hash_fa", "text_zh", "hash_zh",
                  "text_ru", "hash_ru", "text_pt", "hash_pt"]
    with p.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, quoting=csv.QUOTE_MINIMAL)
        writer.writeheader()
        for nb in notebooks:
            writer.writerow({col: "" for col in fieldnames} | {"notebook": nb})
    return p


# --------------------------------------------------------------------------
# _resolve_perimeter — LCP depth-first
# --------------------------------------------------------------------------

def test_resolve_perimeter_basic_lcp(tmp_path):
    """LCP le plus profond couvrant 100% des notebooks."""
    csv_path = _write_csv(tmp_path, "x.csv", [
        "MyIA.AI.Notebooks/GameTheory/GameTheory-1.ipynb",
        "MyIA.AI.Notebooks/GameTheory/GameTheory-10.ipynb",
        "MyIA.AI.Notebooks/GameTheory/SocialChoice/SocialChoice-1.ipynb",
    ])
    perim, nb_count = s._resolve_perimeter(csv_path)
    assert perim == "MyIA.AI.Notebooks/GameTheory/"
    assert nb_count == 3


def test_resolve_perimeter_separates_genai_subdirs(tmp_path):
    """genai/audio ne doit PAS englober genai/image (regression guard)."""
    csv_path = _write_csv(tmp_path, "audio.csv", [
        "MyIA.AI.Notebooks/GenAI/Audio/01-1-Intro.ipynb",
        "MyIA.AI.Notebooks/GenAI/Audio/02-1-Advanced.ipynb",
    ])
    perim, _ = s._resolve_perimeter(csv_path)
    assert perim == "MyIA.AI.Notebooks/GenAI/Audio/", perim


def test_resolve_perimeter_separates_search_parts(tmp_path):
    """search-part1 vs search-part2 = perimetres distincts."""
    csv1 = _write_csv(tmp_path, "p1.csv", [
        "MyIA.AI.Notebooks/Search/Part1-Foundations/A.ipynb",
        "MyIA.AI.Notebooks/Search/Part1-Foundations/B.ipynb",
    ])
    csv2 = _write_csv(tmp_path, "p2.csv", [
        "MyIA.AI.Notebooks/Search/Part2-CSP/X.ipynb",
    ])
    perim1, _ = s._resolve_perimeter(csv1)
    perim2, _ = s._resolve_perimeter(csv2)
    assert perim1 == "MyIA.AI.Notebooks/Search/Part1-Foundations/"
    assert perim2 == "MyIA.AI.Notebooks/Search/Part2-CSP/"
    assert perim1 != perim2


def test_resolve_perimeter_empty_csv(tmp_path):
    csv_path = _write_csv(tmp_path, "empty.csv", [])
    perim, nb_count = s._resolve_perimeter(csv_path)
    assert perim == ""
    assert nb_count == 0


# --------------------------------------------------------------------------
# _target_cols_lost — defense anti-regression sur les colonnes T3
# --------------------------------------------------------------------------

def _row(notebook, cell_id, text_en=""):
    return {
        "notebook": notebook,
        "cell_id": cell_id,
        "cell_type": "markdown",
        "src_lang": "fr",
        "src_hash": "abc",
        "text_fr": "fr",
        "hash_fr": "abc",
        "text_en": text_en,
        "hash_en": "x" if text_en else "",
    }


def test_target_cols_lost_zero_on_legitimate_update():
    """Update qui preserve text_en (cas normal) -> 0 perte."""
    existing = [
        _row("n1.ipynb", "c1", text_en="Hello"),
        _row("n1.ipynb", "c2", text_en=""),
    ]
    updated = [
        _row("n1.ipynb", "c1", text_en="Hello"),  # preserved
        _row("n1.ipynb", "c2", text_en=""),       # vide avant, vide apres
    ]
    assert s._target_cols_lost(existing, updated) == 0


def test_target_cols_lost_detects_simulated_loss():
    """Si text_en et hash_en etaient remplis avant et vides apres -> perte detectee.

    Note : _target_cols() inclut `text_<lang>` ET `hash_<lang>` pour chaque
    langue cible (cf. docstring). Une seule cellule scrubbee detruit donc 2
    champs par langue, et c'est bien 2 qu'on attend ici (text_en + hash_en).
    """
    existing = [_row("n1.ipynb", "c1", text_en="Hello")]
    updated = [_row("n1.ipynb", "c1", text_en="")]  # text_en + hash_en scrubbes
    assert s._target_cols_lost(existing, updated) == 2


def test_target_cols_lost_ignores_disappeared_cells():
    """Une ligne qui disparait (ORPHAN_ROW) n'est PAS une perte T3."""
    existing = [_row("n1.ipynb", "c1", text_en="Hello")]
    updated = []  # ligne disparue
    assert s._target_cols_lost(existing, updated) == 0


def test_target_cols_lost_ignores_preserved_empty_cells():
    """text_en vide avant et vide apres -> pas une perte."""
    existing = [_row("n1.ipynb", "c1", text_en="")]
    updated = [_row("n1.ipynb", "c1", text_en="")]
    assert s._target_cols_lost(existing, updated) == 0


# --------------------------------------------------------------------------
# Smoke test : l'integration resolve_csv_paths tient debout
# --------------------------------------------------------------------------

def test_resolve_csv_paths_finds_csvs():
    """_resolve_csv_paths() trouve au moins un CSV dans translations/.
    Pas de monkeypatch cwd : on utilise CWD par defaut (le repo) qui contient
    bien translations/. Ce test documente la pre-condition minimale.
    """
    raw = s._resolve_csv_paths([Path("translations")], Path.cwd())
    assert isinstance(raw, list)
    # Le repo CoursIA-2 a 33+ CSV ; si ce test echoue, on n'est pas dans le repo.
    assert len(raw) >= 30, f"Trouve seulement {len(raw)} CSV (repo pas charge ?)"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])