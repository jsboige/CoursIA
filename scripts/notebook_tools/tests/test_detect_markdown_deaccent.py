"""Acceptance tests for scripts/notebook_tools/detect_markdown_deaccent.py

The #14064 hardening is validated by FALSE NEGATIVES, never by hits (the
issue's explicit rule: "le durcissement se valide par ses faux négatifs ...
jamais par ses hits"). So the suite pins the forms the instrument MUST catch
and the homographs it MUST NOT auto-flag, plus the FR/EN prose gate.

Pure functions with tmp_path fixtures -- no I/O on the real repo.
"""

import json
import sys
from pathlib import Path

import pytest

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import detect_markdown_deaccent as dmd
from detect_markdown_deaccent import (
    EN_COGNAT_EXCLUSIONS,
    FR_STOPWORDS,
    EN_STOPWORDS,
    HOMOGRAPH_EXCLUSIONS,
    find_candidates,
)


def _write_nb(path: Path, cells: list[dict]) -> Path:
    """Write a minimal nbformat-4 notebook with the given cells to path."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": [source]}


def _notebook(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# --- False negatives: the forms the instrument MUST catch (issue §acceptance) --

ACCEPTANCE_FORMS = ["theoreme", "etat", "donnees", "equilibre", "entrainement"]


def test_acceptance_forms_not_excluded():
    """The 5 mandated forms must never be silently excluded by a list."""
    for form in ACCEPTANCE_FORMS:
        assert form not in HOMOGRAPH_EXCLUSIONS, (
            f"{form} should be auto-flagged, but it is in HOMOGRAPH_EXCLUSIONS"
        )
        assert form not in EN_COGNAT_EXCLUSIONS, (
            f"{form} should be auto-flagged, but it is in EN_COGNAT_EXCLUSIONS"
        )


def test_false_negatives_caught():
    """A French notebook with the 5 forms (accented twin present) → auto-flagged."""
    accented = "Le théorème de Sen, l'état stable, les données, un équilibre et l'entraînement."
    unaccented = "Le theoreme est faux; l'etat change; les donnees manquent; un equilibre existe; l'entrainement dure."
    nb = _notebook([_md(accented), _md(unaccented)])
    result = find_candidates(nb)
    assert result["language"] == "fr", "this notebook must classify as French prose"
    for form in ACCEPTANCE_FORMS:
        assert form in result["auto"], (
            f"false negative: {form} must be auto-flagged, got auto={sorted(result['auto'])}"
        )


def test_homographs_never_auto_flagged():
    """des/sur/mesure/mesures are legitimately-different words → homograph bucket,
    never auto-flagged, even when the accented twin (dès/sûr/mesuré/mesurés) appears."""
    accented = "Dès le départ il est sûr, un résultat mesuré; des mesures précises."
    unaccented = "le des partitif, sur la table, une mesure exacte, ces mesures."
    nb = _notebook([_md(accented), _md(unaccented)])
    result = find_candidates(nb)
    assert result["language"] == "fr"
    for form in ("des", "sur", "mesure", "mesures"):
        assert form not in result["auto"], (
            f"homograph {form} must NOT be auto-flagged"
        )
    # They ARE reported, but only as homographs (transparency, not defects).
    assert "mesure" in result["homograph"] or "mesures" in result["homograph"]


def test_english_notebook_gate_skips():
    """English-dominant prose → language=en, desaccented word with accented twin
    present is NOT flagged (the FR/EN gate prevents false positives on EN prose)."""
    en_prose = "The state is stable and the theorem is true. The etat here."
    accented_twin = "état"
    nb = _notebook([_md(en_prose), _md(accented_twin)])
    result = find_candidates(nb)
    assert result["language"] == "en", (
        f"expected en, got {result['language']}"
    )
    assert "etat" not in result["auto"], (
        "an English-dominant notebook must not flag a desaccented word"
    )
    assert result["auto"] == {}


def test_inline_code_not_flagged():
    """A desaccented word inside an inline-code span is not prose → ignored."""
    accented = "le théorème de Sen"
    code = "use `theoreme` as an identifier here"
    nb = _notebook([_md(accented), _md(code)])
    result = find_candidates(nb)
    assert "theoreme" not in result["auto"]


def test_english_cognat_excluded():
    """An English technical cognat (e.g. detection) with an accented French twin
    (détection) is NOT auto-flagged -- it is a legitimately unaccented EN term."""
    accented = "la détection d'anomalies est l'objectif"
    unaccented = "l'etape de detection est cruciale"
    nb = _notebook([_md(accented), _md(unaccented)])
    result = find_candidates(nb)
    assert "detection" not in result["auto"]


# --- Language gate: the stopword sets are non-empty and disjoint enough to be
# --- a real signal (guards against a later accidental emptying of the lists). --


def test_language_stopwords_nonempty():
    assert len(FR_STOPWORDS) > 20
    assert len(EN_STOPWORDS) > 20


def test_french_stopword_shared_word_not_in_both_notably():
    """A word used as an FR stopword should not be double-qualifying as EN. This is
    a soft guard: `sur` is an FR preposition and happens to be `sur` as a verb; the
    gate only needs *relative* dominance, but a single word dominating both sets
    would mute the signal."""
    overlap = FR_STOPWORDS & EN_STOPWORDS
    # `on`, `sur`, `des` are legitimate in both; allow a tiny overlap but not a
    # large one that would let a single word decide both directions.
    assert len(overlap) < 5, f"FR/EN stopword overlap too large: {sorted(overlap)}"
