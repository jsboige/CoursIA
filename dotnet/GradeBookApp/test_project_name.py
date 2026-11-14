"""Tests for GradeBookApp/gradebook.py::ProjectEvaluation.project_name / match_names.

Guards its heavy deps via ``pytest.importorskip`` so the suite skips cleanly in CI
(no GradeBookApp Python env) but runs on any machine that has the grading-engine
deps installed.

Covers regression #24246: ``project_name`` split on the literal space *before*
stripping, so a name written with a leading space (``" Dupont"``, as produced by
spreadsheet cells and CSV exports) yielded the empty key ``""`` instead of
``"dupon"``. ``match_names`` then failed against the registered ``"Dupont"`` record
and rule 3 of ``is_valid_evaluation`` discarded the evaluation of a perfectly
enrolled evaluator.
"""
import os
import sys
from datetime import datetime, timedelta
from types import SimpleNamespace

import pytest

# Make ``gradebook`` (sibling file) importable regardless of invocation cwd,
# since the repo root pytest.ini uses ``--import-mode importlib`` and does not
# put GradeBookApp/ on sys.path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

pytest.importorskip("pandas")
pytest.importorskip("numpy")
pytest.importorskip("unidecode")
pytest.importorskip("rapidfuzz")

from gradebook import ProjectEvaluation  # noqa: E402  (after importorskip guards)


def _person(nom, prenom):
    """Minimal stand-in for StudentRecord/EvaluationRecord: match_names only reads nom/prenom."""
    return SimpleNamespace(nom=nom, prenom=prenom)


@pytest.fixture()
def engine():
    return ProjectEvaluation("professeur@example.org", [])


# --- Le coeur du defaut #24246 -------------------------------------------------

def test_leading_space_name_matches_registered_student(engine):
    """Le test exige par l'issue : (" Dupont", "Jean") doit correspondre a ("Dupont", "Jean")."""
    assert engine.match_names(_person(" Dupont", "Jean"), _person("Dupont", "Jean")) is True


def test_leading_and_trailing_spaces_are_not_significant(engine):
    assert engine.project_name(" Dupont") == engine.project_name("Dupont") == "dupon"
    assert engine.project_name("Dupont ") == "dupon"
    assert engine.project_name("\tDupont\n") == "dupon"


def test_leading_space_on_first_name_matches(engine):
    assert engine.match_names(_person("Dupont", " Jean"), _person("Dupont", "Jean")) is True


def test_inverted_nom_prenom_with_leading_space_matches(engine):
    assert engine.match_names(_person(" Jean", " Dupont"), _person("Dupont", "Jean")) is True


# --- Gardes : pas de IndexError sur un nom vide --------------------------------

@pytest.mark.parametrize("blank", ["", "   ", "\t", "\n  \t"])
def test_blank_name_returns_empty_key(engine, blank):
    assert engine.project_name(blank) == ""


@pytest.mark.parametrize("not_a_string", [None, 123, 4.5, ["Dupont"]])
def test_non_string_returns_empty_key(engine, not_a_string):
    assert engine.project_name(not_a_string) == ""


# --- Contrat existant, fige pour ne pas le casser en corrigeant ----------------

def test_multiple_spaces_and_tabs_are_single_separators(engine):
    assert engine.project_name("Jean  Pierre") == "jean"
    assert engine.project_name("Jean\tPierre") == "jean"


def test_hyphenated_first_name_keeps_first_segment(engine):
    """Comportement d'origine : "Jean-Pierre" se ramene a "Jean"."""
    assert engine.project_name("Jean-Pierre") == "jean"


def test_accents_are_folded(engine):
    assert engine.project_name("Élodie") == engine.project_name("Elodie") == "elodi"


def test_truncation_to_five_characters_is_unchanged(engine):
    assert engine.project_name("Dupont") == "dupon"


def test_distinct_names_do_not_match(engine):
    assert engine.match_names(_person("Dupont", "Jean"), _person("Martin", "Jean")) is False


# --- Effet de bord mesure : la regle 3 ne doit plus ecarter l'evaluation -------

def _group_evaluation(groupe="G1", date=None):
    return SimpleNamespace(groupe=groupe, date=date or datetime(2026, 1, 15, 10, 0), group_members=[])


def _evaluation(nom, prenom, email, date, note=12.0, is_teacher=False):
    return SimpleNamespace(
        nom=nom,
        prenom=prenom,
        email=email,
        date=date,
        note=note,
        is_teacher=is_teacher,
    )


def test_rule3_now_accepts_enrolled_evaluator_with_leading_space():
    """Preuve de bout en bout : l'evaluation d'un inscrit ecrit " Dupont" est conservee."""
    records = [_person("Dupont", "Jean"), _person("Martin", "Alice")]
    engine = ProjectEvaluation("professeur@example.org", records)
    group = _group_evaluation()
    evaluation = _evaluation(" Dupont", "Jean", "jean.dupont@example.org", group.date)

    assert engine.is_valid_evaluation(group, evaluation, seen_evaluators=set()) is True


def test_rule3_still_rejects_unregistered_evaluator():
    """Controle negatif : la regle 3 garde son effet sur un evaluateur non inscrit."""
    records = [_person("Dupont", "Jean")]
    engine = ProjectEvaluation("professeur@example.org", records)
    group = _group_evaluation()
    evaluation = _evaluation("Inconnu", "Bob", "bob@example.org", group.date)

    assert engine.is_valid_evaluation(group, evaluation, seen_evaluators=set()) is False


def test_rule3_date_tolerance_unaffected():
    """La regle 2 (dates) n'est pas touchee par ce correctif."""
    records = [_person("Dupont", "Jean")]
    engine = ProjectEvaluation("professeur@example.org", records)
    group = _group_evaluation(date=datetime(2026, 1, 15, 10, 0))
    late = _evaluation(" Dupont", "Jean", "jean.dupont@example.org", group.date + timedelta(hours=6))

    assert engine.is_valid_evaluation(group, late, seen_evaluators=set()) is False
