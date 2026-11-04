"""Tests for GradeBookApp/gradebook.py::ProjectEvaluation.evaluator_key (règle 5).

Guards its heavy deps via ``pytest.importorskip`` so the suite skips cleanly in CI
(no GradeBookApp Python env) but runs on any machine that has the grading-engine
deps installed.

Covers regression #24276: rule 5 (rejet des évaluations doubles) took the raw
address as its key, in a plain ``set`` -- case- and whitespace-sensitive, while
the C# mirror (``ProjectModel.cs``) compares with
``StringComparer.OrdinalIgnoreCase``. Two evaluations of the same evaluator
written ``Jean.Dupont@example.org`` and `` jean.dupont@example.org `` were both
accepted and counted twice in the group average.

The end-to-end tests go through ``filter_evaluations``, not through
``is_valid_evaluation`` alone: the defect class is a *pair* of call sites (the
lookup and the ``seen_evaluators.add``), and a unit test on one side would pass
while the two disagreed.
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

from gradebook import GroupEvaluation, ProjectEvaluation  # noqa: E402

BASE_DATE = datetime(2026, 1, 15, 10, 0)


def _person(nom, prenom):
    """Stand-in pour StudentRecord : match_names ne lit que nom/prenom."""
    return SimpleNamespace(nom=nom, prenom=prenom)


def _evaluation(nom, prenom, email, offset_minutes=0, note=12.0, is_teacher=False):
    return SimpleNamespace(
        nom=nom,
        prenom=prenom,
        email=email,
        date=BASE_DATE + timedelta(minutes=offset_minutes),
        note=note,
        is_teacher=is_teacher,
    )


def _filtered(evaluations):
    """Fait tourner la vraie chaîne de filtrage et rend les évaluations conservées."""
    records = [_person("Dupont", "Jean"), _person("Martin", "Alice"), _person("Durand", "Paul")]
    engine = ProjectEvaluation("professeur@example.org", records)
    # Membre du groupe distinct des évaluateurs des tests : la règle 4 écarterait
    # l'auto-évaluation et fausserait le décompte.
    members = [_person("Durand", "Paul")]
    group = GroupEvaluation("G1", list(evaluations), members)
    engine.grouped_evaluations = [group]
    engine.filter_evaluations()
    return group.evaluations


# --- Critère d'acceptation 1 : casse et espaces ne font pas deux évaluateurs ---

def test_case_only_email_difference_is_a_duplicate():
    kept = _filtered([
        _evaluation("Dupont", "Jean", "Jean.Dupont@Example.org", 0),
        _evaluation("Dupont", "Jean", "jean.dupont@example.org", 60),
    ])
    assert len(kept) == 1


def test_surrounding_whitespace_in_email_is_a_duplicate():
    kept = _filtered([
        _evaluation("Dupont", "Jean", " jean.dupont@example.org ", 0),
        _evaluation("Dupont", "Jean", "jean.dupont@example.org", 60),
    ])
    assert len(kept) == 1


def test_case_and_whitespace_together_is_a_duplicate():
    kept = _filtered([
        _evaluation("Dupont", "Jean", "JEAN.DUPONT@EXAMPLE.ORG", 0),
        _evaluation("Dupont", "Jean", "  jean.dupont@example.org\t", 60),
    ])
    assert len(kept) == 1


def test_first_of_the_two_duplicates_is_the_one_kept():
    """La règle trie par date : c'est l'évaluation la plus ancienne qui survit."""
    first = _evaluation("Dupont", "Jean", "jean.dupont@example.org", 0, note=15.0)
    second = _evaluation("Dupont", "Jean", "Jean.Dupont@example.org", 60, note=8.0)
    kept = _filtered([second, first])
    assert kept == [first]


# --- Critère d'acceptation 2 : contrôle négatif, pas de sur-rejet -------------

def test_genuinely_different_emails_are_both_kept():
    kept = _filtered([
        _evaluation("Dupont", "Jean", "jean.dupont@example.org", 0),
        _evaluation("Martin", "Alice", "alice.martin@example.org", 60),
    ])
    assert len(kept) == 2


def test_similar_but_distinct_local_parts_are_not_duplicates():
    kept = _filtered([
        _evaluation("Dupont", "Jean", "jean.dupont@example.org", 0),
        _evaluation("Dupont", "Jean", "jean.dupont2@example.org", 60),
    ])
    assert len(kept) == 2


# --- Critère d'acceptation 3 : repli sur le nom, comme le miroir C# -----------

@pytest.mark.parametrize("absent", [None, "", "   ", float("nan")])
def test_missing_email_rows_of_the_same_evaluator_are_duplicates(absent):
    kept = _filtered([
        _evaluation("Dupont", "Jean", absent, 0),
        _evaluation("Dupont", "Jean", absent, 60),
    ])
    assert len(kept) == 1


@pytest.mark.parametrize("absent", [None, "", "   ", float("nan")])
def test_missing_email_rows_of_different_evaluators_are_both_kept(absent):
    """Sans repli sur le nom, toutes les lignes sans adresse partageaient une clé
    unique et une seule évaluation par groupe était retenue."""
    kept = _filtered([
        _evaluation("Dupont", "Jean", absent, 0),
        _evaluation("Martin", "Alice", absent, 60),
    ])
    assert len(kept) == 2


def test_name_fallback_ignores_case_and_accents():
    kept = _filtered([
        _evaluation("Dupont", "Jean", None, 0),
        _evaluation("DUPONT", "jean", None, 60),
    ])
    assert len(kept) == 1


# --- Contrat de la clé elle-même ---------------------------------------------

@pytest.fixture()
def engine():
    return ProjectEvaluation("professeur@example.org", [])


def test_key_normalizes_case_and_whitespace(engine):
    key = engine.evaluator_key(_evaluation("Dupont", "Jean", "  Jean.Dupont@Example.org  "))
    assert key == ("email", "jean.dupont@example.org")


def test_key_is_identical_for_the_two_spellings(engine):
    assert engine.evaluator_key(
        _evaluation("Dupont", "Jean", "Jean.Dupont@Example.org")
    ) == engine.evaluator_key(
        _evaluation("Dupont", "Jean", " jean.dupont@example.org ")
    )


def test_key_falls_back_to_name_when_email_is_not_usable(engine):
    key = engine.evaluator_key(_evaluation("Dupont", "Jean", None))
    assert key == ("nom", "dupont", "jean")


def test_key_falls_back_to_name_when_email_is_not_a_string(engine):
    assert engine.evaluator_key(_evaluation("Dupont", "Jean", 42)) == ("nom", "dupont", "jean")


def test_key_of_a_nameless_row_does_not_raise(engine):
    assert engine.evaluator_key(_evaluation(float("nan"), float("nan"), None)) == ("nom", "", "")


# --- Ce que le correctif ne change pas ---------------------------------------

def test_rules_1_to_4_are_untouched():
    """Le correctif ne porte que sur la règle 5 : une note invalide reste écartée."""
    kept = _filtered([_evaluation("Dupont", "Jean", "jean.dupont@example.org", 0, note=20.0)])
    assert kept == []
