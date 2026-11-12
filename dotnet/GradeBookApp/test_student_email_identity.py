"""Tests ciblés de l'identité secondaire par e-mail, issue #24357."""
import os
import sys
from datetime import datetime
from types import SimpleNamespace

import pytest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

pytest.importorskip("pandas")
pytest.importorskip("numpy")
pytest.importorskip("unidecode")
pytest.importorskip("rapidfuzz")

from gradebook import (  # noqa: E402
    ProjectEvaluation,
    StudentRecord,
    get_ambiguity_journal,
    load_student_records,
    load_students_with_multiple_groups,
    reset_ambiguity_journal,
)
from run_grading import EXIT_AMBIGUITIES_PENDING, report_ambiguity_gate  # noqa: E402


@pytest.fixture(autouse=True)
def clean_ambiguity_journal():
    reset_ambiguity_journal()
    yield
    reset_ambiguity_journal()


def _person(nom, prenom, email=None):
    return SimpleNamespace(nom=nom, prenom=prenom, email=email)


def _engine(students):
    return ProjectEvaluation("professeur@example.org", students)


def test_email_is_optional_and_does_not_shift_existing_constructor_arguments():
    old_call = StudentRecord("Jean", "Dupont", "Projet")
    newer_call = StudentRecord("Alice", "Martin", "P1", "P2", " a@example.org ")

    assert old_call.email is None
    assert old_call.sujets == ["Projet"]
    assert newer_call.sujets == ["P1", "P2"]
    assert newer_call.email == " a@example.org "


def test_registered_evaluator_can_match_by_normalized_email_when_name_differs():
    engine = _engine([StudentRecord("Jean", "Dupont", "P1", email=" Jean.Dupont@Example.org ")])

    assert engine.is_registered_evaluator(_person("Nom saisi", "Différent", "  jean.dupont@example.org\t"))


def test_nominal_match_remains_valid_without_roster_or_evaluation_email():
    engine = _engine([StudentRecord("Jean", "Dupont", "P1")])

    assert engine.is_registered_evaluator(_person("Dupont", "Jean", None))
    assert not get_ambiguity_journal().has_ambiguities


@pytest.mark.parametrize("invalid_email", [None, "", "  ", float("nan"), 42, 4.2])
def test_non_string_or_missing_evaluation_email_is_never_an_identity(invalid_email):
    engine = _engine([StudentRecord("Autre", "Personne", "P1", email="42")])

    assert not engine.is_registered_evaluator(_person("Inconnu", "Personne", invalid_email))
    assert not get_ambiguity_journal().has_ambiguities


@pytest.mark.parametrize("roster_email", [None, "", "  ", float("nan"), 42])
def test_non_string_or_missing_roster_email_is_never_an_identity(roster_email):
    engine = _engine([StudentRecord("Jean", "Dupont", "P1", email=roster_email)])

    assert not engine.is_registered_evaluator(_person("Inconnu", "Personne", "42"))


def test_email_match_is_exact_after_normalization():
    engine = _engine([StudentRecord("Jean", "Dupont", "P1", email="jean@example.org")])

    assert engine.is_registered_evaluator(_person("Inconnu", "X", " JEAN@EXAMPLE.ORG "))
    assert not engine.is_registered_evaluator(_person("Inconnu", "X", "jean2@example.org"))


def test_duplicate_roster_email_fails_closed_and_logs_only_hashes():
    address = "partage@example.org"
    engine = _engine([
        StudentRecord("Jean", "Dupont", "P1", email=address),
        StudentRecord("Alice", "Martin", "P2", email=f" {address.upper()} "),
    ])

    assert not engine.is_registered_evaluator(_person("Dupont", "Jean", address))
    entries = get_ambiguity_journal().entries
    assert len(entries) == 1
    assert entries[0]["type"] == "identite_evaluateur_ambigue"
    assert address not in repr(entries)
    assert "Dupont" not in repr(entries)
    assert "Martin" not in repr(entries)


def test_name_and_email_pointing_to_different_students_fails_closed():
    engine = _engine([
        StudentRecord("Jean", "Dupont", "P1", email="jean@example.org"),
        StudentRecord("Alice", "Martin", "P2", email="alice@example.org"),
    ])

    assert not engine.is_registered_evaluator(_person("Dupont", "Jean", "alice@example.org"))
    assert len(get_ambiguity_journal()) == 1
    assert "alice@example.org" not in repr(get_ambiguity_journal().entries)


def test_identity_collision_uses_existing_nonfinal_gate_and_pseudonymized_log(tmp_path):
    address = "shared@example.org"
    engine = _engine([
        StudentRecord("Jean", "Dupont", "P1", email=address),
        StudentRecord("Alice", "Martin", "P2", email=address),
    ])
    assert not engine.is_registered_evaluator(_person("Inconnu", "X", address))
    path = tmp_path / "ambiguities.json"

    exit_code = report_ambiguity_gate(get_ambiguity_journal(), str(path), False)

    assert exit_code == EXIT_AMBIGUITIES_PENDING
    logged = path.read_text(encoding="utf-8")
    assert address not in logged
    assert "Dupont" not in logged
    assert "Martin" not in logged


def test_nominal_match_keeps_existing_behavior_when_email_is_not_in_roster():
    engine = _engine([StudentRecord("Jean", "Dupont", "P1", email="jean@example.org")])

    assert engine.is_registered_evaluator(_person("Dupont", "Jean", "external@example.org"))


def test_roster_loader_maps_optional_email_column(tmp_path):
    roster = tmp_path / "inscrits.csv"
    roster.write_text(
        "Prénom,Nom,Sujet IA Symbolique,Adresse e-mail\n"
        "Jean,Dupont,Projet A,jean@example.org\n",
        encoding="utf-8",
    )

    [student] = load_student_records(roster)

    assert student.email == "jean@example.org"


def test_rule3_uses_email_and_keeps_other_registration_guards():
    registered = StudentRecord("Jean", "Dupont", "Autre projet", email="jean@example.org")
    engine = _engine([registered])
    group = SimpleNamespace(
        groupe="Projet évalué",
        date=datetime(2026, 1, 15, 10, 0),
        group_members=[],
    )
    evaluation = SimpleNamespace(
        nom="Nom différent",
        prenom="Saisi",
        email=" JEAN@example.org ",
        date=group.date,
        note=12.0,
        is_teacher=False,
    )

    assert engine.is_valid_evaluation(group, evaluation, seen_evaluators=set()) is True


def test_self_evaluation_by_email_is_rejected():
    member = StudentRecord("Jean", "Dupont", "P1", email="jean@example.org")
    engine = _engine([member])
    group = SimpleNamespace(groupe="P1", date=datetime(2026, 1, 15), group_members=[member])
    evaluation = SimpleNamespace(nom="Inconnu", prenom="Saisi", email=" JEAN@example.org ",
                                 date=group.date, note=12, is_teacher=False)
    assert engine.is_valid_evaluation(group, evaluation, set()) is False


def test_roster_with_multiple_email_columns_is_rejected(tmp_path):
    roster = tmp_path / "roster.csv"
    roster.write_text("Prénom,Nom,Sujet IA Symbolique,Mail,Login\nJean,Dupont,P1,jean@example.org,login@example.org\n", encoding="utf-8")
    with pytest.raises(ValueError, match="email"):
        load_student_records(roster)


@pytest.mark.parametrize("columns", ["Mail,Login", "Email,Adresse e-mail", "email,Mail"])
def test_multi_group_roster_rejects_multiple_email_columns(tmp_path, columns):
    roster = tmp_path / "roster.csv"
    roster.write_text(
        f"Prénom,Nom,Groupe CC1,{columns}\n"
        "Ada,Exemple,P1,ada@example.org,autre@example.org\n",
        encoding="utf-8",
    )
    with pytest.raises(ValueError, match="Plusieurs colonnes email dans le roster"):
        load_students_with_multiple_groups(roster, [{"nom": "CC1", "inscription_col": "Groupe CC1"}])


@pytest.mark.parametrize("column", ["Mail", "Login", "Email", "Adresse e-mail", "email"])
def test_multi_group_roster_keeps_one_email_column(tmp_path, column):
    roster = tmp_path / "roster.csv"
    roster.write_text(
        f"Prénom,Nom,Groupe CC1,{column}\nAda,Exemple,P1,ada@example.org\n",
        encoding="utf-8",
    )
    students = load_students_with_multiple_groups(
        roster, [{"nom": "CC1", "inscription_col": "Groupe CC1"}]
    )
    assert students.iloc[0]["email"] == "ada@example.org"
    assert students.iloc[0]["groupe_cc1"] == "P1"
