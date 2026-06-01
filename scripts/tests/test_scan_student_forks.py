"""Tests for scripts/scan_student_forks.py — student fork scanner.

Tests focus on pure functions (name normalization, dataclass construction).
API-calling functions (gh_api, list_forks, etc.) are excluded from unit tests
as they require subprocess/gh CLI mocking (tested via integration).
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_student_forks import (
    ECE_REPOS,
    REPOS,
    ForkInfo,
    Student,
    normalize_name,
    strip_accents,
)


# ---------------------------------------------------------------------------
# strip_accents
# ---------------------------------------------------------------------------

class TestStripAccents:
    def test_no_accents(self):
        assert strip_accents("hello") == "hello"

    def test_french_accents(self):
        assert strip_accents("Francois") == "Francois"
        assert strip_accents("Andre") == "Andre"
        assert strip_accents("Etienne") == "Etienne"

    def test_mixed_accents(self):
        result = strip_accents("Jean-François")
        assert "ç" not in result
        assert "Jean" in result

    def test_empty_string(self):
        assert strip_accents("") == ""

    def test_no_change_ascii(self):
        assert strip_accents("abc123") == "abc123"


# ---------------------------------------------------------------------------
# normalize_name
# ---------------------------------------------------------------------------

class TestNormalizeName:
    def test_lowercase(self):
        assert normalize_name("Dupont") == "dupont"

    def test_removes_spaces(self):
        assert normalize_name("Jean Pierre") == "jeanpierre"

    def test_removes_hyphens(self):
        assert normalize_name("Jean-Pierre") == "jeanpierre"

    def test_removes_accents_and_case(self):
        result = normalize_name("François")
        assert "ç" not in result
        assert result == "francois"

    def test_removes_apostrophes(self):
        assert normalize_name("O'Brien") == "obrien"

    def test_complex_name(self):
        result = normalize_name("Jean-François D'Arc")
        assert "ç" not in result
        assert "-" not in result
        assert " " not in result
        assert "'" not in result

    def test_empty(self):
        assert normalize_name("") == ""


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------

class TestStudent:
    def test_default_values(self):
        s = Student()
        assert s.first_name == ""
        assert s.school == ""
        assert s.epita_login == ""

    def test_custom_values(self):
        s = Student(first_name="Alice", last_name="Dupont", email="a@b.c", school="ECE", group="Gr1")
        assert s.first_name == "Alice"
        assert s.email == "a@b.c"


class TestForkInfo:
    def test_defaults(self):
        f = ForkInfo(owner="test", repo="test-repo")
        assert f.commits_ahead == 0
        assert f.ahead_shas == []
        assert f.student is None
        assert f.has_pr is False
        assert f.flagged is False

    def test_with_student(self):
        s = Student(first_name="Bob")
        f = ForkInfo(owner="bob", repo="repo", student=s, commits_ahead=3)
        assert f.student.first_name == "Bob"
        assert f.commits_ahead == 3


# ---------------------------------------------------------------------------
# Config constants
# ---------------------------------------------------------------------------

class TestConfig:
    def test_repos_has_coursia(self):
        assert "coursia" in REPOS

    def test_ece_repos_six_groups(self):
        assert len(ECE_REPOS) == 6  # 2 projects x 3 groups

    def test_ece_repos_format(self):
        for repo in ECE_REPOS:
            assert repo.startswith("jsboigeECE/")
            assert "Gr" in repo
