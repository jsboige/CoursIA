"""Tests for scripts/scan_student_forks.py — student fork scanner."""

import importlib.util
import json
from pathlib import Path
from unittest.mock import patch

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent / "scripts" / "scan_student_forks.py"
)
_spec = importlib.util.spec_from_file_location("scan_student_forks", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

strip_accents = _mod.strip_accents
normalize_name = _mod.normalize_name
match_student = _mod.match_student
Student = _mod.Student
ForkInfo = _mod.ForkInfo
generate_markdown_report = _mod.generate_markdown_report
generate_actionable_json = _mod.generate_actionable_json


# --- strip_accents ---


class TestStripAccents:
    def test_no_accents(self):
        assert strip_accents("hello") == "hello"

    def test_french_accents(self):
        assert strip_accents("eclair") == "eclair"
        assert strip_accents("cafe") == "cafe"

    def test_mixed(self):
        result = strip_accents("pre-nom")
        assert "e" not in result or result == "pre-nom"

    def test_empty_string(self):
        assert strip_accents("") == ""

    def test_ascii_only(self):
        assert strip_accents("abc123") == "abc123"


# --- normalize_name ---


class TestNormalizeName:
    def test_lowercase(self):
        assert normalize_name("Jean") == "jean"

    def test_strip_spaces(self):
        assert normalize_name("Jean Pierre") == "jeanpierre"

    def test_strip_hyphens(self):
        assert normalize_name("Jean-Pierre") == "jeanpierre"

    def test_strip_apostrophes(self):
        assert normalize_name("O'Brien") == "obrien"

    def test_combined(self):
        result = normalize_name("Jean-Pierre O'Brien")
        # After normalization: lowercase, no spaces, no hyphens, no apostrophes
        assert " " not in result
        assert "-" not in result
        assert "'" not in result
        assert result == result.lower()

    def test_empty_string(self):
        assert normalize_name("") == ""

    def test_already_normalized(self):
        assert normalize_name("abc") == "abc"


# --- Student dataclass ---


class TestStudent:
    def test_default_values(self):
        s = Student()
        assert s.first_name == ""
        assert s.last_name == ""
        assert s.email == ""
        assert s.school == ""

    def test_custom_values(self):
        s = Student(first_name="Alice", last_name="Dupont", school="EPITA")
        assert s.first_name == "Alice"
        assert s.last_name == "Dupont"
        assert s.school == "EPITA"


# --- ForkInfo dataclass ---


class TestForkInfo:
    def test_default_values(self):
        f = ForkInfo(owner="test", repo="org/repo")
        assert f.owner == "test"
        assert f.repo == "org/repo"
        assert f.commits_ahead == 0
        assert f.has_pr is False
        assert f.flagged is False

    def test_flagged_flag(self):
        f = ForkInfo(owner="test", repo="org/repo", flagged=True)
        assert f.flagged is True

    def test_ahead_shas_default(self):
        f = ForkInfo(owner="test", repo="org/repo")
        assert f.ahead_shas == []


# --- match_student ---


class TestMatchStudent:
    def test_match_by_epita_login(self):
        """Login match: epita_login dots are stripped, fork_owner dots are NOT."""
        students = [
            Student(
                first_name="Alice",
                last_name="Dupont",
                email="alice.dupont@epita.fr",
                epita_login="alice.dupont",
            ),
        ]
        # Fork owner without dots matches the dot-stripped login
        result = match_student("alicedupont", [], students)
        assert result is not None
        assert result.first_name == "Alice"

    def test_match_by_name_in_owner(self):
        students = [
            Student(first_name="Jean", last_name="Martin"),
        ]
        # Owner name matches first+last normalized
        result = match_student("JeanMartin", [], students)
        assert result is not None
        assert result.first_name == "Jean"

    def test_match_by_commit_email(self):
        students = [
            Student(first_name="Bob", last_name="Smith", email="bob@test.com"),
        ]
        commit_authors = [{"author": "Bob", "email": "bob@test.com"}]
        result = match_student("unknown-owner", commit_authors, students)
        assert result is not None
        assert result.first_name == "Bob"

    def test_match_by_commit_author_name(self):
        students = [
            Student(first_name="Claire", last_name="Durand"),
        ]
        commit_authors = [{"author": "Claire Durand", "email": "x@y.com"}]
        result = match_student("random", commit_authors, students)
        assert result is not None
        assert result.first_name == "Claire"

    def test_no_match(self):
        students = [
            Student(first_name="Alice", last_name="Xavier"),
        ]
        result = match_student("zzz-unknown", [], students)
        assert result is None

    def test_empty_students(self):
        result = match_student("alice", [], [])
        assert result is None

    def test_priority_login_over_name(self):
        """Login match should take priority over name match."""
        students = [
            Student(
                first_name="Alice",
                last_name="Dupont",
                epita_login="alicedupont",
            ),
            Student(
                first_name="Alice",
                last_name="Martin",
                epita_login="alicemartin",
            ),
        ]
        result = match_student("alicemartin", [], students)
        assert result is not None
        assert result.last_name == "Martin"

    def test_match_by_last_name_in_author(self):
        """Last name substring match in commit author as fallback."""
        students = [
            Student(first_name="Pierre", last_name="Lambert"),
        ]
        commit_authors = [{"author": "Pierre Lambert", "email": "x@y.com"}]
        result = match_student("unknown", commit_authors, students)
        assert result is not None
        assert result.last_name == "Lambert"


# --- generate_markdown_report ---


class TestGenerateMarkdownReport:
    def test_empty_results(self, tmp_path):
        report_path = generate_markdown_report([], tmp_path)
        assert report_path.exists()
        content = report_path.read_text(encoding="utf-8")
        assert "Fork Scan Report" in content
        assert "All forks with commits have corresponding PRs" in content

    def test_flagged_fork(self, tmp_path):
        student = Student(first_name="Alice", last_name="Dupont", school="EPITA")
        fork = ForkInfo(
            owner="alice-d",
            repo="org/repo",
            commits_ahead=3,
            ahead_shas=["abc1234", "def5678"],
            student=student,
            flagged=True,
        )
        report_path = generate_markdown_report([fork], tmp_path)
        content = report_path.read_text(encoding="utf-8")
        assert "Alice" in content
        assert "flagged" in content.lower() or "WITHOUT PR" in content

    def test_with_pr_fork(self, tmp_path):
        fork = ForkInfo(
            owner="bob-dev",
            repo="org/repo",
            commits_ahead=2,
            has_pr=True,
            pr_number=42,
            pr_state="open",
        )
        report_path = generate_markdown_report([fork], tmp_path)
        content = report_path.read_text(encoding="utf-8")
        assert "#42" in content
        assert "open" in content

    def test_unknown_student(self, tmp_path):
        fork = ForkInfo(
            owner="unknown",
            repo="org/repo",
            commits_ahead=1,
            student=None,
            flagged=True,
        )
        report_path = generate_markdown_report([fork], tmp_path)
        content = report_path.read_text(encoding="utf-8")
        assert "Unknown" in content

    def test_creates_directory(self, tmp_path):
        nested = tmp_path / "sub" / "dir"
        report_path = generate_markdown_report([], nested)
        assert report_path.exists()


# --- generate_actionable_json ---


class TestGenerateActionableJson:
    def test_empty_flagged(self, tmp_path):
        json_path = generate_actionable_json([], tmp_path)
        assert json_path.exists()
        data = json.loads(json_path.read_text(encoding="utf-8"))
        assert data["to_pr"] == []

    def test_flagged_entry(self, tmp_path):
        student = Student(
            first_name="Alice",
            last_name="Dupont",
            email="alice@epita.fr",
            school="EPITA",
            group="SCIA 2027",
        )
        fork = ForkInfo(
            owner="alice-d",
            repo="org/repo",
            commits_ahead=5,
            ahead_shas=["abc1234"],
            files_modified=["notebook.ipynb"],
            student=student,
            flagged=True,
        )
        json_path = generate_actionable_json([fork], tmp_path)
        data = json.loads(json_path.read_text(encoding="utf-8"))
        assert len(data["to_pr"]) == 1
        entry = data["to_pr"][0]
        assert entry["fork_owner"] == "alice-d"
        assert entry["student_name"] == "Alice Dupont"
        assert entry["school"] == "EPITA"

    def test_no_student(self, tmp_path):
        fork = ForkInfo(
            owner="anon",
            repo="org/repo",
            commits_ahead=1,
            flagged=True,
        )
        json_path = generate_actionable_json([fork], tmp_path)
        data = json.loads(json_path.read_text(encoding="utf-8"))
        entry = data["to_pr"][0]
        assert entry["student_name"] == "Unknown"
        assert entry["school"] == "Unknown"

    def test_creates_directory(self, tmp_path):
        nested = tmp_path / "deep" / "nested"
        json_path = generate_actionable_json([], nested)
        assert json_path.exists()

    def test_branch_target_generated(self, tmp_path):
        student = Student(first_name="Jean", last_name="Martin")
        fork = ForkInfo(
            owner="jm",
            repo="org/repo",
            commits_ahead=1,
            student=student,
            flagged=True,
        )
        json_path = generate_actionable_json([fork], tmp_path)
        data = json.loads(json_path.read_text(encoding="utf-8"))
        entry = data["to_pr"][0]
        assert "branch_target" in entry
        assert "jeanmartin" in entry["branch_target"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
