"""Tests for scripts/notebook_tools/epita_prcon_autograde.py — EPITA PrCon auto-grader.

Tests focus on: _generate_notes (pure function), constants consistency.
No GitHub API calls required.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from epita_prcon_autograde import (
    GROUPS,
    GROUP_FOLDERS,
    SIZE_BONUS,
    SOUTENANCE_DATES,
    REPO_DEFAULT,
    _generate_notes,
)


# ---------------------------------------------------------------------------
# Constants consistency
# ---------------------------------------------------------------------------

class TestConstants:
    def test_groups_count(self):
        """5 groups in the grading cohort."""
        assert len(GROUPS) == 5
        assert GROUPS == ["E4", "H1", "H2", "J1", "I2"]

    def test_group_folders_keys_match(self):
        """GROUP_FOLDERS keys match GROUPS."""
        assert set(GROUP_FOLDERS.keys()) == set(GROUPS)

    def test_size_bonus_keys_match(self):
        """SIZE_BONUS keys are a subset of GROUPS."""
        assert set(SIZE_BONUS.keys()).issubset(set(GROUPS))

    def test_size_bonus_values_non_negative(self):
        """SIZE_BONUS values are non-negative."""
        for group, bonus in SIZE_BONUS.items():
            assert bonus >= 0, f"SIZE_BONUS[{group}] = {bonus} < 0"

    def test_soutenance_dates_keys_match(self):
        """SOUTENANCE_DATES keys match GROUPS."""
        assert set(SOUTENANCE_DATES.keys()) == set(GROUPS)

    def test_soutenance_dates_valid_format(self):
        """All dates are YYYY-MM-DD format."""
        for group, date_str in SOUTENANCE_DATES.items():
            assert len(date_str) == 10, f"Date {date_str} for {group} not YYYY-MM-DD"
            assert date_str[4] == "-" and date_str[7] == "-"

    def test_repo_default_is_github(self):
        """REPO_DEFAULT points to a GitHub repo."""
        assert "/" in REPO_DEFAULT
        assert "jsboigeEpita" in REPO_DEFAULT

    def test_group_folders_values_are_strings(self):
        """All folder names are non-empty strings."""
        for group, folder in GROUP_FOLDERS.items():
            assert isinstance(folder, str) and len(folder) > 0, f"Empty folder for {group}"


# ---------------------------------------------------------------------------
# _generate_notes
# ---------------------------------------------------------------------------

class TestGenerateNotes:
    def _default_kwargs(self, **overrides):
        """Build default kwargs for _generate_notes."""
        defaults = {
            "group": "E4",
            "python_files": ["main.py"],
            "notebook_files": ["analysis.ipynb"],
            "has_cpsat": True,
            "has_solver": True,
            "commits": 10,
            "days_inactive": 3,
            "readme_indicators": {"line_count": 80},
        }
        defaults.update(overrides)
        return defaults

    def test_good_project(self):
        """Full project with code, CP-SAT, active git, good README."""
        notes = _generate_notes(**self._default_kwargs())
        assert any("CP-SAT" in n for n in notes)
        assert not any("CRITICAL" in n for n in notes)
        assert not any("WARNING" in n for n in notes)

    def test_no_code_at_all(self):
        """No Python or notebook files = CRITICAL."""
        notes = _generate_notes(**self._default_kwargs(
            python_files=[], notebook_files=[]))
        assert any("CRITICAL" in n and "No code" in n for n in notes)

    def test_no_python_files(self):
        """Missing Python files = WARNING."""
        notes = _generate_notes(**self._default_kwargs(python_files=[]))
        assert any("WARNING" in n and "No Python" in n for n in notes)

    def test_no_notebook_files(self):
        """Missing notebooks = INFO."""
        notes = _generate_notes(**self._default_kwargs(notebook_files=[]))
        assert any("INFO" in n and "No Jupyter" in n for n in notes)

    def test_solver_only_no_cpsat(self):
        """Has solver import but no full CP-SAT model = OK."""
        notes = _generate_notes(**self._default_kwargs(has_cpsat=False, has_solver=True))
        assert any("OK" in n and "Solver" in n for n in notes)

    def test_no_solver_with_code(self):
        """Python code but no CP solver = WARNING."""
        notes = _generate_notes(**self._default_kwargs(has_cpsat=False, has_solver=False))
        assert any("WARNING" in n and "no CP solver" in n for n in notes)

    def test_minimal_commits(self):
        """Only 1 commit = WARNING."""
        notes = _generate_notes(**self._default_kwargs(commits=1))
        assert any("WARNING" in n and "commit" in n for n in notes)

    def test_zero_commits(self):
        """0 commits = WARNING."""
        notes = _generate_notes(**self._default_kwargs(commits=0))
        assert any("WARNING" in n and "commit" in n for n in notes)

    def test_long_inactivity(self):
        """15 days inactive = WARNING."""
        notes = _generate_notes(**self._default_kwargs(days_inactive=15))
        assert any("WARNING" in n and "15 days" in n for n in notes)

    def test_moderate_inactivity(self):
        """8 days inactive = INFO."""
        notes = _generate_notes(**self._default_kwargs(days_inactive=8))
        assert any("INFO" in n and "8 days" in n for n in notes)

    def test_detailed_readme(self):
        """README >100 lines = GOOD."""
        notes = _generate_notes(**self._default_kwargs(
            readme_indicators={"line_count": 120}))
        assert any("GOOD" in n and "Detailed README" in n for n in notes)

    def test_moderate_readme(self):
        """README >50 lines = OK."""
        notes = _generate_notes(**self._default_kwargs(
            readme_indicators={"line_count": 60}))
        assert any("OK" in n and "README" in n for n in notes)

    def test_no_readme(self):
        """No README = CRITICAL."""
        notes = _generate_notes(**self._default_kwargs(
            readme_indicators={"line_count": 0}))
        assert any("CRITICAL" in n and "No README" in n for n in notes)

    def test_j1_without_cpsat(self):
        """J1 group without CP-SAT = CRITICAL (web app misalignment)."""
        notes = _generate_notes(**self._default_kwargs(group="J1", has_cpsat=False))
        assert any("CRITICAL" in n and "Web app" in n for n in notes)

    def test_e4_or_h1_no_python(self):
        """E4/H1 with no Python = RISK (excellent README, no code)."""
        notes = _generate_notes(**self._default_kwargs(group="E4", python_files=[]))
        assert any("RISK" in n and "zero code" in n for n in notes)

    def test_h1_no_python(self):
        """H1 with no Python = RISK."""
        notes = _generate_notes(**self._default_kwargs(group="H1", python_files=[]))
        assert any("RISK" in n and "zero code" in n for n in notes)

    def test_i2_minimal_commits(self):
        """I2 with only 1 commit = RISK."""
        notes = _generate_notes(**self._default_kwargs(group="I2", commits=1))
        assert any("RISK" in n and "Scaffolding" in n for n in notes)

    def test_h2_normal(self):
        """H2 group with normal project — no group-specific notes."""
        notes = _generate_notes(**self._default_kwargs(group="H2"))
        # H2 has no group-specific checks, so no RISK/CRITICAL from group logic
        group_notes = [n for n in notes if "RISK" in n or "CRITICAL" in n]
        assert len(group_notes) == 0

    def test_returns_list_of_strings(self):
        """Output is always a list of strings."""
        notes = _generate_notes(**self._default_kwargs())
        assert isinstance(notes, list)
        for n in notes:
            assert isinstance(n, str)
