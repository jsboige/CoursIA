"""Tests for epita_prcon_autograde.py — mutation-killing tests.

Covers: _generate_notes, analyze_group scoring logic (theoretical,
technical, organisation), file classification, commit deduplication,
date parsing, PR matching, print_summary output.
"""

import json
import os
import sys
from datetime import datetime, timezone
from io import StringIO
from unittest.mock import patch

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from epita_prcon_autograde import (
    GROUPS,
    GROUP_FOLDERS,
    SIZE_BONUS,
    SOUTENANCE_DATES,
    _generate_notes,
    analyze_group,
    print_summary,
)


# --- _generate_notes ---

class TestGenerateNotes:
    """Mutation tests for _generate_notes (L345-394)."""

    def test_no_code_no_notebook_critical(self):
        notes = _generate_notes("E4", [], [], False, False, 5, 0, {"line_count": 50})
        assert any("CRITICAL" in n and "No code" in n for n in notes)

    def test_no_python_warning(self):
        notes = _generate_notes("H2", [], [{"path": "nb.ipynb"}], False, False, 5, 0, {"line_count": 50})
        assert any("WARNING" in n and "No Python" in n for n in notes)

    def test_no_notebook_info(self):
        notes = _generate_notes("H2", [{"path": "a.py"}], [], False, False, 5, 0, {"line_count": 50})
        assert any("INFO" in n and "No Jupyter" in n for n in notes)

    def test_has_cpsat_good(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 0, {"line_count": 50})
        assert any("GOOD" in n and "CP-SAT" in n for n in notes)

    def test_has_solver_no_cpsat_ok(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], False, True, 5, 0, {"line_count": 50})
        assert any("OK" in n and "Solver import" in n for n in notes)

    def test_python_no_solver_warning(self):
        notes = _generate_notes("H2", [{"path": "a.py"}], [], False, False, 5, 0, {"line_count": 50})
        assert any("WARNING" in n and "no CP solver" in n for n in notes)

    def test_single_commit_warning(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 1, 0, {"line_count": 50})
        assert any("WARNING" in n and "1 commit" in n for n in notes)

    def test_zero_commits_warning(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 0, 0, {"line_count": 50})
        assert any("WARNING" in n and "0 commit" in n for n in notes)

    def test_days_inactive_over_14_warning(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 20, {"line_count": 50})
        assert any("WARNING" in n and "20 days" in n for n in notes)

    def test_days_inactive_8_info(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 8, {"line_count": 50})
        assert any("INFO" in n and "8 days" in n for n in notes)

    def test_days_inactive_5_no_note(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 5, {"line_count": 50})
        assert not any("days since" in n for n in notes)

    def test_readme_over_100_good(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 0, {"line_count": 120})
        assert any("GOOD" in n and ">100 lines" in n for n in notes)

    def test_readme_over_50_ok(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 0, {"line_count": 70})
        assert any("OK" in n and "some content" in n for n in notes)

    def test_no_readme_critical(self):
        notes = _generate_notes("E4", [{"path": "a.py"}], [], True, True, 5, 0, {"line_count": 0})
        assert any("CRITICAL" in n and "No README" in n for n in notes)

    def test_j1_no_cpsat_critical(self):
        notes = _generate_notes("J1", [{"path": "a.py"}], [], False, True, 5, 0, {"line_count": 50})
        assert any("CRITICAL" in n and "Web app" in n for n in notes)

    def test_e4_no_python_risk(self):
        notes = _generate_notes("E4", [], [{"path": "nb.ipynb"}], True, True, 5, 0, {"line_count": 50})
        assert any("RISK" in n and "zero code" in n for n in notes)

    def test_i2_single_commit_risk(self):
        notes = _generate_notes("I2", [{"path": "a.py"}], [], True, True, 1, 0, {"line_count": 50})
        assert any("RISK" in n and "Scaffolding" in n for n in notes)

    def test_h1_no_python_risk(self):
        notes = _generate_notes("H1", [], [{"path": "nb.ipynb"}], True, True, 5, 0, {"line_count": 50})
        assert any("RISK" in n for n in notes)


# --- analyze_group: file classification ---

class TestAnalyzeGroupFileClassification:
    """Mutation tests for file classification in analyze_group (L128-147)."""

    # Use actual GROUP_FOLDERS values for correct prefix matching
    _H2_FOLDER = GROUP_FOLDERS["H2"]  # "procedural-gen"

    def _tree(self, paths):
        return [{"path": p, "type": "blob", "size": 100} for p in paths]

    def test_python_files_classified(self):
        tree = self._tree([f"{self._H2_FOLDER}/a.py", f"{self._H2_FOLDER}/b.py", f"{self._H2_FOLDER}/readme.md"])
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["files"]["python"] == 2

    def test_notebook_files_classified(self):
        tree = self._tree([f"{self._H2_FOLDER}/nb.ipynb", f"{self._H2_FOLDER}/a.py"])
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["files"]["notebooks"] == 1

    def test_readme_classified(self):
        tree = self._tree([f"{self._H2_FOLDER}/README.md", f"{self._H2_FOLDER}/a.py"])
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["files"]["readme"] == 1

    def test_json_classified(self):
        tree = self._tree([f"{self._H2_FOLDER}/data.json", f"{self._H2_FOLDER}/a.py"])
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["files"]["json"] == 1

    def test_files_outside_group_excluded(self):
        tree = self._tree(["other-group/a.py", f"{self._H2_FOLDER}/b.py"])
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["files"]["total"] == 1


# --- analyze_group: scoring ---

class TestAnalyzeGroupScoring:
    """Mutation tests for scoring thresholds (L234-299)."""

    _H2 = GROUP_FOLDERS["H2"]

    def _minimal_tree(self, extra_paths=None):
        base = [f"{self._H2}/a.py"]
        if extra_paths:
            base.extend(extra_paths)
        return [{"path": p, "type": "blob", "size": 100} for p in base]

    def test_theoretical_max_capped_at_10(self):
        """Even with all indicators, score cannot exceed 10."""
        tree = self._minimal_tree(["g-H2/README.md"])
        readme = "variable constraint objective cp-sat baseline benchmark metric performance\n" + "\n" * 120
        py_content = "cp_model CpModel newboolvar addconstraint"
        with patch("epita_prcon_autograde.get_file_content", side_effect=lambda r, p, t=None: readme if "README" in p else py_content):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["scores"]["theoretical"] <= 10

        tree = self._minimal_tree([f"{self._H2}/nb.ipynb"] + [f"{self._H2}/file{i}.py" for i in range(10)])
        py_content = "from ortools.sat.python import cp_model\nmodel = cp_model.CpModel()\nnewboolvar\n" + "\n" * 400
        with patch("epita_prcon_autograde.get_file_content", return_value=py_content):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["scores"]["technical"] <= 10

    def test_no_code_low_technical(self):
        tree = [{"path": f"{self._H2}/README.md", "type": "blob", "size": 50}]
        with patch("epita_prcon_autograde.get_file_content", return_value="hello"):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["scores"]["technical"] <= 2

    def test_organisation_zero_commits(self):
        tree = self._minimal_tree()
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": []}, [], "repo")
        # 0 commits → org_score starts at 0, may get points from readme/files
        assert result["scores"]["organisation"] < 5

    def test_organisation_high_activity(self):
        tree = self._minimal_tree([f"{self._H2}/README.md"] + [f"{self._H2}/f{i}.py" for i in range(6)])
        commits = [
            {"sha": f"abc{i}", "author": {"login": f"user{i % 2}"},
             "commit": {"committer": {"date": datetime.now(timezone.utc).isoformat()}}}
            for i in range(6)
        ]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": commits}, [], "repo")
        assert result["scores"]["organisation"] >= 5

    def test_size_bonus_applied(self):
        tree = self._minimal_tree()
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("E4", tree, {}, [], "repo")
        assert result["size_bonus"] == SIZE_BONUS["E4"]

    def test_estimated_range_includes_bonus(self):
        tree = self._minimal_tree()
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("E4", tree, {}, [], "repo")
        # E4 has SIZE_BONUS=3, so range should reflect that
        assert result["estimated_range"]["min"] >= 0
        assert result["estimated_range"]["max"] <= 20


# --- analyze_group: commit deduplication ---

class TestAnalyzeGroupCommitDedup:
    """Mutation tests for commit deduplication (L194-201)."""

    _H2 = GROUP_FOLDERS["H2"]

    def test_duplicate_shas_counted_once(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        commits = [
            {"sha": "abc123", "author": {"login": "u1"},
             "commit": {"committer": {"date": "2026-05-01T00:00:00Z"}}},
            {"sha": "abc123", "author": {"login": "u1"},
             "commit": {"committer": {"date": "2026-05-02T00:00:00Z"}}},
            {"sha": "def456", "author": {"login": "u2"},
             "commit": {"committer": {"date": "2026-05-03T00:00:00Z"}}},
        ]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": commits}, [], "repo")
        assert result["git_activity"]["commit_count"] == 2


# --- analyze_group: PR matching ---

class TestAnalyzeGroupPRMatching:
    """Mutation tests for PR matching (L220-226)."""

    _H2 = GROUP_FOLDERS["H2"]

    def test_pr_matched_by_folder_name(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        prs = [{"title": f"Update {self._H2}", "body": "", "merged_at": "2026-05-01"}]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, prs, "repo")
        assert result["git_activity"]["merged_prs"] == 1

    def test_pr_matched_by_group_id(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        prs = [{"title": "H2 updates", "body": "", "merged_at": "2026-05-01"}]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, prs, "repo")
        assert result["git_activity"]["merged_prs"] == 1

    def test_pr_not_matched_unrelated(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        prs = [{"title": "E4 updates", "body": "unrelated", "merged_at": "2026-05-01"}]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, prs, "repo")
        assert result["git_activity"]["merged_prs"] == 0


# --- analyze_group: date parsing ---

class TestAnalyzeGroupDateParsing:
    """Mutation tests for date parsing (L210-217)."""

    _H2 = GROUP_FOLDERS["H2"]

    def test_last_activity_parsed(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        commits = [
            {"sha": "a1", "author": {"login": "u1"},
             "commit": {"committer": {"date": "2026-05-10T12:00:00Z"}}},
            {"sha": "b2", "author": {"login": "u1"},
             "commit": {"committer": {"date": "2026-05-15T08:00:00Z"}}},
        ]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": commits}, [], "repo")
        assert result["git_activity"]["last_activity"] is not None
        assert "2026-05-15" in result["git_activity"]["last_activity"]

    def test_invalid_date_graceful(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        commits = [
            {"sha": "a1", "author": {"login": "u1"},
             "commit": {"committer": {"date": "not-a-date"}}},
        ]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": commits}, [], "repo")
        # Should not crash, last_activity may be None
        assert "git_activity" in result

    def test_no_author_login_handled(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        commits = [
            {"sha": "a1", "author": None,
             "commit": {"committer": {"date": "2026-05-01T00:00:00Z"}}},
        ]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {"H2": commits}, [], "repo")
        assert len(result["git_activity"]["contributors"]) == 0


# --- analyze_group: readme content analysis ---

class TestAnalyzeGroupReadmeAnalysis:
    """Mutation tests for README keyword detection (L155-174)."""

    _H2 = GROUP_FOLDERS["H2"]

    def _tree_with_readme(self):
        return [
            {"path": f"{self._H2}/a.py", "type": "blob", "size": 100},
            {"path": f"{self._H2}/README.md", "type": "blob", "size": 500},
        ]

    def test_formulation_detected(self):
        readme = "We define variables x and constraints c with objective maximize."
        with patch("epita_prcon_autograde.get_file_content", return_value=readme):
            result = analyze_group("H2", self._tree_with_readme(), {}, [], "repo")
        assert result["readme_analysis"]["has_formulation"] is True

    def test_cp_modeling_detected(self):
        readme = "Using CP-SAT solver from OR-Tools for constraint programming."
        with patch("epita_prcon_autograde.get_file_content", return_value=readme):
            result = analyze_group("H2", self._tree_with_readme(), {}, [], "repo")
        assert result["readme_analysis"]["has_cp_modeling"] is True

    def test_baselines_detected(self):
        readme = "Comparison with random baseline shows improvement."
        with patch("epita_prcon_autograde.get_file_content", return_value=readme):
            result = analyze_group("H2", self._tree_with_readme(), {}, [], "repo")
        assert result["readme_analysis"]["has_baselines"] is True

    def test_metrics_detected(self):
        readme = "Performance metrics show 95% accuracy."
        with patch("epita_prcon_autograde.get_file_content", return_value=readme):
            result = analyze_group("H2", self._tree_with_readme(), {}, [], "repo")
        assert result["readme_analysis"]["has_metrics"] is True

    def test_empty_readme_no_indicators(self):
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", self._tree_with_readme(), {}, [], "repo")
        assert result["readme_analysis"]["has_formulation"] is False
        assert result["readme_analysis"]["line_count"] == 0


# --- analyze_group: soutenance date ---

class TestAnalyzeGroupSoutenance:
    """Mutation tests for soutenance date lookup (L328)."""

    _H2 = GROUP_FOLDERS["H2"]

    def test_soutenance_date_populated(self):
        tree = [{"path": f"{self._H2}/a.py", "type": "blob", "size": 100}]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("H2", tree, {}, [], "repo")
        assert result["soutenance_date"] == SOUTENANCE_DATES["H2"]

    def test_unknown_group_soutenance(self):
        tree = [{"path": "ZZ/a.py", "type": "blob", "size": 100}]
        with patch("epita_prcon_autograde.get_file_content", return_value=""):
            result = analyze_group("ZZ", tree, {}, [], "repo")
        assert result["soutenance_date"] == "unknown"


# --- print_summary ---

class TestPrintSummary:
    """Mutation tests for print_summary (L440-509)."""

    def test_empty_report_no_crash(self):
        buf = StringIO()
        with patch("sys.stdout", buf):
            print_summary({"groups": {}})
        output = buf.getvalue()
        assert "No group data" in output

    def test_single_group_printed(self):
        report = {
            "repo": "test/repo",
            "generated_at": "2026-06-04T00:00:00Z",
            "groups": {
                "H2": {
                    "scores": {"presentation": None, "theoretical": 5, "technical": 6, "organisation": 7},
                    "files": {"total": 3, "python": 2, "notebooks": 1, "readme": 0, "json": 0, "other": 0, "total_py_lines": 100},
                    "git_activity": {"commit_count": 5, "contributors": ["u1"], "last_activity": "2026-06-01", "days_inactive": 3, "merged_prs": 0},
                    "code_analysis": {"has_solver_import": False, "has_cpsat_model": False, "python_file_paths": [], "notebook_paths": []},
                    "soutenance_date": "2026-05-22",
                    "size_bonus": 3,
                    "estimated_range": {"min": 10.0, "max": 15.0},
                    "notes": ["INFO: No Jupyter notebooks found"],
                }
            }
        }
        buf = StringIO()
        with patch("sys.stdout", buf):
            print_summary(report)
        output = buf.getvalue()
        assert "H2" in output
        assert "theory=5" in output
        assert "tech=6" in output
        assert "org=7" in output

    def test_summary_table_printed_with_data(self):
        report = {
            "repo": "test/repo",
            "generated_at": "2026-06-04",
            "groups": {
                "H2": {
                    "scores": {"presentation": None, "theoretical": 3, "technical": 2, "organisation": 1},
                    "files": {"total": 1, "python": 1, "notebooks": 0, "readme": 0, "json": 0, "other": 0, "total_py_lines": 50},
                    "git_activity": {"commit_count": 1, "contributors": [], "last_activity": None, "days_inactive": 30, "merged_prs": 0},
                    "code_analysis": {"has_solver_import": False, "has_cpsat_model": False, "python_file_paths": [], "notebook_paths": []},
                    "soutenance_date": "2026-05-22",
                    "size_bonus": 3,
                    "estimated_range": {"min": 3.0, "max": 8.0},
                    "notes": ["WARNING: Python code present but no CP solver usage detected"],
                }
            }
        }
        buf = StringIO()
        with patch("sys.stdout", buf):
            print_summary(report)
        output = buf.getvalue()
        assert "Summary Table" in output


# --- Constants ---

class TestConstants:
    """Mutation tests for constants (L43-65)."""

    def test_groups_is_list(self):
        assert isinstance(GROUPS, list)
        assert len(GROUPS) == 5

    def test_group_folders_complete(self):
        for g in GROUPS:
            assert g in GROUP_FOLDERS

    def test_size_bonus_keys_match_groups(self):
        for k in SIZE_BONUS:
            assert k in GROUPS

    def test_soutenance_dates_complete(self):
        for g in GROUPS:
            assert g in SOUTENANCE_DATES


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
