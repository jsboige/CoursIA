"""Tests for scripts/validate_qc_projects.py — QC project structure validator."""

import importlib.util
from pathlib import Path

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent
    / "scripts"
    / "validate_qc_projects.py"
)
_spec = importlib.util.spec_from_file_location("validate_qc_projects", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

find_projects = _mod.find_projects
parse_readme_projects = _mod.parse_readme_projects
parse_readme_counts = _mod.parse_readme_counts
check_duplicate_sources = _mod.check_duplicate_sources
validate = _mod.validate


# --- find_projects ---


class TestFindProjects:
    def test_finds_python_project(self, tmp_path):
        proj = tmp_path / "my-strategy"
        proj.mkdir()
        (proj / "main.py").write_text("# strategy", encoding="utf-8")
        result = find_projects(tmp_path)
        assert "my-strategy" in result
        assert result["my-strategy"] == proj

    def test_finds_csharp_project(self, tmp_path):
        proj = tmp_path / "CSharpStrategy"
        proj.mkdir()
        (proj / "Main.cs").write_text("// strategy", encoding="utf-8")
        result = find_projects(tmp_path)
        assert "CSharpStrategy" in result

    def test_skips_underscore_dirs(self, tmp_path):
        hidden = tmp_path / "_docs"
        hidden.mkdir()
        (hidden / "main.py").write_text("x", encoding="utf-8")
        result = find_projects(tmp_path)
        assert "_docs" not in result

    def test_skips_special_dirs(self, tmp_path):
        for name in ("_archives", "__pycache__", ".git"):
            d = tmp_path / name
            d.mkdir()
        result = find_projects(tmp_path)
        assert len(result) == 0

    def test_includes_empty_dirs(self, tmp_path):
        """Directories without main.py/Main.cs are still listed."""
        proj = tmp_path / "empty-strategy"
        proj.mkdir()
        result = find_projects(tmp_path)
        assert "empty-strategy" in result

    def test_skips_files(self, tmp_path):
        (tmp_path / "readme.txt").write_text("not a dir", encoding="utf-8")
        result = find_projects(tmp_path)
        assert len(result) == 0

    def test_multiple_projects(self, tmp_path):
        for name in ("alpha", "beta", "gamma"):
            d = tmp_path / name
            d.mkdir()
            (d / "main.py").write_text("", encoding="utf-8")
        result = find_projects(tmp_path)
        assert len(result) == 3


# --- parse_readme_projects ---


class TestParseReadmeProjects:
    def test_extracts_project_names(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "| [Alpha](Alpha/) | Strategy |\n| [Beta](Beta/) | Other |\n",
            encoding="utf-8",
        )
        names = parse_readme_projects(readme)
        assert names == {"Alpha", "Beta"}

    def test_extracts_nested_paths(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("[Deep](path/to/DeepProj/)\n", encoding="utf-8")
        names = parse_readme_projects(readme)
        assert "DeepProj" in names

    def test_skips_skip_names(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "[docs](docs/) | [forum](forum/) | [Strategy](MyStrategy/)\n",
            encoding="utf-8",
        )
        names = parse_readme_projects(readme)
        assert names == {"MyStrategy"}

    def test_skips_file_extensions(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("[file](report.pdf)\n", encoding="utf-8")
        names = parse_readme_projects(readme)
        assert len(names) == 0

    def test_missing_readme_returns_empty(self, tmp_path):
        names = parse_readme_projects(tmp_path / "nonexistent.md")
        assert names == set()

    def test_external_links_skipped(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "[Example](https://example.com)\n[Local](LocalProj/)\n",
            encoding="utf-8",
        )
        names = parse_readme_projects(readme)
        assert names == {"LocalProj"}


# --- parse_readme_counts ---


class TestParseReadmeCounts:
    def test_extracts_counts(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "# QC Strategies\n**78 stratégies** and **8 clones**.\n",
            encoding="utf-8",
        )
        counts = parse_readme_counts(readme)
        assert counts is not None
        assert counts["stratégies"] == 78
        assert counts["clones"] == 8

    def test_single_count(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("**42 projects**\n", encoding="utf-8")
        counts = parse_readme_counts(readme)
        assert counts is not None
        assert counts["projects"] == 42

    def test_missing_readme(self, tmp_path):
        counts = parse_readme_counts(tmp_path / "nonexistent.md")
        assert counts is None

    def test_no_bold_counts(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Just a title\nNo counts here.\n", encoding="utf-8")
        counts = parse_readme_counts(readme)
        assert counts is None


# --- check_duplicate_sources ---


class TestCheckDuplicateSources:
    def test_detects_duplicate(self, tmp_path):
        qc_root = tmp_path
        projects = qc_root / "projects"
        projects.mkdir()
        (projects / "My-Strategy").mkdir()

        imported = qc_root / "projects-imported"
        imported.mkdir()
        (imported / "my_strategy").mkdir()

        issues = check_duplicate_sources(qc_root)
        assert len(issues) == 1
        assert "DUPLICATE" in issues[0]

    def test_no_duplicate(self, tmp_path):
        qc_root = tmp_path
        projects = qc_root / "projects"
        projects.mkdir()
        (projects / "Alpha").mkdir()

        imported = qc_root / "projects-imported"
        imported.mkdir()
        (imported / "Beta").mkdir()

        issues = check_duplicate_sources(qc_root)
        assert len(issues) == 0

    def test_missing_source_dirs_ok(self, tmp_path):
        qc_root = tmp_path
        projects = qc_root / "projects"
        projects.mkdir()
        (projects / "Alpha").mkdir()
        # No projects-imported, no algorithms dir
        issues = check_duplicate_sources(qc_root)
        assert len(issues) == 0

    def test_normalizes_hyphens_underscores(self, tmp_path):
        qc_root = tmp_path
        projects = qc_root / "projects"
        projects.mkdir()
        (projects / "my-cool-strategy").mkdir()

        imported = qc_root / "projects-imported"
        imported.mkdir()
        (imported / "my_cool_strategy").mkdir()

        issues = check_duplicate_sources(qc_root)
        assert len(issues) == 1


# --- validate ---


class TestValidate:
    def _setup_projects(self, tmp_path, project_names, readme_entries):
        """Helper to create a mini QC project structure."""
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        for name in project_names:
            d = projects_dir / name
            d.mkdir()
            (d / "main.py").write_text("", encoding="utf-8")

        readme = projects_dir / "README.md"
        lines = ["# Projects\n"]
        for entry in readme_entries:
            lines.append(f"| [{entry}]({entry}/) | desc |\n")
        readme.write_text("".join(lines), encoding="utf-8")
        return projects_dir, readme

    def test_all_good(self, tmp_path):
        projects_dir, readme = self._setup_projects(
            tmp_path, ["Alpha", "Beta"], ["Alpha", "Beta"]
        )
        issues = validate(projects_dir, readme)
        # Only SUMMARY line, no errors
        errors = [i for i in issues if not i.startswith("SUMMARY")]
        assert len(errors) == 0
        assert any("SUMMARY" in i for i in issues)

    def test_missing_on_disk(self, tmp_path):
        projects_dir, readme = self._setup_projects(
            tmp_path, ["Alpha"], ["Alpha", "Ghost"]
        )
        issues = validate(projects_dir, readme)
        missing_disk = [i for i in issues if "MISSING_ON_DISK" in i]
        assert len(missing_disk) == 1
        assert "Ghost" in missing_disk[0]

    def test_missing_in_readme(self, tmp_path):
        projects_dir, readme = self._setup_projects(
            tmp_path, ["Alpha", "Hidden"], ["Alpha"]
        )
        issues = validate(projects_dir, readme)
        missing_readme = [i for i in issues if "MISSING_IN_README" in i]
        assert len(missing_readme) == 1
        assert "Hidden" in missing_readme[0]

    def test_empty_project(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        # Create a project without main.py/Main.cs
        empty = projects_dir / "NoCode"
        empty.mkdir()

        readme = projects_dir / "README.md"
        readme.write_text("| [NoCode](NoCode/) |\n", encoding="utf-8")

        issues = validate(projects_dir, readme)
        no_code = [i for i in issues if "NO_CODE" in i]
        assert len(no_code) == 1
        assert "NoCode" in no_code[0]

    def test_summary_includes_counts(self, tmp_path):
        projects_dir, readme = self._setup_projects(
            tmp_path, ["A", "B"], ["A", "B"]
        )
        issues = validate(projects_dir, readme)
        summary = [i for i in issues if "SUMMARY" in i]
        assert len(summary) == 1
        assert "2 dirs" in summary[0]
        assert "2 with code" in summary[0]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
