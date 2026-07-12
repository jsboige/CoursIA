"""Tests for scripts/validate_qc_projects.py — QC project structure validation."""

import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from validate_qc_projects import (
    check_duplicate_sources,
    find_projects,
    parse_readme_counts,
    parse_readme_projects,
    validate,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_project(tmp_path: Path, name: str, code_file: str = "main.py") -> Path:
    """Create a minimal project directory with a code file."""
    proj = tmp_path / name
    proj.mkdir(exist_ok=True)
    (proj / code_file).write_text("# stub", encoding="utf-8")
    return proj


def _make_readme(tmp_path: Path, content: str) -> Path:
    readme = tmp_path / "README.md"
    readme.write_text(content, encoding="utf-8")
    return readme


# ---------------------------------------------------------------------------
# find_projects
# ---------------------------------------------------------------------------

class TestFindProjects:
    def test_finds_projects_with_code(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        _make_project(projects_dir, "Alpha")
        _make_project(projects_dir, "Beta", "Main.cs")

        result = find_projects(projects_dir)
        assert "Alpha" in result
        assert "Beta" in result
        assert len(result) == 2

    def test_skips_underscore_prefixes(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        _make_project(projects_dir, "_archives")
        _make_project(projects_dir, "Good")

        result = find_projects(projects_dir)
        assert "Good" in result
        assert "_archives" not in result

    def test_skips_special_dirs(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        (projects_dir / "__pycache__").mkdir()
        _make_project(projects_dir, "Real")

        result = find_projects(projects_dir)
        assert "__pycache__" not in result
        assert "Real" in result

    def test_empty_dir(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        (projects_dir / "EmptyDir").mkdir()

        result = find_projects(projects_dir)
        assert "EmptyDir" in result  # found but has no code

    def test_ignores_files(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        (projects_dir / "notes.txt").write_text("hello", encoding="utf-8")
        _make_project(projects_dir, "Proj")

        result = find_projects(projects_dir)
        assert len(result) == 1


# ---------------------------------------------------------------------------
# parse_readme_projects
# ---------------------------------------------------------------------------

class TestParseReadmeProjects:
    def test_extracts_project_links(self, tmp_path):
        readme = _make_readme(tmp_path, textwrap.dedent("""\
            | Name | Description |
            |------|-------------|
            | [Alpha](Alpha/) | Test |
            | [Beta](Beta/) | Test |
        """))
        names = parse_readme_projects(readme)
        assert names == {"Alpha", "Beta"}

    def test_extracts_nested_links(self, tmp_path):
        readme = _make_readme(tmp_path, "[Proj](path/to/Proj/)")
        names = parse_readme_projects(readme)
        assert "Proj" in names

    def test_skips_http_links(self, tmp_path):
        readme = _make_readme(tmp_path, "[Docs](https://example.com)")
        names = parse_readme_projects(readme)
        assert len(names) == 0

    def test_skips_file_extensions(self, tmp_path):
        readme = _make_readme(tmp_path, "[file](script.py)")
        names = parse_readme_projects(readme)
        assert len(names) == 0

    def test_nonexistent_readme(self, tmp_path):
        names = parse_readme_projects(tmp_path / "nonexistent.md")
        assert names == set()


# ---------------------------------------------------------------------------
# parse_readme_counts
# ---------------------------------------------------------------------------

class TestParseReadmeCounts:
    def test_extracts_counts(self, tmp_path):
        readme = _make_readme(tmp_path, "We have **42 strategies** and **8 clones**.")
        counts = parse_readme_counts(readme)
        assert counts is not None
        assert counts.get("strategies") == 42
        assert counts.get("clones") == 8

    def test_empty_readme(self, tmp_path):
        readme = _make_readme(tmp_path, "No numbers here.")
        counts = parse_readme_counts(readme)
        assert counts is None

    def test_nonexistent_readme(self, tmp_path):
        counts = parse_readme_counts(tmp_path / "missing.md")
        assert counts is None


# ---------------------------------------------------------------------------
# check_duplicate_sources
# ---------------------------------------------------------------------------

class TestCheckDuplicateSources:
    def test_detects_duplicate(self, tmp_path):
        # Create canonical project
        projects = tmp_path / "projects"
        projects.mkdir()
        _make_project(projects, "EMA-Cross-Alpha")

        # Create duplicate in imported
        imported = tmp_path / "projects-imported"
        imported.mkdir()
        _make_project(imported, "ema_cross_alpha")

        issues = check_duplicate_sources(tmp_path)
        assert any("DUPLICATE" in i for i in issues)

    def test_no_duplicates(self, tmp_path):
        projects = tmp_path / "projects"
        projects.mkdir()
        _make_project(projects, "Unique")

        issues = check_duplicate_sources(tmp_path)
        assert len(issues) == 0

    def test_missing_source_dirs_ok(self, tmp_path):
        projects = tmp_path / "projects"
        projects.mkdir()
        _make_project(projects, "Proj")

        # No projects-imported etc. — should not crash
        issues = check_duplicate_sources(tmp_path)
        assert len(issues) == 0


# ---------------------------------------------------------------------------
# validate (integration)
# ---------------------------------------------------------------------------

class TestValidate:
    def test_all_good(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        _make_project(projects_dir, "Alpha")
        readme = _make_readme(projects_dir, "[Alpha](Alpha/)")
        # validate expects readme_path directly
        issues = validate(projects_dir, readme)
        assert any("SUMMARY" in i for i in issues)
        # No errors if Alpha is both on disk and in README
        errors = [i for i in issues if not i.startswith("SUMMARY")]
        assert len(errors) == 0

    def test_missing_on_disk(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        readme = _make_readme(projects_dir, "[Ghost](Ghost/)")
        issues = validate(projects_dir, readme)
        assert any("MISSING_ON_DISK" in i for i in issues)

    def test_missing_in_readme(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        _make_project(projects_dir, "Orphan")
        readme = _make_readme(projects_dir, "No links here.")
        issues = validate(projects_dir, readme)
        assert any("MISSING_IN_README" in i for i in issues)

    def test_empty_project_detected(self, tmp_path):
        projects_dir = tmp_path / "projects"
        projects_dir.mkdir()
        (projects_dir / "EmptyProj").mkdir()
        readme = _make_readme(projects_dir, "[EmptyProj](EmptyProj/)")
        issues = validate(projects_dir, readme)
        assert any("NO_CODE" in i for i in issues)
