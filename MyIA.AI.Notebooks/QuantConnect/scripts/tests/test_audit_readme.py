"""Tests for audit_readme.py — QC README pedagogical auditor."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from audit_readme import ReadmeAuditor, ReadmeStats


# --- ReadmeStats dataclass ---

class TestReadmeStats:
    def test_defaults(self):
        s = ReadmeStats(path="x/README.md")
        assert s.path == "x/README.md"
        assert s.lines == 0
        assert s.words == 0
        assert s.has_title is False
        assert s.sections == []
        assert s.broken_links == []
        assert s.missing_sections == []

    def test_field_factories_independent(self):
        a = ReadmeStats(path="a")
        b = ReadmeStats(path="b")
        a.sections.append("S")
        assert b.sections == []


# --- classify_readme ---

class TestClassifyReadme:
    """classify_readme only inspects path.parts, no file I/O — use synthetic Paths
    to keep behaviour portable across Linux (/tmp/...) and Windows tmp_path
    (C:\\Users\\...\\AppData\\Local\\Temp\\...) which has many parts and would
    break the len(parts) <= 7 MAIN heuristic."""

    def setup_method(self):
        self.auditor = ReadmeAuditor("/tmp")

    def test_course_example(self):
        p = Path("partner-course-quant-trading") / "examples" / "ex1" / "README.md"
        assert self.auditor.classify_readme(p) == "COURSE_EXAMPLE"

    def test_course_template(self):
        p = Path("partner-course-quant-trading") / "templates" / "t1" / "README.md"
        assert self.auditor.classify_readme(p) == "COURSE_TEMPLATE"

    def test_course_main(self):
        p = Path("partner-course-quant-trading") / "README.md"
        assert self.auditor.classify_readme(p) == "COURSE_MAIN"

    def test_project(self):
        p = Path("projects") / "Strategy" / "README.md"
        assert self.auditor.classify_readme(p) == "PROJECT"

    def test_main_at_root(self):
        p = Path("README.md")
        assert self.auditor.classify_readme(p) == "MAIN"

    def test_other_deeply_nested(self):
        p = Path("a") / "b" / "c" / "d" / "e" / "f" / "g" / "h" / "README.md"
        assert self.auditor.classify_readme(p) == "OTHER"

    def test_partner_examples_takes_precedence_over_project(self):
        # "partner-course-quant-trading" + "examples" wins even with "projects" present
        p = Path("partner-course-quant-trading") / "examples" / "projects" / "README.md"
        assert self.auditor.classify_readme(p) == "COURSE_EXAMPLE"


# --- extract_sections ---

class TestExtractSections:
    def setup_method(self):
        self.auditor = ReadmeAuditor("/tmp")

    def test_simple_sections(self):
        content = "## Intro\nbody\n## Usage\nmore"
        assert self.auditor.extract_sections(content) == ["Intro", "Usage"]

    def test_ignores_h1_and_h3(self):
        content = "# Title\n## Section\n### Sub\n## Other"
        assert self.auditor.extract_sections(content) == ["Section", "Other"]

    def test_empty(self):
        assert self.auditor.extract_sections("") == []

    def test_no_h2(self):
        assert self.auditor.extract_sections("# Only H1\ntext") == []

    def test_unicode_titles(self):
        content = "## Vue d'Ensemble\n## Démarrage Rapide"
        assert self.auditor.extract_sections(content) == ["Vue d'Ensemble", "Démarrage Rapide"]


# --- check_links ---

class TestCheckLinks:
    def setup_method(self):
        self.auditor = ReadmeAuditor("/tmp")

    def test_external_https_ignored(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("[ext](https://example.com)", encoding="utf-8")
        assert self.auditor.check_links(readme.read_text(encoding="utf-8"), readme) == []

    def test_anchor_ignored(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("[anchor](#section)", encoding="utf-8")
        assert self.auditor.check_links(readme.read_text(encoding="utf-8"), readme) == []

    def test_relative_existing(self, tmp_path):
        readme = tmp_path / "README.md"
        target = tmp_path / "other.md"
        target.touch()
        readme.write_text("[t](other.md)", encoding="utf-8")
        assert self.auditor.check_links(readme.read_text(encoding="utf-8"), readme) == []

    def test_relative_broken(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("[t](missing.md)", encoding="utf-8")
        assert self.auditor.check_links(readme.read_text(encoding="utf-8"), readme) == ["missing.md"]

    def test_mixed(self, tmp_path):
        readme = tmp_path / "README.md"
        ok = tmp_path / "ok.md"
        ok.touch()
        readme.write_text(
            "[ext](https://x.io) [anchor](#a) [ok](ok.md) [bad](nope.md)",
            encoding="utf-8",
        )
        assert self.auditor.check_links(readme.read_text(encoding="utf-8"), readme) == ["nope.md"]


# --- find_readmes ---

class TestFindReadmes:
    def test_finds_nested(self, tmp_path):
        (tmp_path / "README.md").touch()
        (tmp_path / "sub").mkdir()
        (tmp_path / "sub" / "README.md").touch()
        auditor = ReadmeAuditor(str(tmp_path))
        found = auditor.find_readmes()
        assert len(found) == 2

    def test_excludes_data_folder(self, tmp_path):
        (tmp_path / "README.md").touch()
        (tmp_path / "data").mkdir()
        (tmp_path / "data" / "README.md").touch()
        (tmp_path / "data" / "sub").mkdir()
        (tmp_path / "data" / "sub" / "README.md").touch()
        auditor = ReadmeAuditor(str(tmp_path))
        found = auditor.find_readmes()
        # Only the root README, both data/ ones excluded
        assert len(found) == 1
        assert found[0].name == "README.md"
        assert "data" not in found[0].parts

    def test_empty_tree(self, tmp_path):
        auditor = ReadmeAuditor(str(tmp_path))
        assert auditor.find_readmes() == []


# --- analyze_readme ---

class TestAnalyzeReadme:
    def test_basic_structure(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text(
            "# Title\n\n" + ("word " * 60) + "\n\n## Usage\ntext\n## Examples\ntext\n",
            encoding="utf-8",
        )
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        assert stats.has_title is True
        assert stats.has_description is True  # > 50 words
        assert "Usage" in stats.sections
        assert "Examples" in stats.sections
        assert stats.has_examples is True
        assert stats.has_usage is True

    def test_thin_readme(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# Title\nshort", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        assert stats.has_title is True
        assert stats.has_description is False  # <= 50 words
        assert stats.sections == []

    def test_project_missing_sections(self, tmp_path):
        # Use PROJECT type because it classifies on path keyword ("projects"),
        # independent of tmp_path depth (avoids fragile len(parts) <= 7 heuristic).
        (tmp_path / "projects" / "Strat").mkdir(parents=True)
        readme = tmp_path / "projects" / "Strat" / "README.md"
        readme.write_text("# Title\n## Random\n", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        # PROJECT expects Description, Stratégie, Performance, Installation, Utilisation
        assert len(stats.missing_sections) > 0

    def test_broken_link_detected(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# T\n[bad](missing.md)\n", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        assert "missing.md" in stats.broken_links

    def test_requirements_keyword(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# T\n## Setup\nPrérequis: python 3.10\n", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        assert stats.has_requirements is True

    def test_links_flag(self, tmp_path):
        readme = tmp_path / "README.md"
        readme.write_text("# T\n[x](https://a)\n", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        stats = auditor.analyze_readme(readme)
        assert stats.has_links is True


# --- audit_all integration ---

class TestAuditAll:
    def test_empty_dir(self, tmp_path):
        auditor = ReadmeAuditor(str(tmp_path))
        results = auditor.audit_all()
        assert results == {}
        assert auditor.readmes == []

    def test_categorizes(self, tmp_path):
        # Use PROJECT + COURSE_MAIN since they classify on path keyword,
        # not on len(parts) heuristic (Windows tmp_path is deeply nested).
        (tmp_path / "README.md").write_text("# Root", encoding="utf-8")
        (tmp_path / "projects").mkdir()
        (tmp_path / "projects" / "Strat").mkdir()
        (tmp_path / "projects" / "Strat" / "README.md").write_text("# Strat", encoding="utf-8")
        (tmp_path / "partner-course-quant-trading").mkdir()
        (tmp_path / "partner-course-quant-trading" / "README.md").write_text("# Course", encoding="utf-8")
        auditor = ReadmeAuditor(str(tmp_path))
        results = auditor.audit_all()
        assert "PROJECT" in results
        assert "COURSE_MAIN" in results
        assert len(auditor.readmes) == 3


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
