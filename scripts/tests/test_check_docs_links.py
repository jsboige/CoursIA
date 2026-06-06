"""Tests for scripts/check_docs_links.py — link checker and orphan detector.

Validates all acceptance criteria from issue #2453:
- Detects broken links (0 false negatives)
- Detects orphan docs
- Self-checks (script does not break anything)
- Baseline write/read roundtrip
- Regression detection vs baseline
"""

import json
import textwrap
from pathlib import Path

import pytest

# Import from the module under test
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_docs_links import (
    BASELINE_PATH,
    LinkRef,
    ScanResult,
    check_link,
    check_regression,
    find_orphan_docs,
    find_scan_files,
    format_report,
    load_baseline,
    run_scan,
    scan_file,
    write_baseline,
    _is_valid_target,
    _should_skip,
    REPO_ROOT,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

class TestIsValidTarget:
    """Test the link target filter."""

    def test_relative_md(self):
        assert _is_valid_target("docs/common-commands.md") is True

    def test_relative_py(self):
        assert _is_valid_target("scripts/check_docs_links.py") is True

    def test_http_url(self):
        assert _is_valid_target("https://example.com") is False

    def test_mailto(self):
        assert _is_valid_target("mailto:user@example.com") is False

    def test_anchor(self):
        assert _is_valid_target("#section") is False

    def test_empty(self):
        assert _is_valid_target("") is False

    def test_template_variable(self):
        assert _is_valid_target("{connection_file}") is False

    def test_absolute_path(self):
        assert _is_valid_target("/absolute/path.md") is False

    def test_directory_traversal(self):
        assert _is_valid_target("../other/file.md") is True

    def test_image(self):
        assert _is_valid_target("images/diagram.png") is True


class TestShouldSkip:
    """Test the path skip filter."""

    def test_lake_dir(self):
        p = REPO_ROOT / ".lake" / "packages" / "foo" / "README.md"
        assert _should_skip(p) is True

    def test_node_modules(self):
        p = REPO_ROOT / "node_modules" / "pkg" / "readme.md"
        assert _should_skip(p) is True

    def test_normal_file(self):
        p = REPO_ROOT / "docs" / "common-commands.md"
        assert _should_skip(p) is False

    def test_git_dir(self):
        p = REPO_ROOT / ".git" / "HEAD"
        assert _should_skip(p) is True

    def test_output_file(self):
        p = REPO_ROOT / "MyIA.AI.Notebooks" / "Search" / "_output" / "nb.ipynb"
        assert _should_skip(p) is True


class TestScanFile:
    """Test link extraction from markdown content."""

    def test_extracts_relative_link(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("# Title\n\nSee [guide](docs/guide.md) for details.\n")
        refs = scan_file(f)
        assert len(refs) == 1
        assert refs[0].target == "docs/guide.md"
        assert refs[0].text == "guide"
        assert refs[0].line == 3

    def test_skips_code_block_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text(textwrap.dedent("""\
            # Title
            ```bash
            # See [old link](docs/deprecated.md)
            echo "hello"
            ```
            [valid](docs/valid.md)
        """))
        refs = scan_file(f)
        assert len(refs) == 1
        assert refs[0].target == "docs/valid.md"

    def test_skips_http_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[web](https://example.com) [local](docs/local.md)\n")
        refs = scan_file(f)
        assert len(refs) == 1
        assert refs[0].target == "docs/local.md"

    def test_skips_anchor_only(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[section](#top)\n")
        refs = scan_file(f)
        assert len(refs) == 0

    def test_multiple_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[a](docs/a.md) and [b](docs/b.md) and [c](docs/c.md)\n")
        refs = scan_file(f)
        assert len(refs) == 3

    def test_handles_utf8(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("# Titre\n\nVoir [guide](docs/guide.md) pour les détails.\n",
                     encoding="utf-8")
        refs = scan_file(f)
        assert len(refs) == 1

    def test_handles_read_error(self, tmp_path):
        """Gracefully handles files that cannot be read."""
        f = tmp_path / "nonexistent.md"
        refs = scan_file(f)
        assert refs == []


class TestCheckLink:
    """Test link resolution.

    check_link takes a root= parameter for safety (within-repo check).
    In tests, we pass root=tmp_path so tmp files are accepted.
    """

    def test_existing_file(self, tmp_path):
        target = tmp_path / "target.md"
        target.write_text("# Target\n")
        source = tmp_path / "source.md"
        assert check_link("target.md", source, root=tmp_path) is True

    def test_missing_file(self, tmp_path):
        source = tmp_path / "source.md"
        assert check_link("nonexistent.md", source, root=tmp_path) is False

    def test_subdirectory_link(self, tmp_path):
        sub = tmp_path / "docs"
        sub.mkdir()
        (sub / "guide.md").write_text("# Guide\n")
        source = tmp_path / "README.md"
        assert check_link("docs/guide.md", source, root=tmp_path) is True

    def test_parent_directory_link(self, tmp_path):
        parent_file = tmp_path / "parent.md"
        parent_file.write_text("# Parent\n")
        subdir = tmp_path / "sub"
        subdir.mkdir()
        source = subdir / "child.md"
        assert check_link("../parent.md", source, root=tmp_path) is True

    def test_path_with_spaces(self, tmp_path):
        target = tmp_path / "my file.md"
        target.write_text("# Content\n")
        source = tmp_path / "source.md"
        assert check_link("my file.md", source, root=tmp_path) is True


class TestBrokenLinkDetection:
    """Integration test: detects a deliberately injected broken link."""

    def test_detects_injected_broken_link(self, tmp_path, monkeypatch):
        """Acceptance: script detects a broken link injected for testing."""
        # Create a temp repo structure
        readme = tmp_path / "README.md"
        readme.write_text("[broken](docs/does_not_exist.md)\n")
        docs_dir = tmp_path / "docs"
        docs_dir.mkdir()

        # Monkeypatch REPO_ROOT to use tmp_path
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        monkeypatch.setattr("check_docs_links.BASELINE_PATH",
                            tmp_path / "baseline.json")

        result = run_scan(report_orphans=True)
        assert len(result.broken) >= 1
        broken_targets = [r.target for r in result.broken]
        assert "docs/does_not_exist.md" in broken_targets


class TestOrphanDetection:
    """Test orphan file detection."""

    def test_finds_unreferenced_doc(self, tmp_path, monkeypatch):
        """An .md file in docs/ not referenced anywhere is reported as orphan."""
        readme = tmp_path / "README.md"
        readme.write_text("# No links here\n")
        docs = tmp_path / "docs"
        docs.mkdir()
        (docs / "orphan.md").write_text("# Nobody links to me\n")

        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        monkeypatch.setattr("check_docs_links.BASELINE_PATH",
                            tmp_path / "baseline.json")

        result = run_scan(report_orphans=True)
        assert "docs/orphan.md" in result.orphans

    def test_referenced_file_not_orphan(self, tmp_path, monkeypatch):
        """A file that IS referenced is not reported as orphan."""
        docs = tmp_path / "docs"
        docs.mkdir()
        (docs / "referenced.md").write_text("# I am linked\n")
        readme = tmp_path / "README.md"
        readme.write_text("[link](docs/referenced.md)\n")

        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        monkeypatch.setattr("check_docs_links.BASELINE_PATH",
                            tmp_path / "baseline.json")

        result = run_scan(report_orphans=True)
        assert "docs/referenced.md" not in result.orphans


class TestBaseline:
    """Test baseline write/read roundtrip."""

    def test_write_and_load(self, tmp_path):
        baseline_path = tmp_path / "baseline.json"
        result = ScanResult(
            broken=[
                LinkRef(source="README.md", target="docs/missing.md",
                        line=5, text="link"),
            ],
            orphans=["docs/old.md"],
            scanned_files=10,
            total_links=50,
        )
        write_baseline(result, baseline_path)

        loaded = load_baseline(baseline_path)
        assert loaded is not None
        assert len(loaded["broken_links"]) == 1
        assert loaded["broken_links"][0]["target"] == "docs/missing.md"
        assert loaded["orphans"] == ["docs/old.md"]
        assert loaded["scanned_files"] == 10
        assert loaded["total_links"] == 50

    def test_load_missing_baseline(self):
        loaded = load_baseline(Path("/nonexistent/baseline.json"))
        assert loaded is None


class TestRegressionDetection:
    """Test regression detection vs baseline."""

    def test_new_broken_link_is_regression(self):
        baseline = {
            "broken_links": [
                {"source": "README.md", "target": "docs/old_broken.md",
                 "line": 1, "text": "old"},
            ],
        }
        result = ScanResult(
            broken=[
                LinkRef(source="README.md", target="docs/old_broken.md",
                        line=1, text="old"),
                LinkRef(source="CLAUDE.md", target="docs/NEW_broken.md",
                        line=10, text="new"),
            ],
        )
        new_broken = check_regression(result, baseline)
        assert len(new_broken) == 1
        assert new_broken[0].target == "docs/NEW_broken.md"

    def test_no_new_broken_links(self):
        baseline = {
            "broken_links": [
                {"source": "README.md", "target": "docs/old.md",
                 "line": 1, "text": "old"},
            ],
        }
        result = ScanResult(
            broken=[
                LinkRef(source="README.md", target="docs/old.md",
                        line=1, text="old"),
            ],
        )
        new_broken = check_regression(result, baseline)
        assert len(new_broken) == 0

    def test_fixed_link_not_flagged(self):
        """A previously broken link that is now valid is NOT a regression."""
        baseline = {
            "broken_links": [
                {"source": "README.md", "target": "docs/was_broken.md",
                 "line": 1, "text": "was broken"},
            ],
        }
        result = ScanResult(broken=[])  # All fixed now
        new_broken = check_regression(result, baseline)
        assert len(new_broken) == 0


class TestSelfCheck:
    """Acceptance: the script itself does not break anything."""

    def test_script_runs_on_repo(self):
        """The link checker runs successfully on the actual repo."""
        result = run_scan(report_orphans=False)
        # Should not crash, should return a ScanResult
        assert isinstance(result, ScanResult)
        assert result.scanned_files > 0
        assert result.total_links > 0

    def test_scan_files_include_key_targets(self):
        """Verify key files are included in the scan."""
        files = find_scan_files()
        rel_paths = {str(f.relative_to(REPO_ROOT)).replace("\\", "/")
                     for f in files}
        # CLAUDE.md should be scanned
        assert "CLAUDE.md" in rel_paths
        # docs/ files should be scanned
        assert any(p.startswith("docs/") for p in rel_paths)
        # .claude/rules/ should be scanned
        assert any(p.startswith(".claude/rules/") for p in rel_paths)

    def test_skip_dirs_not_included(self):
        """Verify .lake/ and other skip dirs are not scanned."""
        files = find_scan_files()
        for f in files:
            parts = Path(f).parts
            for skip in (".lake", "node_modules", ".git", "_output"):
                assert skip not in parts, f"Found skip dir {skip} in {f}"


# ---------------------------------------------------------------------------
# format_report
# ---------------------------------------------------------------------------


class TestFormatReport:
    """Tests for format_report — human-readable scan result formatting."""

    def test_no_broken_no_orphans(self):
        """Clean scan produces 'No broken links found'."""
        result = ScanResult(scanned_files=10, total_links=50, broken=[], valid=[], orphans=[])
        report = format_report(result)
        assert "Scanned 10 files, 50 links" in report
        assert "No broken links found" in report
        assert "Orphan" not in report

    def test_with_broken_links(self):
        """Broken links are listed with source:line -> target."""
        result = ScanResult(
            scanned_files=5, total_links=20,
            broken=[
                LinkRef(source="docs/a.md", target="missing.md", line=10, text="link"),
                LinkRef(source="README.md", target="gone.md", line=5, text="ref"),
            ],
            valid=[], orphans=[],
        )
        report = format_report(result)
        assert "Broken links (2)" in report
        assert "docs/a.md:10 -> missing.md" in report
        assert "README.md:5 -> gone.md" in report

    def test_with_orphans(self):
        """Orphans shown when show_orphans=True."""
        result = ScanResult(
            scanned_files=3, total_links=10, broken=[], valid=[],
            orphans=["docs/orphan.md", "docs/lonely.md"],
        )
        report = format_report(result, show_orphans=True)
        assert "Orphan docs (2)" in report
        assert "docs/orphan.md" in report
        assert "docs/lonely.md" in report

    def test_orphans_hidden_by_default(self):
        """Orphans not shown when show_orphans=False (default)."""
        result = ScanResult(
            scanned_files=3, total_links=10, broken=[], valid=[],
            orphans=["docs/orphan.md"],
        )
        report = format_report(result, show_orphans=False)
        assert "Orphan" not in report

    def test_broken_sorted_by_source_and_line(self):
        """Broken links are sorted by (source, line)."""
        result = ScanResult(
            scanned_files=2, total_links=5,
            broken=[
                LinkRef(source="b.md", target="x", line=5, text=""),
                LinkRef(source="a.md", target="y", line=10, text=""),
                LinkRef(source="a.md", target="z", line=3, text=""),
            ],
            valid=[], orphans=[],
        )
        report = format_report(result)
        # a.md:3 before a.md:10 before b.md:5
        pos_a3 = report.index("a.md:3")
        pos_a10 = report.index("a.md:10")
        pos_b5 = report.index("b.md:5")
        assert pos_a3 < pos_a10 < pos_b5

    def test_empty_scan(self):
        """Zero files scanned produces valid report."""
        result = ScanResult(scanned_files=0, total_links=0, broken=[], valid=[], orphans=[])
        report = format_report(result)
        assert "Scanned 0 files, 0 links" in report
        assert "No broken links found" in report


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
