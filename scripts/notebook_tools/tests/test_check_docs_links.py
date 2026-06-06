"""Tests for scripts/check_docs_links.py — docs/ link checker (rewritten API)."""

import importlib.util
import json
from pathlib import Path
from unittest.mock import patch

import pytest

# Load module by file path
_MOD_PATH = (
    Path(__file__).resolve().parent.parent.parent.parent
    / "scripts"
    / "check_docs_links.py"
)
_spec = importlib.util.spec_from_file_location("check_docs_links", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

scan_file = _mod.scan_file
check_link = _mod.check_link
find_scan_files = _mod.find_scan_files
find_orphan_docs = _mod.find_orphan_docs
run_scan = _mod.run_scan
write_baseline = _mod.write_baseline
load_baseline = _mod.load_baseline
check_regression = _mod.check_regression
format_report = _mod.format_report
LINK_PATTERN = _mod.LINK_PATTERN
REPO_ROOT = _mod.REPO_ROOT
LinkRef = _mod.LinkRef
ScanResult = _mod.ScanResult


# --- scan_file ---


class TestScanFile:
    def test_finds_relative_link(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("See [docs](docs/guide.md) for details.", encoding="utf-8")
        results = scan_file(f)
        assert len(results) == 1
        assert results[0].target == "docs/guide.md"
        assert results[0].line == 1
        assert results[0].text == "docs"

    def test_no_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("No links here.", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_multiple_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text(
            "[A](docs/a.md)\n[B](docs/b.md)\n[C](docs/c.md)\n",
            encoding="utf-8",
        )
        results = scan_file(f)
        assert len(results) == 3

    def test_skips_http_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[external](https://example.com)", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_skips_anchor_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[section](#intro)", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_skips_mailto_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[email](mailto:user@example.com)", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_line_numbers(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("line1\nline2\n[link](docs/x.md)\n", encoding="utf-8")
        results = scan_file(f)
        assert results[0].line == 3

    def test_unicode_content(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[doc](docs/guide.md) — accentué", encoding="utf-8")
        results = scan_file(f)
        assert len(results) == 1

    def test_skips_code_blocks(self, tmp_path):
        """Links inside fenced code blocks must be ignored."""
        f = tmp_path / "test.md"
        f.write_text(
            "```\n[fake](docs/should-not-match.md)\n```\n",
            encoding="utf-8",
        )
        results = scan_file(f)
        assert results == []

    def test_skips_bare_directory_without_extension(self, tmp_path):
        """Targets without a file extension and not ending with / are skipped."""
        f = tmp_path / "test.md"
        f.write_text("[link](some-dir)", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_handles_nonexistent_file(self, tmp_path):
        """scan_file returns empty list for unreadable files."""
        f = tmp_path / "nonexistent.md"
        results = scan_file(f)
        assert results == []


# --- check_link ---


class TestCheckLink:
    def test_existing_file(self, tmp_path):
        target = tmp_path / "docs" / "guide.md"
        target.parent.mkdir(parents=True)
        target.write_text("content", encoding="utf-8")
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        assert check_link("docs/guide.md", source, root=tmp_path) is True

    def test_missing_file(self, tmp_path):
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        assert check_link("docs/nonexistent.md", source, root=tmp_path) is False

    def test_link_outside_repo(self, tmp_path):
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        result = check_link("../../etc/passwd", source, root=tmp_path)
        assert result is False

    def test_nested_path(self, tmp_path):
        target = tmp_path / "docs" / "sub" / "deep.md"
        target.parent.mkdir(parents=True)
        target.write_text("deep", encoding="utf-8")
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        assert check_link("docs/sub/deep.md", source, root=tmp_path) is True

    def test_existing_directory(self, tmp_path):
        """Links to existing directories should work."""
        target = tmp_path / "docs" / "subdir"
        target.mkdir(parents=True)
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        assert check_link("docs/subdir/", source, root=tmp_path) is True


# --- LINK_PATTERN ---


class TestLinkPattern:
    def test_matches_docs_link(self):
        m = LINK_PATTERN.search("[text](docs/guide.md)")
        assert m is not None
        assert m.group(1) == "text"
        assert m.group(2) == "docs/guide.md"

    def test_no_match_external(self):
        m = LINK_PATTERN.search("[text](https://example.com)")
        assert m is None

    def test_match_image_extension(self):
        """Image links should be checked too."""
        m = LINK_PATTERN.search("[img](docs/image.png)")
        assert m is not None
        assert m.group(2) == "docs/image.png"

    def test_match_with_hash(self):
        # Links with # fragment should NOT match (pattern excludes #)
        m = LINK_PATTERN.search("[text](docs/guide.md#section)")
        assert m is None

    def test_match_various_names(self):
        for name in ["docs/a.md", "docs/foo_bar-baz.md", "docs/sub/dir.md"]:
            m = LINK_PATTERN.search(f"[x]({name})")
            assert m is not None, f"Should match {name}"


# --- find_scan_files ---


class TestFindScanFiles:
    def test_finds_readme(self, tmp_path):
        (tmp_path / "README.md").write_text("# Test", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path), \
             patch.object(_mod, "SCAN_SCOPES", []):
            files = find_scan_files()
            assert any(f.name == "README.md" for f in files)

    def test_skips_git_dir(self, tmp_path):
        git_dir = tmp_path / ".git"
        git_dir.mkdir()
        (git_dir / "README.md").write_text("# git", encoding="utf-8")
        (tmp_path / "README.md").write_text("# root", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path), \
             patch.object(_mod, "SCAN_SCOPES", []):
            files = find_scan_files()
            assert not any(".git" in str(f) for f in files)

    def test_excludes_archived_dirs(self, tmp_path):
        arch = tmp_path / "_archives"
        arch.mkdir()
        (arch / "README.md").write_text("# old", encoding="utf-8")
        (tmp_path / "README.md").write_text("# root", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path), \
             patch.object(_mod, "SCAN_SCOPES", []):
            files = find_scan_files()
            paths = [str(f) for f in files]
            assert all("_archives" not in p for p in paths), f"Found archives: {paths}"

    def test_finds_scope_file(self, tmp_path):
        claude_md = tmp_path / "CLAUDE.md"
        claude_md.write_text("# Project", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path), \
             patch.object(_mod, "SCAN_SCOPES", ["CLAUDE.md"]):
            files = find_scan_files()
            assert any(f.name == "CLAUDE.md" for f in files)


# --- find_orphan_docs ---


class TestFindOrphanDocs:
    def test_finds_orphan(self, tmp_path):
        """A .md file in docs/ not referenced anywhere should be an orphan."""
        docs = tmp_path / "docs"
        docs.mkdir()
        orphan = docs / "orphan.md"
        orphan.write_text("# Lonely", encoding="utf-8")
        # No files reference it
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            orphans = find_orphan_docs([], [])
            assert "docs/orphan.md" in orphans

    def test_referenced_not_orphan(self, tmp_path):
        """A .md file referenced by a scanned file is not an orphan."""
        docs = tmp_path / "docs"
        docs.mkdir()
        referenced = docs / "guide.md"
        referenced.write_text("# Guide", encoding="utf-8")
        source = tmp_path / "README.md"
        source.write_text("[guide](docs/guide.md)", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            refs = scan_file(source)
            orphans = find_orphan_docs([source], refs)
            assert "docs/guide.md" not in orphans


# --- baseline write/read ---


class TestBaseline:
    def test_write_and_load(self, tmp_path):
        result = ScanResult(
            broken=[
                LinkRef(source="test.md", target="missing.md", line=1, text="link")
            ],
            valid=[],
            orphans=["docs/orphan.md"],
            scanned_files=5,
            total_links=10,
        )
        baseline_path = tmp_path / "baseline.json"
        write_baseline(result, path=baseline_path)

        loaded = load_baseline(path=baseline_path)
        assert loaded is not None
        assert loaded["scanned_files"] == 5
        assert loaded["total_links"] == 10
        assert len(loaded["broken_links"]) == 1
        assert loaded["broken_links"][0]["source"] == "test.md"
        assert loaded["orphans"] == ["docs/orphan.md"]

    def test_load_missing_returns_none(self, tmp_path):
        loaded = load_baseline(path=tmp_path / "nonexistent.json")
        assert loaded is None


# --- check_regression ---


class TestCheckRegression:
    def test_new_broken_link(self):
        baseline = {
            "broken_links": [
                {"source": "old.md", "target": "old_missing.md", "line": 1, "text": "old"}
            ],
        }
        result = ScanResult(
            broken=[
                LinkRef(source="old.md", target="old_missing.md", line=1, text="old"),
                LinkRef(source="new.md", target="new_missing.md", line=5, text="new"),
            ],
            valid=[],
            orphans=[],
            scanned_files=2,
            total_links=10,
        )
        new_broken = check_regression(result, baseline)
        assert len(new_broken) == 1
        assert new_broken[0].source == "new.md"

    def test_no_new_broken(self):
        baseline = {
            "broken_links": [
                {"source": "old.md", "target": "old_missing.md", "line": 1, "text": "old"}
            ],
        }
        result = ScanResult(
            broken=[
                LinkRef(source="old.md", target="old_missing.md", line=1, text="old"),
            ],
            valid=[],
            orphans=[],
            scanned_files=2,
            total_links=10,
        )
        new_broken = check_regression(result, baseline)
        assert len(new_broken) == 0


# --- format_report ---


class TestFormatReport:
    def test_with_broken(self):
        result = ScanResult(
            broken=[
                LinkRef(source="test.md", target="missing.md", line=1, text="link")
            ],
            valid=[],
            orphans=[],
            scanned_files=5,
            total_links=10,
        )
        report = format_report(result)
        assert "Broken links (1)" in report
        assert "test.md" in report

    def test_no_broken(self):
        result = ScanResult(
            broken=[], valid=[], orphans=[], scanned_files=5, total_links=10
        )
        report = format_report(result)
        assert "No broken links found" in report

    def test_with_orphans(self):
        result = ScanResult(
            broken=[],
            valid=[],
            orphans=["docs/orphan.md"],
            scanned_files=5,
            total_links=10,
        )
        report = format_report(result, show_orphans=True)
        assert "Orphan docs" in report


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
