"""Tests for scripts/check_docs_links.py — docs/ link checker."""

import importlib.util
import json
import re
from pathlib import Path
from unittest.mock import patch

import pytest

# Load module by file path
_MOD_PATH = Path(__file__).resolve().parent.parent.parent.parent / "scripts" / "check_docs_links.py"
_spec = importlib.util.spec_from_file_location("check_docs_links", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

scan_file = _mod.scan_file
check_link = _mod.check_link
find_readmes = _mod.find_readmes
LINK_PATTERN = _mod.LINK_PATTERN
REPO_ROOT = _mod.REPO_ROOT


# --- scan_file ---


class TestScanFile:
    def test_finds_docs_link(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("See [docs](docs/guide.md) for details.", encoding="utf-8")
        results = scan_file(f)
        assert len(results) == 1
        assert results[0] == ("docs", "docs/guide.md", 1)

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

    def test_skips_non_docs_links(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[external](https://example.com)\n[local](other.md)", encoding="utf-8")
        results = scan_file(f)
        assert results == []

    def test_line_numbers(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("line1\nline2\n[link](docs/x.md)\n", encoding="utf-8")
        results = scan_file(f)
        assert results[0][2] == 3  # line 3

    def test_unicode_file(self, tmp_path):
        f = tmp_path / "test.md"
        f.write_text("[doc](docs/guide.md) — accentué", encoding="utf-8")
        results = scan_file(f)
        assert len(results) == 1

    def test_missing_file(self, tmp_path):
        """scan_file does NOT catch FileNotFoundError — only Unicode/Permission errors."""
        f = tmp_path / "nonexistent.md"
        with pytest.raises(FileNotFoundError):
            scan_file(f)


# --- check_link ---


class TestCheckLink:
    def test_existing_file(self, tmp_path):
        target = tmp_path / "docs" / "guide.md"
        target.parent.mkdir(parents=True)
        target.write_text("content", encoding="utf-8")
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            assert check_link("docs/guide.md", source) is True

    def test_missing_file(self, tmp_path):
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            assert check_link("docs/nonexistent.md", source) is False

    def test_link_outside_repo(self, tmp_path):
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        # A path that resolves outside the source directory
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            result = check_link("../../etc/passwd", source)
            assert result is False

    def test_nested_path(self, tmp_path):
        target = tmp_path / "docs" / "sub" / "deep.md"
        target.parent.mkdir(parents=True)
        target.write_text("deep", encoding="utf-8")
        source = tmp_path / "test.md"
        source.write_text("", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            assert check_link("docs/sub/deep.md", source) is True


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

    def test_no_match_non_md(self):
        m = LINK_PATTERN.search("[text](docs/image.png)")
        assert m is None

    def test_match_with_hash(self):
        # Links with # fragment should NOT match (pattern excludes #)
        m = LINK_PATTERN.search("[text](docs/guide.md#section)")
        assert m is None

    def test_match_various_names(self):
        for name in ["docs/a.md", "docs/foo_bar-baz.md", "docs/sub/dir.md"]:
            m = LINK_PATTERN.search(f"[x]({name})")
            assert m is not None, f"Should match {name}"


# --- find_readmes ---


class TestFindReadmes:
    def test_finds_readme(self, tmp_path):
        (tmp_path / "README.md").write_text("# Test", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            readmes = find_readmes()
            assert any(r.name == "README.md" for r in readmes)

    def test_skips_gitignore_dirs(self, tmp_path):
        git_dir = tmp_path / ".git"
        git_dir.mkdir()
        (git_dir / "README.md").write_text("# git", encoding="utf-8")
        (tmp_path / "README.md").write_text("# root", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            readmes = find_readmes()
            assert not any(".git" in str(r) for r in readmes)

    def test_skips_archives(self, tmp_path):
        arch = tmp_path / "_archives"
        arch.mkdir()
        (arch / "README.md").write_text("# old", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            readmes = find_readmes()
            # _archives is in SKIP_DIRS, so its README should be excluded
            # Only the _archives/README.md should be absent — root has no README
            paths = [str(r) for r in readmes]
            assert all("_archives" not in p for p in paths), f"Found archives: {paths}"

    def test_nested_readme(self, tmp_path):
        sub = tmp_path / "subdir"
        sub.mkdir()
        (sub / "README.md").write_text("# sub", encoding="utf-8")
        (tmp_path / "README.md").write_text("# root", encoding="utf-8")
        with patch.object(_mod, "REPO_ROOT", tmp_path):
            readmes = find_readmes()
            names = [r.name for r in readmes]
            assert names.count("README.md") == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
