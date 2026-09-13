"""Tests for scripts/check_docs_links.py — link checker and orphan detector.

Validates all acceptance criteria from issue #2453:
- Detects broken links (0 false negatives)
- Detects orphan docs
- Self-checks (script does not break anything)
- Baseline write/read roundtrip
- Regression detection vs baseline
"""

import json
import subprocess
import textwrap
from pathlib import Path

import pytest

# Import from the module under test
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_docs_links
from check_docs_links import (
    BASELINE_PATH,
    LinkRef,
    ScanResult,
    check_link,
    check_regression,
    find_deck_files,
    find_orphan_docs,
    find_scan_files,
    format_report,
    load_baseline,
    preexisting_broken,
    run_scan,
    scan_content,
    scan_file,
    write_baseline,
    _is_valid_target,
    _link_exists_in_tree,
    _should_skip,
    _tree_dirs,
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


class TestShouldSkipArchiveVariants:
    """Lock the archive-skip design decision (EPIC #9535 item 10, incident #9814).

    `_archive/` (notebook archives) is DELIBERATELY NOT skipped: its READMEs
    link to active notebooks, and a broken link there is a real defect. This
    was proven when renaming a folder `_archives/` -> `_archive/` de-skipped
    it and surfaced a structurally-broken `../../` link (PR #9814). These
    tests prevent a future contributor from masking such bugs by "harmonizing"
    `_archive` into SKIP_DIRS without checking link health first.
    """

    def test_archive_readme_not_skipped(self):
        """A README inside `_archive/` is scanned (not skipped).

        These archive READMEs point to active notebooks; validating them
        catches real broken links (incident #9814)."""
        p = (REPO_ROOT / "MyIA.AI.Notebooks" / "Search" / "_archive"
             / "README.md")
        assert _should_skip(p) is False

    def test_archive_subdir_readme_not_skipped(self):
        """A README in a nested `_archive/<date>/` is also scanned."""
        p = (REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "SymbolicLearning"
             / "_archive" / "2026-07-04-Neurosymbolic-EML-precurseur-SL12"
             / "README.md")
        assert _should_skip(p) is False

    def test_docs_archive_skipped(self):
        """`docs/archive/` (historical reports) IS skipped -- out of scope."""
        p = REPO_ROOT / "docs" / "archive" / "old-report.md"
        assert _should_skip(p) is True

    def test_stale_archives_entry_removed_from_skip_dirs(self):
        """The stale `_archives` (with 's') entry is no longer in SKIP_DIRS.

        All `_archives/` folders were renamed to `_archive/` (EPIC #9535
        item 10, last one by #9814), so the entry was dead. Removing it keeps
        SKIP_DIRS honest -- nothing claims to skip a folder that no longer
        exists."""
        from check_docs_links import SKIP_DIRS
        assert "_archives" not in SKIP_DIRS
        assert "_archive" not in SKIP_DIRS  # deliberately NOT skipped
        assert "archive" in SKIP_DIRS        # docs historical archives still skipped

    def test_real_archive_readmes_are_scanned(self):
        """Integration: at least one real `_archive/` README is in the scan."""
        files = find_scan_files()
        rel = {str(f.relative_to(REPO_ROOT)).replace("\\", "/") for f in files}
        archive_readmes = [p for p in rel if "/_archive/" in p and p.endswith("README.md")]
        assert len(archive_readmes) >= 1, "Expected _archive/ READMEs to be scanned"


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

    def test_quarto_rendered_notebook_html(self, tmp_path):
        notebooks = tmp_path / "notebooks"
        notebooks.mkdir()
        (notebooks / "lesson.ipynb").write_text("{}\n")
        (tmp_path / "_quarto.yml").write_text(
            'project:\n  render:\n    - "notebooks/lesson.ipynb"\n'
        )
        source = notebooks / "README.md"

        assert check_link("lesson.html", source, root=tmp_path) is True

    def test_unlisted_notebook_html_is_broken(self, tmp_path):
        notebooks = tmp_path / "notebooks"
        notebooks.mkdir()
        (notebooks / "excluded.ipynb").write_text("{}\n")
        (tmp_path / "_quarto.yml").write_text(
            'project:\n  render:\n    - "notebooks/other.ipynb"\n'
        )
        source = notebooks / "README.md"

        assert check_link("excluded.html", source, root=tmp_path) is False


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


class TestPreexistingExcuse:
    """--check accepts links already broken at the comparison revision (#15766)."""

    def test_preexisting_link_is_not_a_regression(self):
        result = ScanResult(broken=[
            LinkRef(source="README.md", target="docs/gone.md", line=3, text="gone"),
        ])
        new_broken = check_regression(
            result, {}, preexisting={("README.md", "docs/gone.md")})
        assert new_broken == []

    def test_unrelated_preexisting_does_not_mask_a_new_link(self):
        result = ScanResult(broken=[
            LinkRef(source="README.md", target="docs/gone.md", line=3, text="gone"),
            LinkRef(source="CLAUDE.md", target="docs/fresh.md", line=9, text="fresh"),
        ])
        new_broken = check_regression(
            result, {}, preexisting={("README.md", "docs/gone.md")})
        assert [r.target for r in new_broken] == ["docs/fresh.md"]

    def test_baseline_and_preexisting_both_excuse(self):
        baseline = {"broken_links": [
            {"source": "README.md", "target": "docs/old.md", "line": 1, "text": "old"},
        ]}
        result = ScanResult(broken=[
            LinkRef(source="README.md", target="docs/old.md", line=1, text="old"),
            LinkRef(source="PARCOURS.md", target="docs/gone.md", line=2, text="gone"),
        ])
        new_broken = check_regression(
            result, baseline, preexisting={("PARCOURS.md", "docs/gone.md")})
        assert new_broken == []

    def test_no_preexisting_keeps_legacy_semantics(self):
        """Omitting the comparison revision behaves exactly as before."""
        result = ScanResult(broken=[
            LinkRef(source="README.md", target="docs/gone.md", line=3, text="gone"),
        ])
        assert len(check_regression(result, {})) == 1


class TestLinkExistsInTree:
    """The git-tree existence oracle mirrors check_link on a file listing."""

    FILES = {"docs/a.md", "docs/sub/b.md", "README.md"}

    def test_existing_file(self):
        assert _link_exists_in_tree("./a.md", "docs/a.md", self.FILES,
                                    _tree_dirs(self.FILES), None)

    def test_missing_file(self):
        assert not _link_exists_in_tree("./nope.md", "docs/a.md", self.FILES,
                                        _tree_dirs(self.FILES), None)

    def test_parent_traversal_inside_repo(self):
        assert _link_exists_in_tree("../README.md", "docs/a.md", self.FILES,
                                    _tree_dirs(self.FILES), None)

    def test_directory_target(self):
        assert _link_exists_in_tree("./sub/", "docs/a.md", self.FILES,
                                    _tree_dirs(self.FILES), None)

    def test_escaping_the_repo_is_broken(self):
        assert not _link_exists_in_tree("../../outside.md", "docs/a.md", self.FILES,
                                        _tree_dirs(self.FILES), None)

    def test_html_needs_listed_notebook(self):
        files = self.FILES | {"docs/nb.ipynb"}
        dirs = _tree_dirs(files)
        assert not _link_exists_in_tree("./nb.html", "docs/a.md", files, dirs, "")
        assert _link_exists_in_tree("./nb.html", "docs/a.md", files, dirs,
                                    '"docs/nb.ipynb"')

    def test_submodule_path_is_valid(self, monkeypatch):
        monkeypatch.setattr(check_docs_links, "SUBMODULE_PATHS", {"vendor/lib"})
        assert _link_exists_in_tree("vendor/lib/x.py", "README.md", self.FILES,
                                    _tree_dirs(self.FILES), None)


class TestPreexistingBrokenAgainstRealGit:
    """End-to-end: only links already broken at the base revision are excused."""

    @staticmethod
    def _git(root: Path, *args: str) -> None:
        subprocess.run(
            ["git", "-c", "user.email=t@example.com", "-c", "user.name=t", *args],
            cwd=root, check=True, capture_output=True,
        )

    def _fixture(self, tmp_path: Path, monkeypatch) -> Path:
        root = tmp_path / "repo"
        (root / "docs").mkdir(parents=True)
        self._git(root, "init", "-q")
        # Base revision: one link whose target is already missing, one that works.
        (root / "docs" / "present.md").write_text("# present\n", encoding="utf-8")
        (root / "docs" / "a.md").write_text(
            "[gone](./missing.md)\n[ok](./present.md)\n", encoding="utf-8")
        self._git(root, "add", "-A")
        self._git(root, "commit", "-q", "-m", "base")
        # Head revision: unchanged a.md, plus a new file carrying a new broken link.
        (root / "docs" / "b.md").write_text("[newgone](../nope.md)\n", encoding="utf-8")
        self._git(root, "add", "-A")
        self._git(root, "commit", "-q", "-m", "head")
        monkeypatch.setattr(check_docs_links, "REPO_ROOT", root)
        return root

    def test_only_already_broken_links_are_excused(self, tmp_path, monkeypatch):
        self._fixture(tmp_path, monkeypatch)
        refs = [
            LinkRef(source="docs/a.md", target="./missing.md", line=1, text="gone"),
            LinkRef(source="docs/a.md", target="./present.md", line=2, text="ok"),
            LinkRef(source="docs/b.md", target="../nope.md", line=1, text="newgone"),
        ]
        excused = preexisting_broken(refs, "HEAD~1")

        assert excused == {("docs/a.md", "./missing.md")}
        # The link whose target existed at base is a real regression now, and the
        # file added by this branch has nothing to excuse it.
        remaining = check_regression(ScanResult(broken=refs), {}, excused)
        assert sorted(r.target for r in remaining) == ["../nope.md", "./present.md"]

    def test_unreadable_revision_returns_none(self, tmp_path, monkeypatch):
        self._fixture(tmp_path, monkeypatch)
        refs = [LinkRef(source="docs/a.md", target="./missing.md", line=1, text="x")]
        assert preexisting_broken(refs, "no-such-rev-15766") is None

    def test_no_broken_refs_short_circuits(self, tmp_path, monkeypatch):
        """Nothing broken at HEAD means no revision needs to be read at all."""
        monkeypatch.setattr(check_docs_links, "REPO_ROOT", tmp_path)
        assert preexisting_broken([], "no-such-rev-15766") == set()

    def test_scan_content_matches_scan_file(self, tmp_path, monkeypatch):
        """The extracted scanner keeps the on-disk behaviour byte for byte."""
        f = tmp_path / "x.md"
        body = "# t\n\n[ok](./y.md)\n\n```\n[skip](./z.md)\n```\n"
        f.write_text(body, encoding="utf-8")
        monkeypatch.setattr(check_docs_links, "REPO_ROOT", tmp_path)
        from_file = scan_file(f)
        from_content = scan_content(body, "x.md")
        assert [(r.source, r.target, r.line) for r in from_file] == \
               [(r.source, r.target, r.line) for r in from_content]
        assert [r.target for r in from_content] == ["./y.md"]


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


# ---------------------------------------------------------------------------
# Deck scope (#15867)
# ---------------------------------------------------------------------------


class TestDeckScope:
    """`slides/<deck>/slides.md` is scanned, and an empty scope fails loudly."""

    def test_decks_are_scanned_on_the_repo(self):
        """Acceptance 1: decks are part of the scanned file set."""
        rel_paths = {
            str(f.relative_to(REPO_ROOT)).replace("\\", "/")
            for f in find_scan_files()
        }
        decks = {p for p in rel_paths if p.endswith("/slides.md")}
        assert decks, "no deck file reached the scan"
        assert all(p.startswith("slides/") for p in decks)

    def test_deck_scope_is_not_the_whole_slides_tree(self):
        """The deck scope must stay deck-only.

        Measured on origin/main 2026-09-13: `slides/**/*.md` is 119 files and
        734 broken links of 1367 (`analysis/`, `extracted/`, `*.marp.md`) --
        widening the scope there would redden every PR.

        Asserted on `find_deck_files()` itself: the pre-existing repo-wide
        README sweep legitimately brings in `slides/**/README.md`, which is not
        this scope's doing.
        """
        decks = find_deck_files()
        assert decks
        assert all(d.name == "slides.md" for d in decks)
        assert not [
            d for d in decks
            if "/analysis/" in d.as_posix()
            or "/extracted/" in d.as_posix()
            or d.name.endswith(".marp.md")
        ], f"non-deck markdown leaked into the deck scope: {decks}"

    def test_existing_but_empty_deck_scope_raises(self, tmp_path, monkeypatch):
        """Trap 1: `slides/` present yet holding no deck must not scan silently."""
        (tmp_path / "slides" / "01-vide").mkdir(parents=True)
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        with pytest.raises(check_docs_links.DeckScopeEmpty):
            find_deck_files()

    def test_absent_deck_dir_is_not_an_error(self, tmp_path, monkeypatch):
        """A tree without `slides/` (as in most fixtures) simply has no deck."""
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        assert find_deck_files() == []

    def test_deck_linked_outside_slides_resolves(self, tmp_path, monkeypatch):
        """Trap 2: a deck link may leave `slides/` and target a notebook.

        `..` must be normalised before testing existence, or every deck link
        reads as broken (or as valid).
        """
        repo = tmp_path
        nb = repo / "MyIA.AI.Notebooks" / "GameTheory"
        nb.mkdir(parents=True)
        (nb / "GameTheory-02-NormalForm.ipynb").write_text("{}", encoding="utf-8")
        deck_dir = repo / "slides" / "05-theorie-des-jeux"
        deck_dir.mkdir(parents=True)
        deck = deck_dir / "slides.md"
        deck.write_text(
            "*Notebooks : [GameTheory-02-NormalForm]"
            "(../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm.ipynb).*\n"
            "[mort](../../MyIA.AI.Notebooks/GameTheory/GameTheory-99-Absent.ipynb)\n",
            encoding="utf-8",
        )
        refs = scan_file(deck)
        assert [r.target for r in refs] == [
            "../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm.ipynb",
            "../../MyIA.AI.Notebooks/GameTheory/GameTheory-99-Absent.ipynb",
        ]
        assert check_link(refs[0].target, deck, root=repo) is True
        assert check_link(refs[1].target, deck, root=repo) is False

    def test_real_deck_links_are_all_valid(self):
        """Acceptance 3: the 108 deck links on main stay all valid.

        No false positive is introduced on the existing corpus; this is the
        count the issue measured (#15867).
        """
        deck_broken = [
            ref for ref in run_scan().broken
            if ref.source.startswith("slides/")
        ]
        assert deck_broken == [], (
            "the deck scope introduced false positives on the existing corpus: "
            f"{[(r.source, r.line, r.target) for r in deck_broken]}"
        )


class TestPositiveControl:
    """`--expect-broken N` -- the control that tells "clean" from "blind"."""

    def _broken_tree(self, tmp_path, monkeypatch):
        (tmp_path / "slides" / "03-logique").mkdir(parents=True)
        (tmp_path / "slides" / "03-logique" / "slides.md").write_text(
            "[cassee](../../MyIA.AI.Notebooks/absent.ipynb)\n", encoding="utf-8"
        )
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        monkeypatch.setattr("check_docs_links.BASELINE_PATH",
                            tmp_path / "baseline.json")

    def test_control_is_met_on_a_deliberately_broken_tree(self, tmp_path, monkeypatch):
        """Acceptance 2: a dead link written on a deck is detected."""
        self._broken_tree(tmp_path, monkeypatch)
        result = run_scan()
        assert [r.target for r in result.broken] == [
            "../../MyIA.AI.Notebooks/absent.ipynb"
        ]

    def test_met_control_does_not_exit_2(self, tmp_path, monkeypatch):
        """Armed + broken == a genuine finding (rc=1), not a control failure."""
        self._broken_tree(tmp_path, monkeypatch)
        monkeypatch.setattr("sys.argv", ["check_docs_links.py", "--expect-broken", "1"])
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 1

    def test_same_tree_fails_the_control_under_a_higher_threshold(
        self, tmp_path, monkeypatch, capsys
    ):
        """Discrimination, on ONE tree: the threshold, not the tree, decides.

        Raising the expectation above what the organ can see must flip rc=1
        (finding) into rc=2 (control unmet) -- which is what makes a dead
        detection path detectable instead of green.
        """
        self._broken_tree(tmp_path, monkeypatch)
        monkeypatch.setattr("sys.argv", ["check_docs_links.py", "--expect-broken", "2"])
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 2
        assert "POSITIVE CONTROL FAILED" in capsys.readouterr().err

    def test_clean_scan_under_an_armed_control_exits_2(self, monkeypatch, capsys):
        """A genuinely clean tree under an armed control is a FAILURE, not a pass.

        `run_scan` is stubbed: the claim under test is the control's verdict on
        a zero-broken result, not path resolution.
        """
        monkeypatch.setattr("check_docs_links.run_scan", lambda report_orphans=False: ScanResult())
        monkeypatch.setattr("sys.argv", ["check_docs_links.py", "--expect-broken", "1"])
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 2
        assert "POSITIVE CONTROL FAILED" in capsys.readouterr().err

    def test_gate_mode_does_not_print_the_advisory(self, monkeypatch, capsys):
        """`--check` success stays a single summary line: no advisory noise.

        The gate runs on every PR; an advisory printed on every green run is
        trained away within a week, so it is confined to the bare scan.
        """
        monkeypatch.setattr("check_docs_links.run_scan",
                            lambda report_orphans=False: ScanResult())
        monkeypatch.setattr("check_docs_links.load_baseline",
                            lambda *a, **k: {"broken_links": []})
        monkeypatch.setattr("sys.argv", ["check_docs_links.py", "--check"])
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 0
        assert "WARNING" not in capsys.readouterr().err


class TestDeckScopeWiring:
    """Adding the scope to the organ is worthless if the gate never runs it."""

    def test_deck_scope_is_wired_into_the_fast_lane(self):
        """The `check-links` gate must fire when a deck changes.

        `docs-link-check.yml` is `workflow_dispatch`-only since #12567: for PRs
        the organ is rendered by the fast lane, which decides from `paths`. A
        scope added to the organ alone leaves deck-only PRs unchecked -- the
        #15865 case.
        """
        sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
        try:
            import fast_lane_registry
        finally:
            sys.path.pop(0)
        guard = next(
            g for g in fast_lane_registry.TRANCHE1 if g.name == "check-links"
        )
        assert "slides/**" in guard.paths, (
            "the check-links gate does not watch slides/ -- a deck-only PR "
            "would never run the organ (#15867)"
        )

    def test_every_declared_scope_is_reachable_from_the_gate(self):
        """Parity: each scanned scope must have a matching gate trigger."""
        sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
        try:
            import fast_lane_registry
        finally:
            sys.path.pop(0)
        guard = next(
            g for g in fast_lane_registry.TRANCHE1 if g.name == "check-links"
        )
        for scope in check_docs_links.SCAN_SCOPES:
            if scope.endswith("/"):
                assert any(p.startswith(scope) for p in guard.paths), (
                    f"scope {scope!r} is scanned but no gate path covers it"
                )
            else:
                assert scope in guard.paths, (
                    f"scope {scope!r} is scanned but the gate never watches it"
                )
        assert any(
            p.startswith(f"{check_docs_links.DECK_DIR}/") for p in guard.paths
        ), "the deck scope is scanned but the gate never watches it"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
