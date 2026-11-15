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
    CODE_BASELINE_PATH,
    DOC_CITATION_PATTERN,
    LinkRef,
    ScanResult,
    check_link,
    check_regression,
    find_code_files,
    find_deck_files,
    find_orphan_docs,
    find_scan_files,
    format_report,
    load_baseline,
    preexisting_broken,
    run_scan,
    scan_code_content,
    scan_code_file,
    scan_content,
    scan_file,
    write_baseline,
    _citation_exists,
    _citation_exists_in_tree,
    _comment_spans,
    _is_output_position,
    _is_scoped_doc_citation,
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


class TestSiteArtifactSkip:
    """`_site/` (Quarto build artifact) is not repository source.

    `_site/` is gitignored and GENERATED from our own docs. A broken link
    inside it is a re-render of a link the source already declares, so the
    organ must not report it as a repository defect.

    Before this entry, the organ's verdict depended on the machine: on a
    workstation that had run a Quarto build it reported dead links for pages
    that are not in the repository at all, while CI -- where the artifact is
    gitignored and therefore never checked out -- stayed green. A verdict
    that depends on the machine is not a verdict.
    """

    def test_site_root_skipped(self):
        p = REPO_ROOT / "_site" / "index.html"
        assert _should_skip(p) is True

    def test_site_nested_skipped(self):
        """A nested `_site/` is skipped too -- the skip is by directory NAME."""
        p = REPO_ROOT / "docs" / "_site" / "reference" / "index.html"
        assert _should_skip(p) is True

    def test_site_is_gitignored(self):
        """The skip list and `.gitignore` must agree on `_site/`.

        Tying them by test rather than by comment: if `_site/` were ever
        un-ignored, the skip would start masking real content, and this test
        is what would notice.
        """
        gitignore = (REPO_ROOT / ".gitignore").read_text(encoding="utf-8")
        assert "_site/" in gitignore


class TestScratchSkip:
    """`.tmp/` (agent scratch) is not repository source either (#24410).

    Same defect class as `_site/`: gitignored, never checked out in CI, and
    repo-wide README sweep makes it reachable on any machine that has run a
    scratch worktree. Measured 2026-11-03: 29 of the 31 "broken links" the
    organ reported locally came from three `.tmp/` worktrees, against 2 real
    defects -- the real ones drowned in scratch noise.
    """

    def test_tmp_root_skipped(self):
        p = REPO_ROOT / ".tmp" / "sf-labeler" / "README.md"
        assert _should_skip(p) is True

    def test_tmp_nested_skip_is_by_directory_name(self):
        """Skip matches the directory NAME anywhere in the path, like `_site/`."""
        p = REPO_ROOT / "docs" / ".tmp" / "analysis" / "note.md"
        assert _should_skip(p) is True

    def test_tmp_is_gitignored(self):
        """The skip list and `.gitignore` must agree on `.tmp/`.

        `.tmp/` is ignored by the `*.tmp` glob (see `.gitignore`), not by a
        literal `.tmp/` line: a DIRECTORY named `.tmp` ends in `.tmp` and
        matches. Asserting git's own verdict rather than a spelling keeps the
        test honest if the pattern is ever rewritten.
        """
        res = subprocess.run(
            ["git", "check-ignore", "-q", ".tmp/scratch/README.md"],
            cwd=REPO_ROOT, capture_output=True,
        )
        assert res.returncode == 0, (
            ".tmp/ is no longer gitignored -- the skip would mask real content"
        )

    def test_dot_tmp_named_file_still_scanned(self):
        """Only the `.tmp` DIRECTORY is skipped -- not names merely containing it."""
        p = REPO_ROOT / "docs" / "notes.tmp.md"
        assert _should_skip(p) is False


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


class TestGeneratedSourceExcuse:
    """#22651: a generated page cannot be repaired on a content branch."""

    @staticmethod
    def _result(source: str) -> ScanResult:
        return ScanResult(broken=[LinkRef(
            source=source,
            target="../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/"
                   "04-17-Basic-Pitch-Transcription.ipynb",
            line=78, text="Transcription Note a Note : basic-pitch",
        )])

    def test_real_generated_curriculum_link_is_excused(self):
        """Positive control: the #22556 rename on the real generated page."""
        source = "docs/curriculum/genai.md"
        assert check_docs_links._is_generated_source(REPO_ROOT / source)
        assert check_regression(self._result(source), {}) == []
        report = check_docs_links.format_generated_excuses(
            self._result(source).broken)
        assert "Excused: 1 generated source" in report
        assert "04-17-Basic-Pitch-Transcription.ipynb" in report

    def test_same_broken_link_in_manual_page_remains_regression(self, tmp_path, monkeypatch):
        """Negative control: no header, no exemption."""
        source = "docs/curriculum/manual.md"
        page = tmp_path / source
        page.parent.mkdir(parents=True)
        page.write_text("# Parcours rédigé à la main\n", encoding="utf-8")
        monkeypatch.setattr(check_docs_links, "REPO_ROOT", tmp_path)
        assert check_docs_links._is_generated_source(page) is False
        assert len(check_regression(self._result(source), {})) == 1


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
        (nb / "GameTheory-02-NormalForm-Python.ipynb").write_text("{}", encoding="utf-8")
        deck_dir = repo / "slides" / "05-theorie-des-jeux"
        deck_dir.mkdir(parents=True)
        deck = deck_dir / "slides.md"
        deck.write_text(
            "*Notebooks : [GameTheory-02-NormalForm-Python]"
            "(../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Python.ipynb).*\n"
            "[mort](../../MyIA.AI.Notebooks/GameTheory/GameTheory-99-Absent.ipynb)\n",
            encoding="utf-8",
        )
        refs = scan_file(deck)
        assert [r.target for r in refs] == [
            "../../MyIA.AI.Notebooks/GameTheory/GameTheory-02-NormalForm-Python.ipynb",
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
        monkeypatch.setattr(
            "check_docs_links.run_scan",
            lambda report_orphans=False, code=False: ScanResult())
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
                            lambda report_orphans=False, code=False: ScanResult())
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


class TestQuartoSourceScan:
    """#26457: the site is built from ``.qmd``, which the scan must open.

    Before the fix ``find_scan_files()`` globbed ``*.md`` only, so a ``.qmd``
    was never opened and a broken link inside it read as a clean scan (#26281
    moved parcours.qmd and left 19 dead links the organ reported as 0). Two
    guarantees: ``.qmd`` reach the scan, and a broken ``.qmd`` link is a real
    finding (rc=1), so "the .qmd are clean" is no longer indistinguishable from
    "the .qmd are still not scanned".
    """

    def test_qmd_files_are_in_the_scan(self, tmp_path, monkeypatch):
        """Guarantee 1: a .qmd under a scanned scope is enumerated."""
        (tmp_path / "docs").mkdir()
        (tmp_path / "docs" / "parcours.qmd").write_text(
            "# Parcours\n", encoding="utf-8")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        rel = {f.relative_to(tmp_path).as_posix() for f in find_scan_files()}
        assert "docs/parcours.qmd" in rel

    def test_qmd_broken_link_is_detected(self, tmp_path, monkeypatch):
        """Guarantee 2: a dead link written in a .qmd is found."""
        (tmp_path / "docs").mkdir()
        (tmp_path / "docs" / "index.qmd").write_text(
            "[mort](../absent.md)\n", encoding="utf-8")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        result = run_scan()
        assert [r.target for r in result.broken] == ["../absent.md"]

    def test_qmd_broken_link_arms_the_positive_control(
        self, tmp_path, monkeypatch
    ):
        """The .qmd finding is rc=1 (a real finding), not rc=2 (blind)."""
        (tmp_path / "docs").mkdir()
        (tmp_path / "docs" / "index.qmd").write_text(
            "[mort](../absent.md)\n", encoding="utf-8")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        monkeypatch.setattr("check_docs_links.BASELINE_PATH",
                            tmp_path / "baseline.json")
        monkeypatch.setattr("sys.argv",
                            ["check_docs_links.py", "--expect-broken", "1"])
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 1


# ---------------------------------------------------------------------------
# Code-comment citation pass (#24410)
# ---------------------------------------------------------------------------

class TestDocCitationPattern:
    """The shape filter: what counts as a doc path inside a comment."""

    def test_plain_repo_path(self):
        m = DOC_CITATION_PATTERN.search("see docs/reference/x.md for the reason")
        assert m is not None and m.group(1) == "docs/reference/x.md"

    def test_dotted_top_level_dir(self):
        m = DOC_CITATION_PATTERN.search("per .claude/rules/git-workflow.md")
        assert m is not None and m.group(1) == ".claude/rules/git-workflow.md"

    def test_parent_relative_path(self):
        m = DOC_CITATION_PATTERN.search("cf. ../docs/reference/x.md")
        assert m is not None and m.group(1) == "../docs/reference/x.md"

    def test_equivalence_shape_is_not_matched(self):
        """`docs/...md` is how PROSE names the pattern, not a cited page.

        This is the shape the organ's own docstring uses to describe itself; if
        it matched, the instrument would report itself as broken forever.
        """
        assert DOC_CITATION_PATTERN.search("every `docs/...md`-shaped string") is None

    def test_bare_filename_is_not_matched(self):
        """A bare `README.md` names no resolvable file -- which directory?"""
        assert DOC_CITATION_PATTERN.search("see README.md for setup") is None

    def test_mdx_is_not_md(self):
        assert DOC_CITATION_PATTERN.search("see docs/page.mdx") is None


class TestCommentSpansPython:
    """Python comments and docstrings, told apart from string literals."""

    def test_hash_comment(self):
        spans = _comment_spans(".py", "x = 1  # see docs/a.md\n")
        assert ("docs/a.md" in spans[0][1]) and spans[0][0] == 1

    def test_hash_inside_string_is_not_a_comment(self):
        spans = _comment_spans(".py", 'URL = "http://x/#frag"  # real\n')
        assert len(spans) == 1
        assert "real" in spans[0][1]

    def test_docstring_is_scanned(self):
        src = 'def f():\n    """Cite docs/a.md here."""\n    return 1\n'
        text = " ".join(t for _, t in _comment_spans(".py", src))
        assert "docs/a.md" in text

    def test_module_docstring_is_scanned(self):
        src = '"""Module citing docs/b.md."""\n'
        text = " ".join(t for _, t in _comment_spans(".py", src))
        assert "docs/b.md" in text

    def test_unparsable_source_does_not_raise(self):
        """A file the interpreter rejects is still a file to scan."""
        assert isinstance(_comment_spans(".py", "def f(:\n  # docs/a.md\n"), list)


class TestCommentSpansGeneric:
    """Lean and C# comment syntax, including Lean's nesting."""

    def test_lean_line_comment(self):
        spans = _comment_spans(".lean", "-- cites docs/a.md\n¬p\n")
        assert len(spans) == 1 and "docs/a.md" in spans[0][1]

    def test_lean_nested_block_comment(self):
        """Lean nests `/- -/`: stopping at the first `-/` would scan code."""
        spans = _comment_spans(".lean", "/- outer /- inner -/ tail -/\n")
        text = " ".join(t for _, t in spans)
        assert "outer" in text and "inner" in text and "tail" in text

    def test_lean_marker_inside_string_is_not_a_comment(self):
        spans = _comment_spans(".lean", 'def s := "-- not a comment"\n')
        assert spans == []

    def test_csharp_line_comment(self):
        spans = _comment_spans(".cs", "// cites docs/a.md\nvar x = 1;\n")
        assert len(spans) == 1 and "docs/a.md" in spans[0][1]

    def test_csharp_block_comment(self):
        spans = _comment_spans(".cs", "/* cite docs/a.md */\n")
        assert "docs/a.md" in spans[0][1]

    def test_csharp_marker_inside_string_is_not_a_comment(self):
        spans = _comment_spans(".cs", 'var u = "http://x";\n')
        assert spans == []

    def test_unknown_suffix_yields_nothing(self):
        assert _comment_spans(".txt", "# docs/a.md") == []


class TestCitationScope:
    """The three noise families, excluded structurally rather than by list."""

    def test_third_party_repo_path_is_out_of_scope(self):
        """`lean/docs/132.md` belongs to the upstream project, not to us."""
        assert _is_scoped_doc_citation("lean/docs/132.md", {"docs", "scripts"}) is False

    def test_path_anchored_at_our_top_level_is_in_scope(self):
        assert _is_scoped_doc_citation("docs/a.md", {"docs"}) is True

    def test_relative_path_is_in_scope(self):
        assert _is_scoped_doc_citation("../docs/a.md", set()) is True

    def test_command_output_position_is_excluded(self):
        assert _is_output_position("--out ") is True

    def test_write_call_position_is_excluded(self):
        assert _is_output_position('target.write_text("') is True
        assert _is_output_position('open("') is True

    def test_arrow_is_not_an_output_redirect(self):
        """`-> Path` in a signature must not read as a shell redirect."""
        assert _is_output_position("parse(x) -> Path(") is False

    def test_plain_prose_is_a_citation_position(self):
        assert _is_output_position("# see ") is False


class TestCitationAnchoring:
    """A citation is dead only when NEITHER anchor finds it."""

    def _tree(self, tmp_path, monkeypatch):
        (tmp_path / "docs").mkdir()
        (tmp_path / "docs" / "root-page.md").write_text("# root\n")
        nested = tmp_path / "a" / "b"
        nested.mkdir(parents=True)
        (tmp_path / "a" / "docs").mkdir()
        (tmp_path / "a" / "docs" / "sibling-page.md").write_text("# sibling\n")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        return "a/b/f.py"

    def test_root_anchor_resolves_a_nested_citation(self, tmp_path, monkeypatch):
        """The issue's convention: a deep file writes `docs/x.md` meaning root."""
        source = self._tree(tmp_path, monkeypatch)
        assert _citation_exists("docs/root-page.md", source) is True

    def test_source_dir_anchor_still_works(self, tmp_path, monkeypatch):
        """A file at `a/f.py` citing `docs/...` resolves to `a/docs/...`."""
        self._tree(tmp_path, monkeypatch)
        assert _citation_exists("docs/sibling-page.md", "a/f.py") is True

    def test_neither_anchor_resolves_is_dead(self, tmp_path, monkeypatch):
        source = self._tree(tmp_path, monkeypatch)
        assert _citation_exists("docs/nowhere.md", source) is False

    def test_explicit_relative_path_is_not_re_anchored(self, tmp_path, monkeypatch):
        """`../docs/...` names one anchor; the root must not rescue it."""
        source = self._tree(tmp_path, monkeypatch)
        assert _citation_exists("../docs/root-page.md", source) is False

    def test_tree_oracle_mirrors_both_anchors(self):
        files = {"docs/root-page.md", "a/docs/sibling-page.md"}
        dirs = _tree_dirs(files)
        assert _citation_exists_in_tree("docs/root-page.md", "a/b/f.py", files, dirs, None)
        assert _citation_exists_in_tree("../docs/sibling-page.md", "a/b/f.py", files, dirs, None)
        assert not _citation_exists_in_tree("docs/nowhere.md", "a/b/f.py", files, dirs, None)


class TestCodeScan:
    """End-to-end behaviour of the code-comment pass."""

    def test_scan_code_content_reports_dead_and_alive(self, tmp_path, monkeypatch):
        (tmp_path / "docs").mkdir()
        (tmp_path / "docs" / "alive.md").write_text("# alive\n")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        content = "# see docs/alive.md\n# see docs/dead.md\n"
        refs = scan_code_content(content, "pkg/mod.py")
        assert {r.target for r in refs} == {"docs/alive.md", "docs/dead.md"}

    def test_output_position_is_not_reported(self, tmp_path, monkeypatch):
        (tmp_path / "docs").mkdir()
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        refs = scan_code_content("# --out docs/generated.md\n", "pkg/gen.py")
        assert refs == []

    def test_same_path_twice_on_a_line_is_one_citation(self, tmp_path, monkeypatch):
        (tmp_path / "docs").mkdir()
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        refs = scan_code_content("# docs/a.md and docs/a.md again\n", "pkg/m.py")
        assert len(refs) == 1

    def test_file_without_md_is_not_lexed(self, tmp_path, monkeypatch):
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        assert scan_code_content("x = 1\n", "pkg/m.py") == []

    def test_test_trees_are_not_scanned(self, tmp_path, monkeypatch):
        """Family 1: a path in a test tree is a fixture value, not a claim."""
        (tmp_path / "scripts" / "tests").mkdir(parents=True)
        (tmp_path / "scripts" / "tests" / "test_x.py").write_text(
            "# docs/fixture.md\n")
        (tmp_path / "scripts" / "src").mkdir()
        (tmp_path / "scripts" / "src" / "mod.py").write_text("# docs/a.md\n")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        rel = {
            (tmp_path / p).relative_to(tmp_path).as_posix()
            for p in ("scripts/tests/test_x.py", "scripts/src/mod.py")
        }
        found = {
            f.relative_to(tmp_path).as_posix()
            for f in find_code_files()
            if f.relative_to(tmp_path).as_posix() in rel
        }
        assert found == {"scripts/src/mod.py"}

    def test_run_scan_code_mode_fills_broken(self, tmp_path, monkeypatch):
        (tmp_path / "docs").mkdir()
        (tmp_path / "pkg").mkdir()
        (tmp_path / "pkg" / "m.py").write_text("# cites docs/gone.md\n")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        result = run_scan(code=True)
        assert [r.target for r in result.broken] == ["docs/gone.md"]
        assert result.scanned_files == 1

    def test_run_scan_markdown_mode_ignores_code(self, tmp_path, monkeypatch):
        """The two passes stay separate: markdown mode never opens a .py."""
        (tmp_path / "docs").mkdir()
        (tmp_path / "pkg").mkdir()
        (tmp_path / "pkg" / "m.py").write_text("# cites docs/gone.md\n")
        monkeypatch.setattr("check_docs_links.REPO_ROOT", tmp_path)
        assert run_scan().broken == []


class TestIssueReproducibleCases:
    """The four citations that founded #24410, measured on the real tree.

    Each names a path that no longer exists at the cited location because the
    target moved. Before the fix the organ could not see any of them: they live
    in `.py` files, which the markdown scan never opens.
    """

    CASES = [
        ("MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/m13_ms_har.py",
         "docs/M13_MS_HAR.md"),
        ("MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/hmm_regime_vol.py",
         "docs/M5_HMM_REGIME.md"),
        ("MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/_archive/"
         "s2_gsp_cross_asset_vol.py", "docs/RECAP_KEEPERS_V2.md"),
        ("MyIA.AI.Notebooks/GenAI/shared/helpers/comfyui_client.py",
         "docs/suivis/genai-image/phase-29-corrections-qwen/"
         "SYNTHESE-COMPLETE-PHASE-29.md"),
    ]

    @pytest.mark.parametrize("source,target", CASES)
    def test_case_is_detected_and_dead(self, source, target):
        path = REPO_ROOT / source
        if not path.is_file():
            pytest.skip(f"{source} no longer exists on this tree")
        refs = scan_code_file(path)
        assert target in {r.target for r in refs}, (
            f"{source} cites {target} but the organ does not see it")
        assert _citation_exists(target, source) is False, (
            f"{target} was expected to be dead at this location")

    def test_positive_control_arms_the_code_pass(self, monkeypatch, capsys):
        """Requirement 3: `--expect-broken` is wired to the NEW detection path.

        main() is invoked with the code pass selected and a scan that reports
        nothing: an unmet control must exit 2, which is what distinguishes "0
        dead citations" from "the code pass never ran". The pass is stubbed so
        the test measures the CONTROL BRANCH, not a 70 s full scan; that the
        real pass finds real citations is what the case tests above prove.
        """
        import check_docs_links

        monkeypatch.setattr(sys, "argv", [
            "check_docs_links.py", "--code", "--quiet", "--expect-broken", "1",
        ])
        monkeypatch.setattr(
            check_docs_links, "run_scan",
            lambda **kw: ScanResult(scanned_files=1, total_links=1),
        )
        with pytest.raises(SystemExit) as exc:
            check_docs_links.main()
        assert exc.value.code == 2
        assert "POSITIVE CONTROL FAILED" in capsys.readouterr().err

    def test_preexisting_accepts_the_code_scanner(self):
        """--check --base --code routes through the code pass, not markdown.

        A fake scanner reports the citation at the base revision and a fake
        oracle reports it dead there: the pair must then be excused. The kwargs
        are the only seam; if they disappear, code mode silently compares
        against the MARKDOWN scan and every dead citation reddens again.
        """
        ref = LinkRef(source="README.md", target="docs/x.md", line=1, text="t")
        seen = {}

        def fake_scanner(content, rel_source):
            seen["scanned"] = rel_source
            return [LinkRef(source=rel_source, target="docs/x.md", line=9, text="t")]

        def fake_oracle(target, source, files, dirs, quarto):
            seen["oracle"] = True
            return False

        out = preexisting_broken([ref], "HEAD",
                                 scanner=fake_scanner, exists_in_tree=fake_oracle)
        assert out == {("README.md", "docs/x.md")}
        assert seen == {"scanned": "README.md", "oracle": True}


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
