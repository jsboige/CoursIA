"""Tests for the shared notebook walker (#8650).

Covers: canonical SKIP_DIRS content, SKIP_DIRS / _output filtering, and the
``tracked_only`` git filter (the deterministic exclusion of gitignored trees
that the eleven scanners previously relied on SKIP_DIRS only matching by
accident). The git filter is exercised with a real throwaway ``git init`` so
the regression is caught if the mechanism ever breaks.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import notebook_walk as nw  # noqa: E402


def _nb(name="nb.ipynb"):
    return {"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _write(tree_root: Path, rel: str):
    p = tree_root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(_nb()), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# 1. SKIP_DIRS canonical content
# ---------------------------------------------------------------------------
class TestSkipDirs:
    def test_is_a_set(self):
        assert isinstance(nw.SKIP_DIRS, set)

    def test_contains_canonical_entries(self):
        for key in (
            ".lake", ".git", "__pycache__", "_archives", "archive", "_archive",
            ".ipynb_checkpoints", "_output", ".pytest_cache", "worktrees",
            "foundry-lib", ".claude", "node_modules",
        ):
            assert key in nw.SKIP_DIRS, key

    def test_output_kept_as_dir_entry(self):
        # `_output` is primarily a Papermill *file suffix* (skip_papermill_output),
        # but it is also kept as a directory name -- harmless (no tracked `_output/`
        # dir exists) and preserves the scanners whose tests assert a `_output/`
        # directory is out-of-scope (#8650 discussion).
        assert "_output" in nw.SKIP_DIRS


# ---------------------------------------------------------------------------
# 2. iter_notebooks -- SKIP_DIRS + papermill suffix filtering (no git)
# ---------------------------------------------------------------------------
class TestIterNotebooksFiltering:
    def test_yields_plain_notebook(self, tmp_path):
        _write(tmp_path, "family/nb.ipynb")
        paths = list(nw.iter_notebooks(tmp_path, tracked_only=False))
        assert [p.name for p in paths] == ["nb.ipynb"]

    def test_skips_vendored_dirs(self, tmp_path):
        _write(tmp_path, ".lake/packages/x.ipynb")
        _write(tmp_path, "foundry-lib/lib/y.ipynb")
        _write(tmp_path, "nb.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path, tracked_only=False)}
        assert names == {"nb.ipynb"}

    def test_skips_archive_dirs(self, tmp_path):
        # `archive` (singular) is the entry plotly historically lacked (#8650).
        _write(tmp_path, "Search/archive/old.ipynb")
        _write(tmp_path, "_archives/older.ipynb")
        _write(tmp_path, "nb.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path, tracked_only=False)}
        assert names == {"nb.ipynb"}

    def test_skips_papermill_output_artifact(self, tmp_path):
        _write(tmp_path, "primary.ipynb")
        _write(tmp_path, "primary_output.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path, tracked_only=False)}
        assert names == {"primary.ipynb"}

    def test_skip_papermill_output_false_keeps_artifact(self, tmp_path):
        _write(tmp_path, "primary.ipynb")
        _write(tmp_path, "primary_output.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path, tracked_only=False, skip_papermill_output=False)}
        assert names == {"primary.ipynb", "primary_output.ipynb"}

    def test_family_subset(self, tmp_path):
        _write(tmp_path, "Search/a.ipynb")
        _write(tmp_path, "ML/b.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path, family="Search", tracked_only=False)}
        assert names == {"a.ipynb"}


# ---------------------------------------------------------------------------
# 3. tracked_only -- the git filter (deterministic exclusion of gitignored)
# ---------------------------------------------------------------------------
def _git(path: Path, *args):
    return subprocess.run(["git", *args], cwd=str(path), capture_output=True, text=True)


@pytest.fixture
def git_repo(tmp_path):
    """A throwaway git repo with one tracked + one gitignored notebook."""
    root = tmp_path / "repo"
    (root / "MyIA.AI.Notebooks").mkdir(parents=True)
    _git(root, "init", "-q")
    _git(root, "config", "user.email", "t@t")
    _git(root, "config", "user.name", "t")
    root.joinpath(".gitignore").write_text("ignored.ipynb\n", encoding="utf-8")
    nb_root = root / "MyIA.AI.Notebooks"
    _write(nb_root, "tracked.ipynb")
    _write(nb_root, "ignored.ipynb")  # gitignored -> never added
    _git(root, "add", ".")
    _git(root, "commit", "-q", "-m", "init")
    return nb_root


class TestTrackedOnly:
    def test_default_excludes_gitignored(self, git_repo):
        names = {p.name for p in nw.iter_notebooks(git_repo)}
        assert names == {"tracked.ipynb"}

    def test_tracked_only_false_includes_gitignored(self, git_repo):
        names = {p.name for p in nw.iter_notebooks(git_repo, tracked_only=False)}
        assert names == {"tracked.ipynb", "ignored.ipynb"}

    def test_relative_root_with_git(self, git_repo, monkeypatch):
        # Regression: a caller passing a RELATIVE --root (e.g. plotly's default
        # "MyIA.AI.Notebooks") must still resolve against the absolute repo root
        # returned by `git rev-parse` -- otherwise nb.relative_to(repo_root)
        # raises ValueError and EVERY notebook is silently skipped (#8650).
        # git_repo is <repo>/MyIA.AI.Notebooks, so the repo root is its parent.
        monkeypatch.chdir(git_repo.parent)
        names = {p.name for p in nw.iter_notebooks(Path("MyIA.AI.Notebooks"))}
        assert names == {"tracked.ipynb"}

    def test_fallback_when_not_a_repo(self, tmp_path, capsys, monkeypatch):
        # Outside any git repo: degrade to on-disk scan + warn (no false "0").
        monkeypatch.setattr(nw, "_git_repo_root", lambda _p: None)
        _write(tmp_path, "a.ipynb")
        _write(tmp_path, "b.ipynb")
        names = {p.name for p in nw.iter_notebooks(tmp_path)}
        assert names == {"a.ipynb", "b.ipynb"}
        assert "git is unavailable" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# 4. missing base -- graceful no-op
# ---------------------------------------------------------------------------
def test_missing_base_yields_nothing(tmp_path):
    assert list(nw.iter_notebooks(tmp_path / "does_not_exist")) == []
