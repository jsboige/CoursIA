"""Tests for check_exec_ratchet.py — ratchet gate (#11112 tier 2).

Pins the ratchet contract on a real miniature git history: a notebook whose
sequence was CLEAN at base must stay CLEAN at head; a base-dirty notebook is
never required to improve; added notebooks are reported, not failed. No
network, no kernel.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_exec_ratchet as ratchet


def make_nb(exec_counts):
    cells = [{"cell_type": "code", "execution_count": ec,
              "source": f"print({i})", "outputs": [], "metadata": {}}
             for i, ec in enumerate(exec_counts)]
    return {"cells": cells, "metadata": {}, "nbformat": 4,
            "nbformat_minor": 5}


def write_nb(repo, rel, nb):
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")


def git_ok(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, encoding="utf-8")


@pytest.fixture
def repo(tmp_path):
    """Mini repo with one base commit; returns (repo, base_sha)."""
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True,
                  capture_output=True)
    git_ok(tmp_path, "config", "user.email", "t@t")
    git_ok(tmp_path, "config", "user.name", "t")
    return tmp_path


def commit(repo, msg):
    git_ok(repo, "add", "-A")
    git_ok(repo, "commit", "-m", msg)
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                          check=True, capture_output=True,
                          encoding="utf-8").stdout.strip()


class TestRatchetVerdicts:
    def test_clean_soled_is_regression(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, 2]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs == [{"notebook": "a.ipynb", "base": "CLEAN",
                         "head": "DUPLICATE", "regression": True}]

    def test_dirty_staying_dirty_passes(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 2]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 1, 3]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs[0]["regression"] is False

    def test_dirty_to_clean_improvement_passes(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 2]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs[0] == {"notebook": "a.ipynb", "base": "DUPLICATE",
                           "head": "CLEAN", "regression": False}

    def test_clean_to_partial_is_regression(self, repo):
        # cells left never-executed soil a clean sequence too
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, None]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs[0]["regression"] is True
        assert recs[0]["head"] == "PARTIAL"

    def test_partial_to_dirty_not_regression(self, repo):
        # base not clean: no ratchet (H.3 owns never-executed evidence)
        write_nb(repo, "a.ipynb", make_nb([1, None, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, 2]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs[0]["regression"] is False

    def test_added_notebook_reported_not_failed(self, repo):
        write_nb(repo, "keep.ipynb", make_nb([1, 2]))
        base = commit(repo, "base")
        write_nb(repo, "new.ipynb", make_nb([5, 5]))
        commit(repo, "head")
        recs = ratchet.ratchet(base, cwd=repo)
        assert recs[0]["notebook"] == "new.ipynb"
        assert recs[0]["base"] == "ABSENT"
        assert recs[0]["regression"] is False

    def test_untouched_notebook_not_listed(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2]))
        (repo / "b.md").write_text("x", encoding="utf-8")
        base = commit(repo, "base")
        (repo / "b.md").write_text("y", encoding="utf-8")
        commit(repo, "head")
        assert ratchet.ratchet(base, cwd=repo) == []

    def test_deleted_notebook_not_listed(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2]))
        write_nb(repo, "b.ipynb", make_nb([1, 2]))
        base = commit(repo, "base")
        (repo / "a.ipynb").unlink()
        commit(repo, "head")
        assert ratchet.ratchet(base, cwd=repo) == []


class TestExclusions:
    def test_archive_output_research_checkpoints_excluded(self, monkeypatch):
        lines = "a.ipynb\npkg/archive/o.ipynb\npkg/_output/o.ipynb\n" \
                "pkg/research/o.ipynb\npkg/nb/.ipynb_checkpoints/o.ipynb\n"
        monkeypatch.setattr(ratchet, "git", lambda *a, **kw: lines)
        assert ratchet.changed_notebooks("origin/main") == ["a.ipynb"]


class TestCli:
    def run_cli(self, repo, *args):
        return subprocess.run(
            [sys.executable, str(Path(__file__).resolve().parent.parent
                                 / "check_exec_ratchet.py"), *args],
            cwd=repo, capture_output=True, encoding="utf-8")

    def test_exit_1_on_regression(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([2, 2, 3]))
        commit(repo, "head")
        out = self.run_cli(repo, base)
        assert out.returncode == 1
        assert "REGRESSION" in out.stdout
        assert "::error file=a.ipynb" in out.stderr

    def test_exit_0_when_clean_kept(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3, 4]))
        commit(repo, "head")
        out = self.run_cli(repo, base)
        assert out.returncode == 0
        assert "regressions       : 0" in out.stdout

    def test_json_output(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([1, 2, 2]))
        commit(repo, "head")
        out = self.run_cli(repo, base, "--json")
        assert out.returncode == 1
        data = json.loads(out.stdout)
        assert data["changed"] == 1
        assert data["regressions"] == 1
        assert data["records"][0]["head"] == "DUPLICATE"
