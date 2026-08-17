"""Tests for check_papermill_ratchet.py — ratchet gate (#11155 tier 2).

Pins the ratchet contract on a miniature git history: changed outputs riding
a byte-identical metadata.papermill block fail; every legal combination
(markdown-only edit, block removed, block moved, block added, notebook
added) passes. No network, no kernel.
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_papermill_ratchet as gate


def make_nb(outputs_by_cell, papermill=None, exec_counts=None):
    n = len(outputs_by_cell)
    counts = exec_counts or list(range(1, n + 1))
    cells = [{"cell_type": "code", "execution_count": ec,
              "source": f"print({i})", "outputs": outs, "metadata": {}}
             for i, (ec, outs) in enumerate(zip(counts, outputs_by_cell))]
    nb = {"cells": cells, "metadata": {}, "nbformat": 4,
          "nbformat_minor": 5}
    if papermill is not None:
        nb["metadata"]["papermill"] = papermill
    return nb


PM = {"input_path": "a.ipynb", "output_path": "a.ipynb",
      "start_time": "2026-08-16T10:00:00", "end_time": "2026-08-16T10:01:00",
      "duration": 60.0, "exception": False}
PM2 = dict(PM, start_time="2026-08-17T10:00:00",
           end_time="2026-08-17T10:02:00", duration=120.0)
OUT1 = [{"output_type": "stream", "name": "stdout", "text": "hello"}]
OUT2 = [{"output_type": "stream", "name": "stdout", "text": "world"}]


def write_nb(repo, rel, nb):
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb), encoding="utf-8")


def git_ok(repo, *args):
    return subprocess.run(["git", *args], cwd=repo, check=True,
                          capture_output=True, encoding="utf-8")


@pytest.fixture
def repo(tmp_path):
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


class TestRegression:
    def test_changed_outputs_identical_block_fails(self, repo):
        """The exact case #11155: outputs changed, block byte-identical."""
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2], papermill=PM))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs == [{"notebook": "a.ipynb", "verdict": "STALE_BLOCK",
                         "regression": True}]

    def test_execution_count_change_alone_fails(self, repo):
        """Re-numbered evidence with identical outputs+block is stale too."""
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM,
                                          exec_counts=[1]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM,
                                          exec_counts=[7]))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0]["regression"] is True
        assert recs[0]["verdict"] == "STALE_BLOCK"


class TestLegalPasses:
    def test_markdown_only_edit_passes(self, repo):
        """Outputs untouched: a later markdown-only edit rides the block."""
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        nb = make_nb([OUT1], papermill=PM)
        nb["cells"].insert(0, {"cell_type": "markdown",
                               "source": "# new prose", "metadata": {}})
        write_nb(repo, "a.ipynb", nb)
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0] == {"notebook": "a.ipynb",
                           "verdict": "OUTPUTS_UNCHANGED",
                           "regression": False}

    def test_block_removed_passes(self, repo):
        """Block removed at head - explicitly allowed by the issue."""
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2]))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0] == {"notebook": "a.ipynb",
                           "verdict": "BLOCK_REMOVED",
                           "regression": False}

    def test_block_moved_passes(self, repo):
        """Executor rewrote the block alongside the new outputs."""
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2], papermill=PM2))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0]["verdict"] == "BLOCK_MOVED"
        assert recs[0]["regression"] is False

    def test_block_added_passes(self, repo):
        """Head gains a block it never had - an improvement, never a fail."""
        write_nb(repo, "a.ipynb", make_nb([OUT1]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2], papermill=PM))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0]["verdict"] == "BLOCK_ADDED"
        assert recs[0]["regression"] is False

    def test_added_notebook_reported_not_failed(self, repo):
        write_nb(repo, "keep", "x")
        base = commit(repo, "base")
        write_nb(repo, "new.ipynb", make_nb([OUT1], papermill=PM))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs == [{"notebook": "new.ipynb", "verdict": "ADDED",
                         "regression": False}]

    def test_block_key_order_irrelevant(self, repo):
        """Same block content, different key order = identical block."""
        pm_reorder = {k: PM[k] for k in reversed(list(PM.keys()))}
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2], papermill=pm_reorder))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs[0]["verdict"] == "STALE_BLOCK"


class TestExclusions:
    def test_output_copies_excluded(self, repo):
        write_nb(repo, "keep", "x")
        base = commit(repo, "base")
        write_nb(repo, "sub/_output/x.ipynb", make_nb([OUT1], papermill=PM))
        commit(repo, "head")
        recs = gate.ratchet(base, cwd=repo)
        assert recs == []


class TestMain:
    def test_exit_code_on_regression(self, repo, capsys, monkeypatch):
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([OUT2], papermill=PM))
        commit(repo, "head")
        monkeypatch.chdir(repo)
        sys.argv = ["check_papermill_ratchet.py", base]
        with pytest.raises(SystemExit) as exc:
            gate.main()
        assert exc.value.code == 1
        assert "::error file=a.ipynb" in capsys.readouterr().err

    def test_exit_zero_when_clean(self, repo, monkeypatch):
        write_nb(repo, "a.ipynb", make_nb([OUT1], papermill=PM))
        base = commit(repo, "base")
        nb = make_nb([OUT1], papermill=PM)
        nb["cells"][0]["source"] = "print(9)"
        write_nb(repo, "a.ipynb", nb)
        commit(repo, "head")
        monkeypatch.chdir(repo)
        sys.argv = ["check_papermill_ratchet.py", base]
        with pytest.raises(SystemExit) as exc:
            gate.main()
        assert exc.value.code == 0
