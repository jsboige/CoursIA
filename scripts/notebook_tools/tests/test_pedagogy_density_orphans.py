"""Tests for the #13815 orphan organ of scripts/notebook_tools/pedagogy_density.py.

The baseline records one density float per tracked notebook. #13815: a rename
or a delete leaves the old path out of ``git ls-files``; that key becomes an
orphan whose float the Phase-2 ratchet would read as a real measurement on a
path that no longer exists. These tests pin the pure orphan set and the
advisory organ's exit code against a self-contained git fixture.
"""

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import pedagogy_density as pd

import pytest


# -------- Pure orphan-set logic --------

class TestBaselineOrphanKeys:
    """``_baseline_orphan_keys`` : keys absent from the tracked set are orphans."""

    def test_finds_orphan(self):
        baseline = {"a.ipynb": 1.0, "b.ipynb": 2.0}
        assert pd._baseline_orphan_keys(baseline, {"a.ipynb"}) == ["b.ipynb"]

    def test_none_when_all_tracked(self):
        baseline = {"a.ipynb": 1.0}
        assert pd._baseline_orphan_keys(baseline, {"a.ipynb"}) == []

    def test_empty_baseline(self):
        assert pd._baseline_orphan_keys({}, {"a.ipynb"}) == []

    def test_orphan_ordering_deterministic(self):
        baseline = {"z.ipynb": 1.0, "a.ipynb": 2.0, "m.ipynb": 3.0}
        assert pd._baseline_orphan_keys(baseline, {"only.ipynb"}) == [
            "a.ipynb", "m.ipynb", "z.ipynb",
        ]


# -------- Organ integration (real git fixture) --------

@pytest.fixture
def _fixture_repo(tmp_path):
    """Build ``tmp_path/repo`` with a tracked ``notebookA.ipynb``.

    Returns ``(repo_root, tools_dir)`` where ``tools_dir`` mirrors the module
    layout (``<repo>/scripts/notebook_tools``) so ``._TOOLS_DIR.parents[1]`` is
    the git repo root.
    """
    repo = tmp_path / "repo"
    tools = repo / "scripts" / "notebook_tools"
    tools.mkdir(parents=True)
    git = ["git", "-C", str(repo)]
    subprocess.run([*git, "init", "-q"], check=True)
    nb = repo / "notebookA.ipynb"
    nb.write_text("{}", encoding="utf-8")
    subprocess.run([*git, "add", "."], check=True)
    subprocess.run(
        [*git, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "c1"],
        check=True,
    )
    return repo, tools


def _write_baseline(tools, notebooks):
    baseline = {
        "_comment": "test fixture",
        "metric": "prose_chars / code_cells",
        "count": len(notebooks),
        "notebooks": notebooks,
    }
    (tools / "pedagogy_density_baseline.json").write_text(
        json.dumps(baseline), encoding="utf-8",
    )


class TestCheckOrphans:
    """``--check-orphans`` returns non-zero when the baseline carries orphans."""

    def test_detects_orphan(self, _fixture_repo, monkeypatch):
        repo, tools = _fixture_repo
        _write_baseline(tools, {"notebookA.ipynb": 1.0, "gone.ipynb": 2.0})
        monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
        monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")
        assert pd._check_orphans() == 1

    def test_clean_when_no_orphan(self, _fixture_repo, monkeypatch):
        repo, tools = _fixture_repo
        _write_baseline(tools, {"notebookA.ipynb": 1.0})
        monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
        monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")
        assert pd._check_orphans() == 0

    def test_cli_flag_routes_to_check_orphans(self, _fixture_repo, monkeypatch, capsys):
        repo, tools = _fixture_repo
        _write_baseline(tools, {"notebookA.ipynb": 1.0, "gone.ipynb": 2.0})
        monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
        monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")
        assert pd.main(["--check-orphans"]) == 1
        out = capsys.readouterr().out
        assert "gone.ipynb" in out
        assert "1 cle(s) orpheline(s)" in out


# -------- Non-ASCII paths (regression: git quoting, not Python decoding) --------

@pytest.fixture
def _accented_repo(tmp_path):
    """Fixture repo tracking a notebook whose name carries a non-ASCII char.

    ``core.quotepath`` is pinned to ``true`` -- git's own default -- so the
    control is deterministic on any machine: git then emits the path
    octal-escaped AND double-quoted (``"cafÃ©.ipynb"``), which no
    baseline key can ever equal. The defect is in git's rendering, upstream of
    any Python decoding, so ``encoding="utf-8"`` on the subprocess does not
    prevent it -- only ``-c core.quotepath=false`` does.
    """
    repo = tmp_path / "repo"
    tools = repo / "scripts" / "notebook_tools"
    tools.mkdir(parents=True)
    git = ["git", "-C", str(repo)]
    subprocess.run([*git, "init", "-q"], check=True)
    subprocess.run([*git, "config", "core.quotepath", "true"], check=True)
    (repo / "café.ipynb").write_text("{}", encoding="utf-8")
    subprocess.run([*git, "add", "."], check=True)
    subprocess.run(
        [*git, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "c1"],
        check=True,
    )
    return repo, tools


class TestNonAsciiPathsAreNotOrphans:
    """A tracked non-ASCII path must never be reported as an orphan.

    Measured on the real repo (2026-08-31): without the fix the organ counted
    48 orphans, with it 47 -- the 48th being the tracked notebook
    ``GenAI/SemanticKernel/Créateur de mail personnalisé.ipynb``.
    A count that depends on the reader's git config is not a measurement, and
    a CI gate wired to it would disagree with itself across machines.
    """

    def test_tracked_accented_path_is_not_orphan(self, _accented_repo, monkeypatch):
        repo, tools = _accented_repo
        _write_baseline(tools, {"café.ipynb": 1.0})
        monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
        monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")
        assert pd._check_orphans() == 0

    def test_git_listing_carries_no_escaping(self, _accented_repo, monkeypatch):
        """Positive control: the listing itself must hold the literal path."""
        repo, tools = _accented_repo
        monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
        listed = pd._tracked_notebook_paths()
        assert "café.ipynb" in listed
        assert not any(k.startswith('"') or "\3" in k for k in listed)
