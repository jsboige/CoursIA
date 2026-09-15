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
        # #16122 -- the finding now carries its DIRECTION, so the message names
        # which of the two questions failed instead of collapsing both into one
        # count ("1 cle(s) orpheline(s)").
        assert "ORPHAN_KEY gone.ipynb" in out
        assert "1 ORPHAN_KEY" in out


# -------- #16122 : the missing direction (tracked file without a key) --------

class TestBaselineUnkeyedFiles:
    """``_baseline_unkeyed_files`` : judged notebooks the baseline does not key.

    The counterpart of ``_baseline_orphan_keys``: #13815 asks "does every key
    have a file?", #16122 asks "does every file have a key?". This is the
    INVENTORY (reported, non-blocking) -- the blocking case is LOST_KEY below.
    """

    def test_finds_unkeyed_file(self):
        assert pd._baseline_unkeyed_files({"a.ipynb": 1.0}, {"a.ipynb", "b.ipynb"}) == ["b.ipynb"]

    def test_none_when_all_keyed(self):
        assert pd._baseline_unkeyed_files({"a.ipynb": 1.0}, {"a.ipynb"}) == []

    def test_empty_population(self):
        assert pd._baseline_unkeyed_files({"a.ipynb": 1.0}, set()) == []

    def test_ordering_deterministic(self):
        assert pd._baseline_unkeyed_files({}, {"z.ipynb", "a.ipynb", "m.ipynb"}) == [
            "a.ipynb", "m.ipynb", "z.ipynb",
        ]


class TestKeysLostByRename:
    """``_keys_lost_by_rename`` : the #15917 regression, and only it.

    A rename that MOVES its key is the routine renumber gesture; a rename that
    DELETES it silently amputates the ratchet. The pair is what tells them
    apart, and neither a brand-new notebook nor a plain deletion is a finding.
    """

    def test_rename_that_dropped_the_key_is_a_finding(self):
        base = {"old.ipynb": 1.0}
        head = {"old.ipynb": 1.0}  # the head baseline still holds the stale key
        assert pd._keys_lost_by_rename(base, head, [("old.ipynb", "new.ipynb")]) == [
            ("old.ipynb", "new.ipynb")
        ]

    def test_rename_that_moved_the_key_is_healthy(self):
        """The routine renumber: the key follows the file. Not a finding."""
        base = {"old.ipynb": 1.0}
        head = {"new.ipynb": 1.0}
        assert pd._keys_lost_by_rename(base, head, [("old.ipynb", "new.ipynb")]) == []

    def test_rename_of_an_unkeyed_notebook_is_not_a_finding(self):
        assert pd._keys_lost_by_rename({}, {"new.ipynb": 1.0}, [("old.ipynb", "new.ipynb")]) == []

    def test_deletion_is_not_a_lost_key(self):
        """A deleted notebook has no rename pair -- ORPHAN_KEY's business, not this."""
        assert pd._keys_lost_by_rename({"gone.ipynb": 1.0}, {}, []) == []

    def test_ordering_deterministic(self):
        base = {"b.ipynb": 1.0, "a.ipynb": 1.0}
        lost = pd._keys_lost_by_rename(base, {}, [("b.ipynb", "B.ipynb"), ("a.ipynb", "A.ipynb")])
        assert lost == [("a.ipynb", "A.ipynb"), ("b.ipynb", "B.ipynb")]


@pytest.fixture
def _rename_repo(tmp_path):
    """Two-commit repo: ``c1`` keys a judged notebook, and the caller renames it.

    The baseline is committed in BOTH commits so ``_baseline_at("HEAD~1")`` has
    a base key set to compare against -- which is the whole point of LOST_KEY.
    """
    repo = tmp_path / "repo"
    tools = repo / "scripts" / "notebook_tools"
    family = repo / "MyIA.AI.Notebooks" / "GameTheory"
    tools.mkdir(parents=True)
    family.mkdir(parents=True)
    subprocess.run(["git", "-C", str(repo), "init", "-q"], check=True)
    (family / "GameTheory-01-Intro.ipynb").write_text("{}", encoding="utf-8")
    (family / "Setup-01-Env.ipynb").write_text("{}", encoding="utf-8")
    _write_baseline(tools, {"MyIA.AI.Notebooks/GameTheory/GameTheory-01-Intro.ipynb": 2000.0})
    _commit(repo, "c1")
    return repo, tools, family


def _commit(repo, message):
    subprocess.run(["git", "-C", str(repo), "add", "-A"], check=True)
    subprocess.run(
        ["git", "-C", str(repo), "-c", "user.email=t@t", "-c", "user.name=t",
         "commit", "-q", "-m", message],
        check=True,
    )


def _wire(monkeypatch, tools):
    """Point the module at the fixture repo."""
    monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
    monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")


class TestCheckOrphansBothDirections:
    """The directions must be told apart: one count cannot name the failure.

    Acceptance #3 of #16122 asks for three cases -- ORPHAN_KEY alone, the new
    direction alone, and HEALTHY. Without the third, the fix is
    indistinguishable from a guard that always screams.
    """

    KEY = "MyIA.AI.Notebooks/GameTheory/GameTheory-01-Intro.ipynb"
    RENAMED = "MyIA.AI.Notebooks/GameTheory/GameTheory-01-Intro-v2.ipynb"

    def test_healthy_rename_that_moves_the_key_is_green(self, _rename_repo, monkeypatch, capsys):
        repo, tools, family = _rename_repo
        subprocess.run(["git", "-C", str(repo), "mv",
                        str(family / "GameTheory-01-Intro.ipynb"),
                        str(family / "GameTheory-01-Intro-v2.ipynb")], check=True)
        _write_baseline(tools, {self.RENAMED: 2000.0})  # key MOVED with the file
        _commit(repo, "c2")
        _wire(monkeypatch, tools)
        assert pd._check_orphans("HEAD~1") == 0
        out = capsys.readouterr().out
        assert "0 LOST_KEY" in out
        # The note must not report "non evalue" on a comparison it DID make: a
        # verdict that contradicts its own measure is the defect this organ is
        # built to catch, so it must not commit it (#16122 review).
        assert "non evalue" not in out
        assert "LOST_KEY evalue contre HEAD~1" in out

    def test_lost_key_alone_fails(self, _rename_repo, monkeypatch, capsys):
        """The #15917 regression: renamed, and the key deleted rather than moved."""
        repo, tools, family = _rename_repo
        subprocess.run(["git", "-C", str(repo), "mv",
                        str(family / "GameTheory-01-Intro.ipynb"),
                        str(family / "GameTheory-01-Intro-v2.ipynb")], check=True)
        _write_baseline(tools, {})  # ... and the key is simply GONE
        _commit(repo, "c2")
        _wire(monkeypatch, tools)
        assert pd._check_orphans("HEAD~1") == 1
        out = capsys.readouterr().out
        assert f"LOST_KEY {self.KEY} -> {self.RENAMED}" in out

    def test_brand_new_notebook_does_not_fail(self, _rename_repo, monkeypatch, capsys):
        """Fleet-safety control: a notebook ADDED un-keyed was never under the
        ratchet, so it must not redden the gate that every PR runs."""
        repo, tools, family = _rename_repo
        (family / "GameTheory-02-Nouveau.ipynb").write_text("{}", encoding="utf-8")
        _commit(repo, "c2")
        _wire(monkeypatch, tools)
        assert pd._check_orphans("HEAD~1") == 0
        out = capsys.readouterr().out
        assert "inventaire UNKEYED_FILE : 1 notebook(s)" in out  # inventoried...
        assert "0 LOST_KEY" in out  # ...but not a failure

    def test_orphan_key_alone_fails(self, _rename_repo, monkeypatch, capsys):
        repo, tools, family = _rename_repo
        _write_baseline(tools, {"gone.ipynb": 1.0})
        _commit(repo, "c2")
        _wire(monkeypatch, tools)
        assert pd._check_orphans("HEAD~1") == 1
        out = capsys.readouterr().out
        assert "ORPHAN_KEY gone.ipynb" in out
        assert "->" not in out  # the LOST_KEY finding format `old -> new`

    def test_setup_notebook_is_never_in_the_inventory(self, _rename_repo, monkeypatch, capsys):
        """Positive control on the population: `setup` is out of the density
        corpus, so an un-keyed setup notebook is not an unkeyed file."""
        repo, tools, family = _rename_repo
        _wire(monkeypatch, tools)
        assert pd._check_orphans() == 0
        assert "Setup-01-Env" not in capsys.readouterr().out

    def test_without_base_the_loss_direction_says_not_evaluated(
        self, _rename_repo, monkeypatch, capsys
    ):
        """No base => no LOST_KEY claim. Honest 'not evaluated', never 'clean'."""
        repo, tools, family = _rename_repo
        _wire(monkeypatch, tools)
        assert pd._check_orphans() == 0
        assert "non evalue" in capsys.readouterr().out

    def test_cli_routes_base_and_reports_the_direction(self, _rename_repo, monkeypatch, capsys):
        repo, tools, family = _rename_repo
        subprocess.run(["git", "-C", str(repo), "mv",
                        str(family / "GameTheory-01-Intro.ipynb"),
                        str(family / "GameTheory-01-Intro-v2.ipynb")], check=True)
        _write_baseline(tools, {})
        _commit(repo, "c2")
        _wire(monkeypatch, tools)
        assert pd.main(["--check-orphans", "--base", "HEAD~1"]) == 1
        assert "LOST_KEY" in capsys.readouterr().out


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
