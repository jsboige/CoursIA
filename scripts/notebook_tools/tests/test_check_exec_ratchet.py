"""Tests for check_exec_ratchet.py — ratchet gate (#11112 tier 2).

Pins the ratchet contract on a real miniature git history: a notebook whose
sequence was CLEAN at base must stay CLEAN at head; a base-dirty notebook is
never required to improve; added notebooks are reported, not failed. No
network, no kernel.
"""
import errno
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


class TestBaseAdvancedMeanwhile:
    """A branch behind its base is judged on ITS diff, not on the gap.

    Every other test in this file passes a base that is an ANCESTOR of HEAD,
    where tree-to-tree and merge-base comparisons coincide -- which is the
    only topology the suite covered, and why the defect lived here unseen
    while its byte-identical twin was being fixed (#11532 -> #11627).

    The false verdict here is sign-reversed and therefore convincing: main
    re-executes a notebook DUPLICATE -> CLEAN, the stale branch still holds
    the old blob, and a tree-to-tree read calls that CLEAN -> DUPLICATE --
    a "regression" in a file the branch never opened.
    """

    def _diverge(self, repo):
        """base holds two notebooks; the branch edits one, base fixes the
        other. Returns the base-branch tip sha."""
        write_nb(repo, "mine.ipynb", make_nb([1, 2, 3]))
        write_nb(repo, "theirs.ipynb", make_nb([1, 2, 2]))
        commit(repo, "base")
        base_branch = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=repo,
            check=True, capture_output=True, encoding="utf-8").stdout.strip()
        git_ok(repo, "checkout", "-q", "-b", "feature")
        nb = make_nb([1, 2, 3])
        nb["cells"].insert(0, {"cell_type": "markdown",
                               "source": "# new prose", "metadata": {}})
        write_nb(repo, "mine.ipynb", nb)
        commit(repo, "feature: markdown only")
        git_ok(repo, "checkout", "-q", base_branch)
        # main re-executes the OTHER notebook: DUPLICATE -> CLEAN
        write_nb(repo, "theirs.ipynb", make_nb([1, 2, 3]))
        tip = commit(repo, "base advances")
        git_ok(repo, "checkout", "-q", "feature")
        return tip

    def test_base_side_changes_are_not_attributed_to_the_branch(self, repo):
        tip = self._diverge(repo)
        recs = ratchet.ratchet(tip, cwd=repo)
        assert [r["notebook"] for r in recs] == ["mine.ipynb"]
        assert recs[0]["regression"] is False

    def test_a_real_regression_on_a_stale_branch_is_still_caught(self, repo):
        """The fix removes false positives without blunting the gate."""
        tip = self._diverge(repo)
        write_nb(repo, "mine.ipynb", make_nb([1, 2, 2]))
        commit(repo, "feature: sequence soiled")
        recs = ratchet.ratchet(tip, cwd=repo)
        assert [r["notebook"] for r in recs] == ["mine.ipynb"]
        assert recs[0] == {"notebook": "mine.ipynb", "base": "CLEAN",
                           "head": "DUPLICATE", "regression": True}

    def test_resolve_base_falls_back_when_no_merge_base(self, repo):
        """Unrelated histories (shallow clone): previous behaviour kept."""
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        commit(repo, "base")
        assert ratchet.resolve_base("no-such-ref", cwd=repo) == "no-such-ref"


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

    def test_failure_points_to_failbydesign_protocol(self, repo):
        write_nb(repo, "a.ipynb", make_nb([1, 2, 3]))
        base = commit(repo, "base")
        write_nb(repo, "a.ipynb", make_nb([2, 2, 3]))
        commit(repo, "head")
        out = self.run_cli(repo, base)
        assert out.returncode == 1
        assert "fail-by-design" in out.stderr
        assert "regles-validation-detail.md" in out.stderr
        assert "never hand-edit" in out.stderr

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


class TestTransientSpawnRetry:
    """EAGAIN au spawn = contention de processus transitoire (pytest-xdist
    -n 4 sur le runner). Le `except OSError: return None` historique
    transformait ce pic en "changed notebooks : 0" -> faux vert CI (flake
    #16125) : le wrapper doit retenter borne, pas rendre None au premier
    echec de spawn."""

    def _patch_run(self, monkeypatch, etat, resultat_ok):
        import errno as _errno

        def faux_run(*args, **kwargs):
            etat["appels"] += 1
            if etat["appels"] <= etat["echecs"]:
                raise BlockingIOError(_errno.EAGAIN,
                                      "Resource temporarily unavailable")
            return resultat_ok

        monkeypatch.setattr(ratchet.time, "sleep",
                            lambda s: etat["dors"].append(s))
        monkeypatch.setattr(ratchet.subprocess, "run", faux_run)

    def test_eagain_retente_puis_passe(self, monkeypatch):
        etat = {"appels": 0, "echecs": 2, "dors": []}
        ok = subprocess.CompletedProcess(args=(), returncode=0, stdout="ok\n")
        self._patch_run(monkeypatch, etat, ok)
        assert ratchet.git("status") == "ok\n"
        assert etat["appels"] == 3
        assert etat["dors"] == list(ratchet._EAGAIN_BACKOFF)

    def test_autre_oserror_leve_instrument_indisponible(self, monkeypatch):
        # #16164 : un spawn rate qui n'est pas EAGAIN (git absent, EACCES)
        # n'est pas une reponse -- l'instrument n'a pas tourne.
        etat = {"appels": 0, "echecs": 1, "dors": []}
        import errno as _errno

        def faux_run(*args, **kwargs):
            etat["appels"] += 1
            raise OSError(_errno.ENOENT, "git introuvable")

        monkeypatch.setattr(ratchet.time, "sleep",
                            lambda s: etat["dors"].append(s))
        monkeypatch.setattr(ratchet.subprocess, "run", faux_run)
        with pytest.raises(ratchet.InstrumentUnavailable):
            ratchet.git("status")
        assert etat["appels"] == 1
        assert etat["dors"] == []

    def test_eagain_epuise_leve_instrument_indisponible(self, monkeypatch):
        # #16164 : a l'epuisement des retries, l'echec de spawn monte au
        # CLI (exit 2) au lieu du faux vert « changed notebooks : 0 ».
        etat = {"appels": 0, "echecs": 99, "dors": []}
        ok = subprocess.CompletedProcess(args=(), returncode=0, stdout="ok\n")
        self._patch_run(monkeypatch, etat, ok)
        with pytest.raises(ratchet.InstrumentUnavailable):
            ratchet.git("status")
        assert etat["appels"] == ratchet._EAGAIN_ATTEMPTS
        assert etat["dors"] == list(ratchet._EAGAIN_BACKOFF)


class TestInstrumentIndisponible:
    """#16164 : « n'a pas pu mesurer » n'est pas « a mesure 0 ».

    Le contrat lenient historique (git() -> None -> « changed notebooks :
    0 » -> exit 0) confondait l'echec de spawn avec une mesure nulle. La
    decision arbitree ici : fail-closed sur instrument indisponible, en
    convergence avec le canon (check_kernel_suffix_canon.py laisse
    l'OSError propager) ; exit 2 reste distinct de 1 (regression) et de
    0 (mesure faite, rien a signaler).
    """

    def test_verdict_at_base_ne_dit_pas_absent_si_le_blob_est_illisible(
            self, monkeypatch):
        # git show en echec de SPAWN n'est pas un blob absent : avant #16164
        # l'OSError avaldee faisait lire ABSENT (donc « ajoute par la PR »)
        # a un notebook existant a la base.
        def faux_git(*args, **kwargs):
            raise ratchet.InstrumentUnavailable(
                OSError(errno.EAGAIN, "Resource temporarily unavailable"))

        monkeypatch.setattr(ratchet, "git", faux_git)
        with pytest.raises(ratchet.InstrumentUnavailable):
            ratchet.verdict_at_base("origin/main", "a.ipynb")

    def test_cli_exit_2_instrument_indisponible(self, monkeypatch, capsys):
        # distinct de 0 (mesure propre) et de 1 (regression) ; le message
        # nomme l'echec de spawn et ne imprime PAS « changed notebooks ».
        def faux_git(*args, **kwargs):
            raise ratchet.InstrumentUnavailable(
                OSError(errno.EAGAIN, "Resource temporarily unavailable"))

        monkeypatch.setattr(ratchet, "git", faux_git)
        monkeypatch.setattr(sys, "argv",
                            ["check_exec_ratchet.py", "origin/main"])
        with pytest.raises(SystemExit) as sortie:
            ratchet.main()
        assert sortie.value.code == 2
        capture = capsys.readouterr()
        assert "instrument indisponible" in capture.err
        assert "changed notebooks" not in capture.out
        assert "changed notebooks" not in capture.err
