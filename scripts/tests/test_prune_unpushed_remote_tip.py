#!/usr/bin/env python3
r"""Temoins comportementaux du motif `unpushed_commits` (#23330).

Pinent la confrontation au TIP DISTANT, pas la seule ref de tracking
locale :

1. tip distant == HEAD          -> le motif ne s'applique pas (leve) ;
2. HEAD ancetre du tip distant  -> leve aussi ;
3. tip distant hors base locale -> fail-CLOSED : decompte local conserve ;
4. branche absente du distant   -> fail-CLOSED : refus conserve tel quel ;
5. API indeterminable           -> fail-CLOSED : decompte local conserve ;
6. mode degrade gh (#21753)     -> aucun appel reseau tente ;
7. aucun canal `ls-remote` introduit.

Les témoins 1-6 montent de vrais depots git jetables : la decision est
mesuree sur `git rev-list`, pas sur un mock de git.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


# ---------------------------------------------------------------------------
# harnais git jetable
# ---------------------------------------------------------------------------

def _git(cwd, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(cwd), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=True,
    )
    return proc.stdout.strip()


def _make_repo(tmp_path: Path, name: str = "wt") -> Path:
    """Depot avec un commit c1 sur `main` et un bare `origin` qui le porte."""
    repo = tmp_path / name
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "temoins@example.com")
    _git(repo, "config", "user.name", "Temoins")
    (repo / "a.txt").write_text("c1\n", encoding="utf-8")
    _git(repo, "add", "a.txt")
    _git(repo, "commit", "-q", "-m", "c1")

    origin = tmp_path / f"{name}-origin.git"
    _git(tmp_path, "init", "--bare", "-q", str(origin))
    _git(repo, "remote", "add", "origin", str(origin))
    _git(repo, "push", "-q", "-u", "origin", "main")
    return repo


def _commit(repo: Path, label: str) -> str:
    (repo / "a.txt").write_text(f"{label}\n", encoding="utf-8")
    _git(repo, "add", "a.txt")
    _git(repo, "commit", "-q", "-m", label)
    return _git(repo, "rev-parse", "HEAD")


def _make_stale_tracking_ref(repo: Path, branch: str, sha: str) -> None:
    """Fait pointer la ref de tracking LOCALE sur un commit perime."""
    _git(repo, "update-ref", f"refs/remotes/origin/{branch}", sha)


def _info(repo: Path, monkeypatch, state: str, tip=None) -> dict:
    """`get_worktree_info` avec un tip distant injecte."""
    monkeypatch.setattr(pmw, "_remote_branch_tip", lambda branch: (state, tip))
    monkeypatch.setattr(pmw, "_REMOTE_TIP_MEMO", {})
    return pmw.get_worktree_info(str(repo), str(repo))


@pytest.fixture(autouse=True)
def _no_gh_mode(monkeypatch):
    """Le singleton de resolution ne doit pas se croire en mode degrade."""
    pmw.reset_pr_resolution()


# ---------------------------------------------------------------------------
# 1-2 : le motif se leve quand le distant porte deja le local
# ---------------------------------------------------------------------------

class TestTipDistantPorteLeLocal:
    def test_tip_egal_head_leve_le_refus(self, tmp_path, monkeypatch):
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/posee")
        c2 = _commit(repo, "c2")
        c3 = _commit(repo, "c3")
        _git(repo, "push", "-q", "origin", "feat/posee")
        # ref de tracking locale en retard : c'est la cause racine #23330
        _make_stale_tracking_ref(repo, "feat/posee", _git(repo, "rev-parse", "HEAD~2"))

        # controle : sans confrontation, le decompte local est faux
        pmw.reset_remote_tip_memo()
        monkeypatch.setattr(
            pmw, "_remote_branch_tip", lambda branch: ("unknown", None)
        )
        assert pmw.get_worktree_info(str(repo), str(repo))["ahead_count"] == 2

        info = _info(repo, monkeypatch, "ok", c3)
        assert info["ahead_count"] == 0
        assert c2 != c3

    def test_head_ancetre_du_tip_distant_leve_le_refus(self, tmp_path, monkeypatch):
        repo = _make_repo(tmp_path)
        c2 = _commit(repo, "c2")
        _git(repo, "checkout", "-q", "-b", "feat/retard")
        c3 = _commit(repo, "c3")          # tip distant = c3, connu localement
        _git(repo, "checkout", "-q", "-b", "feat/retard-encore", c2)
        _make_stale_tracking_ref(repo, "feat/retard-encore", _git(repo, "rev-parse", "HEAD~1"))

        info = _info(repo, monkeypatch, "ok", c3)
        assert info["ahead_count"] == 0
        assert pmw.REMOTE_TIP_STATS["cleared_ancestor"] == 1


# ---------------------------------------------------------------------------
# 3-4 : le refus subsiste, avec un decompte qui dit vrai
# ---------------------------------------------------------------------------

class TestRefusConserveDitVrai:
    def test_tip_hors_base_locale_conserve_le_decompte_local(self, tmp_path, monkeypatch):
        """Tip annonce mais absent de la base locale : on ne peut pas le
        confronter, donc on ne disculpe rien -- fail-CLOSED."""
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/locale")
        _commit(repo, "c2")
        _commit(repo, "c3")
        _make_stale_tracking_ref(repo, "feat/locale", _git(repo, "rev-parse", "HEAD~2"))
        inconnu = "0" * 40  # SHA absent de la base locale

        info = _info(repo, monkeypatch, "ok", inconnu)
        assert info["ahead_count"] == 2   # le local, non confronte -> refus

    def test_branche_absente_du_distant_reste_refusee(self, tmp_path, monkeypatch):
        """Branche absente du distant : le distant ne peut pas disculper,
        le refus local est conserve tel quel (#23330, fail-CLOSED)."""
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/jamais-poussee")
        _commit(repo, "c2")
        _make_stale_tracking_ref(repo, "feat/jamais-poussee", _git(repo, "rev-parse", "HEAD~1"))

        info = _info(repo, monkeypatch, "absent", None)
        assert info["ahead_count"] == 1
        assert info["ahead_count"] > 0

    def test_un_commit_reellement_non_pousse_reste_refuse(self, tmp_path, monkeypatch):
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/un-en-plus")
        _git(repo, "push", "-q", "origin", "feat/un-en-plus")
        tip_pousse = _git(repo, "rev-parse", "HEAD")
        _make_stale_tracking_ref(repo, "feat/un-en-plus", tip_pousse)
        _commit(repo, "pas-pousse")          # 1 commit vraiment non pousse

        info = _info(repo, monkeypatch, "ok", tip_pousse)
        assert info["ahead_count"] == 1


# ---------------------------------------------------------------------------
# 5-6 : fail-CLOSED
# ---------------------------------------------------------------------------

class TestFailClosed:
    def test_api_indeterminee_conserve_le_decompte_local(self, tmp_path, monkeypatch):
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/doute")
        _commit(repo, "c2")
        _commit(repo, "c3")
        _make_stale_tracking_ref(repo, "feat/doute", _git(repo, "rev-parse", "HEAD~2"))

        info = _info(repo, monkeypatch, "unknown", None)
        assert info["ahead_count"] == 2   # le local, non mesure -> refus conserve

    def test_mode_degrade_gh_aucun_appel_reseau(self, tmp_path, monkeypatch):
        repo = _make_repo(tmp_path)
        _git(repo, "checkout", "-q", "-b", "feat/degrade")
        _commit(repo, "c2")
        _make_stale_tracking_ref(repo, "feat/degrade", _git(repo, "rev-parse", "HEAD~1"))
        pmw.get_pr_resolution().unavailable_reason = "gh absent (temoin)"

        appels = []
        monkeypatch.setattr(
            pmw, "_remote_branch_tip",
            lambda branch: appels.append(branch) or ("ok", "0" * 40),
        )
        info = pmw.get_worktree_info(str(repo), str(repo))
        assert appels == []
        assert info["ahead_count"] == 1


# ---------------------------------------------------------------------------
# 7 : pas de nouveau canal reseau
# ---------------------------------------------------------------------------

def test_aucun_ls_remote_invoque_par_l_organe():
    """Le mot peut vivre dans la prose ; c'est l'APPEL qui est interdit."""
    source = (Path(pmw.__file__)).read_text(encoding="utf-8")
    invocations = re.findall(r"""["']ls-remote""", source)
    assert invocations == [], (
        "l'organe ne doit pas introduire de second canal reseau (#23330) : "
        "la voie REST `repos/{owner}/{repo}/branches/<b>` suffit"
    )


def test_memo_remis_a_zero_par_passe():
    pmw._REMOTE_TIP_MEMO["b"] = ("ok", "x")
    pmw.REMOTE_TIP_STATS["calls"] = 7
    pmw.reset_remote_tip_memo()
    assert pmw._REMOTE_TIP_MEMO == {}
    assert pmw.REMOTE_TIP_STATS["calls"] == 0
