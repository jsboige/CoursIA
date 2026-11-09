#!/usr/bin/env python3
r"""Tests du predicat 1 ``unpushed_commits`` apres le fix #20009.

Pinent, sur une fixture git reelle (origin bare + clone + 3 worktrees) :
1. le ref distant homonyme prime sur ``@{u}`` : une branche « photographie
   d'un main ancien » avec ``@{u}`` = branche soeur n'est PLUS refusee
   ``unpushed_commits`` alors que l'ancien instrument rendait ahead=1+ ;
2. la garde ancestor-of-main du predicat 1 : meme sans homonyme distant,
   un HEAD ancetre de ``origin/main`` n'est pas refuse pour un artefact
   ``@{u}`` -- il tombe dans le flot normal (fenetre d'activite #18494,
   puis content_on_main) ;
3. temoin negatif : une branche avec 1 commit propre non pousse reste
   REFUSE ``unpushed_commits:1``, compte exact contre le homonyme.

La mesure fondatrice (po-2024, #20009) : 5 worktrees refuses
``unpushed_commits:210`` avec 0 commit propre et SHA identique au ref
distant homonyme -- ``@{u}`` pointait une branche soeur de pile.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


def _git(cwd, *args, check=True):
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    if check and proc.returncode != 0:
        raise AssertionError(f"git {' '.join(args)} -> rc={proc.returncode}: {proc.stderr}")
    return proc


def _commit(repo, path, content, msg):
    (repo / path).write_text(content, encoding="utf-8")
    _git(repo, "add", path)
    _git(repo, "commit", "-m", msg)


class _Fixture:
    """origin (bare) + clone portant les 3 branches du cas #20009.

    Historique construit :

      main : A -- B -- C            (pousse ; origin/main = C)
      base/stack : A -- s1 -- s2    (branche soeur, poussee)
      fix/photograph : B            (0 commit propre, homonyme pousse a B)
      fix/artifact : B              (0 commit propre, JAMAIS poussee,
                                     @{u} = origin/base/stack -> artefact)
      fix/own-work : B -- o1        (1 commit propre, homonyme pousse a B
                                     puis avance localement -> avance reelle)
    """

    def __init__(self, tmp_path: Path):
        origin = tmp_path / "origin.git"
        origin.mkdir()
        _git(origin, "init", "--bare", "-b", "main")

        seed = tmp_path / "seed"
        seed.mkdir()
        _git(seed, "init", "-b", "main")
        _git(seed, "config", "user.name", "T")
        _git(seed, "config", "user.email", "t@example.invalid")
        _commit(seed, "a.txt", "a\n", "A")
        sha_a = _git(seed, "rev-parse", "HEAD").stdout.strip()
        _commit(seed, "b.txt", "b\n", "B")
        sha_b = _git(seed, "rev-parse", "HEAD").stdout.strip()
        _commit(seed, "c.txt", "c\n", "C")
        _git(seed, "remote", "add", "origin", str(origin))
        _git(seed, "push", "origin", "main")

        clone = tmp_path / "clone"
        _git(tmp_path, "clone", str(origin), "clone")
        _git(clone, "config", "user.name", "T")
        _git(clone, "config", "user.email", "t@example.invalid")

        # Branche soeur de pile, forkee au main ancien A.
        _git(clone, "checkout", "-b", "base/stack", sha_a)
        _commit(clone, "s1.txt", "s1\n", "s1")
        _commit(clone, "s2.txt", "s2\n", "s2")
        _git(clone, "push", "origin", "base/stack")

        # Photographie d'un main ancien (B), homonyme distant pousse.
        _git(clone, "checkout", "-b", "fix/photograph", sha_b)
        _git(clone, "push", "origin", "fix/photograph")
        # LE BUG mesure : @{u} herite de la base de pile, pas du homonyme.
        _git(clone, "branch", "--set-upstream-to=origin/base/stack", "fix/photograph")

        # Artefact pur : B jamais pousse, @{u} = branche soeur.
        _git(clone, "branch", "fix/artifact", sha_b)
        _git(clone, "branch", "--set-upstream-to=origin/base/stack", "fix/artifact")

        # Temoin negatif : 1 commit propre au-dela du homonyme pousse.
        _git(clone, "branch", "fix/own-work", sha_b)
        _git(clone, "push", "origin", "fix/own-work")
        _git(clone, "checkout", "fix/own-work")
        _commit(clone, "o1.txt", "o1\n", "o1")
        # Liberer la branche pour le worktree (un checkout par branche).
        _git(clone, "checkout", "--detach")

        self.clone = clone
        self.wts = {}
        for name in ("fix/photograph", "fix/artifact", "fix/own-work"):
            wt = tmp_path / ("wt-" + name.replace("/", "-"))
            _git(clone, "worktree", "add", str(wt), name)
            self.wts[name] = wt


class TestUnpushedPredicateFix:
    def test_homonym_ref_wins_over_sister_upstream(self, tmp_path):
        """fix/photograph : ahead=0 contre le homonyme (l'ancien instrument
        rendait 1+ contre @{u} soeur), et le verdict n'est pas unpushed."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["fix/photograph"]
        info = pmw.get_worktree_info(str(wt), str(fx.clone))
        assert info["branch"] == "fix/photograph"
        assert info["ahead_count"] == 0, (
            "le homonyme origin/fix/photograph porte le meme SHA : "
            "l'avance doit etre 0, pas l'ecart a la branche soeur"
        )

    def test_ancestor_guard_bypasses_artifact_when_homonym_absent(self, tmp_path):
        """fix/artifact : homonyme absent, @{u} soeur -> artefact ahead=1,
        mais HEAD (B) est ancetre de origin/main : pas de refus unpushed,
        le flot normal tranche (fenetre d'activite, puis content_on_main)."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["fix/artifact"]
        info = pmw.get_worktree_info(str(wt), str(fx.clone))
        assert info["ahead_count"] == 1, "l'artefact @{u} doit bien mesurer 1 ici"

        saved = pmw.lookup_pr_for_branch
        try:
            pmw.lookup_pr_for_branch = lambda branch, head_sha=None: None
            # Fenetre d'activite ouverte : le worktree frais est protege
            # (prouve la chute dans le flot normal, pas un retrait aveugle).
            st = pmw.diagnose_worktree(str(wt), str(fx.clone), activity_window_h=6.0)
            assert st.decision == "REFUSE"
            assert st.refusal_reason.startswith("recent_activity:")
            assert not st.refusal_reason.startswith("unpushed_commits")
            # Fenetre passee : retrait par contenu, jamais par unpushed.
            st2 = pmw.diagnose_worktree(str(wt), str(fx.clone), activity_window_h=0.0)
            assert st2.decision == "REMOVE"
            assert st2.refusal_reason is None
            assert st2.content_on_main is True
        finally:
            pmw.lookup_pr_for_branch = saved

    def test_negative_witness_own_unpushed_commit_stays_refused(self, tmp_path):
        """fix/own-work : 1 commit propre au-dela du homonyme pousse ->
        REFUSE unpushed_commits:1, compte exact. Le fix ne desserre rien
        pour du travail reel."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["fix/own-work"]
        info = pmw.get_worktree_info(str(wt), str(fx.clone))
        assert info["ahead_count"] == 1
        saved = pmw.lookup_pr_for_branch
        try:
            pmw.lookup_pr_for_branch = lambda branch, head_sha=None: None
            st = pmw.diagnose_worktree(str(wt), str(fx.clone), activity_window_h=0.0)
            assert st.decision == "REFUSE"
            assert st.refusal_reason == "unpushed_commits:1"
        finally:
            pmw.lookup_pr_for_branch = saved

    def test_photograph_reaches_content_on_main_remove(self, tmp_path):
        """fix/photograph pousse au homonyme : meme sans PR attribuable,
        le verdict terminal est REMOVE par contenu (le precedent mesurait
        un refus unpushed_commits:1 avant le fix)."""
        fx = _Fixture(tmp_path)
        wt = fx.wts["fix/photograph"]
        saved = pmw.lookup_pr_for_branch
        try:
            pmw.lookup_pr_for_branch = lambda branch, head_sha=None: None
            st = pmw.diagnose_worktree(str(wt), str(fx.clone), activity_window_h=0.0)
            assert st.decision == "REMOVE"
            assert st.content_on_main is True
        finally:
            pmw.lookup_pr_for_branch = saved
