#!/usr/bin/env python3
"""test_prune_merged_worktrees.py -- tests unitaires pour la garde
« agent vivant » de prune_merged_worktrees.py (#18494).

Deux niveaux :

- fonctions deterministes pures (age du marqueur d'activite) -- CPU seul ;
- le predicat content_on_main de diagnose_worktree sur un depot git
  ephemere (init local + origin bare + worktree sans commit propre).
  La resolution PR y est patchee : ce que ces tests mesurent est la
  FENETRE D'ACTIVITE, pas l'ancre gh (deja couverte par sa propre
  couche a trois etages, #15369).

Les tests n'ont PAS besoin de GH_TOKEN ni de reseau.
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_REPO, "scripts", "ci"))

import prune_merged_worktrees as pmw  # noqa: E402


class TestRecentActivityAgeHours(unittest.TestCase):
    """Age du marqueur d'activite : le plus jeune des deux gouverne."""

    def test_fresh_directory_is_recent(self):
        with tempfile.TemporaryDirectory() as d:
            age = pmw.recent_activity_age_hours(d)
            self.assertLess(age, 0.1)

    def test_old_directory_no_lane_owner(self):
        with tempfile.TemporaryDirectory() as d:
            old = time.time() - 10 * 3600
            os.utime(d, (old, old))
            age = pmw.recent_activity_age_hours(d)
            self.assertGreater(age, 9.9)
            self.assertLess(age, 10.1)

    def test_fresh_lane_owner_beats_old_directory(self):
        # Cas de la mesure fondatrice (#18494) : le dossier date du spawn,
        # le marqueur .lane-owner vient d'etre pose -- actif.
        with tempfile.TemporaryDirectory() as d:
            old = time.time() - 10 * 3600
            os.utime(d, (old, old))
            with open(os.path.join(d, ".lane-owner"), "w",
                      encoding="utf-8") as f:
                f.write("myia-po-2027:CoursIA\n")
            age = pmw.recent_activity_age_hours(d)
            self.assertLess(age, 0.1)

    def test_unreadable_path_is_infinite(self):
        age = pmw.recent_activity_age_hours(
            os.path.join(tempfile.gettempdir(), "nope-18494", "wt"))
        self.assertEqual(age, float("inf"))


def _run_git(cwd, *args):
    subprocess.run(
        ["git", "-C", cwd, *args],
        capture_output=True, text=True, encoding="utf-8", check=True,
    )


class TestActivityWindowPredicate(unittest.TestCase):
    """Acceptance #18494 sur un depot ephemere.

    Le worktree cible est celui d'un « agent vivant en phase de lecture » :
    branche sans commit propre, HEAD ancetre de origin/main, arbre propre.
    """

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        root = self._tmp.name
        # Depot de travail + origin bare : origin/main doit exister pour
        # que head_is_ancestor_of_main tranne (sinon le predicat 5 n'est
        # meme pas atteint).
        self.repo = os.path.join(root, "repo")
        self.origin = os.path.join(root, "origin.git")
        self.wt = os.path.join(root, "wt-agent")
        os.makedirs(self.repo)
        _run_git(self.repo, "init", "-b", "main")
        _run_git(self.repo, "config", "user.email", "t@example.invalid")
        _run_git(self.repo, "config", "user.name", "Test 18494")
        with open(os.path.join(self.repo, "f.txt"), "w",
                  encoding="utf-8") as f:
            f.write("init\n")
        _run_git(self.repo, "add", "f.txt")
        _run_git(self.repo, "commit", "-m", "init")
        _run_git(self.repo, "init", "--bare", self.origin)
        _run_git(self.repo, "remote", "add", "origin", self.origin)
        _run_git(self.repo, "push", "-u", "origin", "main")
        # Worktree « agent vivant » : branche neuve sur la pointe de main,
        # aucun commit propre, aucun fichier.
        _run_git(self.repo, "worktree", "add", self.wt, "-b", "topic-agent")
        # Le repo de travail doit voir origin/main (fetch implicite via
        # push -u ; le worktree partage les refs du depot hebergeur).
        _run_git(self.wt, "fetch", "origin", "main")
        # Resolution PR patchee : hermetique, et le cas mesure n'a de
        # toute facon aucune PR.
        patcher = mock.patch.object(
            pmw, "lookup_pr_for_branch", lambda branch, head_sha=None: None)
        patcher.start()
        self.addCleanup(patcher.stop)
        patcher2 = mock.patch.object(
            pmw, "remote_head_for_head",
            lambda wt_path, branch, head_sha: None)
        patcher2.start()
        self.addCleanup(patcher2.stop)
        pmw.reset_pr_resolution()

    def tearDown(self):
        pmw.reset_pr_resolution()
        self._tmp.cleanup()

    def _diagnose(self, window_h=6.0):
        return pmw.diagnose_worktree(
            self.wt, current_path=self.repo,
            head_sha=None, activity_window_h=window_h,
        )

    def test_active_agent_is_refused_never_removed(self):
        # Acceptance 1 : dry-run pendant qu'un agent travaille (worktree
        # cree a l'instant, donc marqueur d'activite frais) -> REFUSE,
        # jamais REMOVE.
        status = self._diagnose()
        self.assertEqual(status.decision, "REFUSE")
        self.assertTrue(status.refusal_reason.startswith("recent_activity:"))
        self.assertTrue(status.content_on_main)

    def test_stale_activity_becomes_removable_again(self):
        # Acceptance 2 : le marqueur depasse la fenetre -> retour au
        # retrait par contenu deja integre. Le refus protege la phase de
        # travail, il ne conserve rien indefiniment.
        old = time.time() - 10 * 3600
        os.utime(self.wt, (old, old))
        status = self._diagnose()
        self.assertEqual(status.decision, "REMOVE")
        self.assertTrue(status.content_on_main)
        self.assertIsNone(status.refusal_reason)

    def test_window_parameter_moves_the_boundary(self):
        # La fenetre est un parametre : avec 12 h, un worktree inactif
        # depuis 10 h est encore protege.
        old = time.time() - 10 * 3600
        os.utime(self.wt, (old, old))
        self.assertEqual(self._diagnose(window_h=6.0).decision, "REMOVE")
        self.assertEqual(self._diagnose(window_h=12.0).decision, "REFUSE")

    def test_lane_owner_marker_protects_old_directory(self):
        # .lane-owner frais sur un dossier vieux : le marqueur le plus
        # jeune gouverne, le worktree reste protege.
        old = time.time() - 10 * 3600
        os.utime(self.wt, (old, old))
        with open(os.path.join(self.wt, ".lane-owner"), "w",
                  encoding="utf-8") as f:
            f.write("myia-po-2027:CoursIA\n")
        status = self._diagnose()
        self.assertEqual(status.decision, "REFUSE")
        self.assertTrue(status.refusal_reason.startswith("recent_activity:"))


if __name__ == "__main__":
    unittest.main()
