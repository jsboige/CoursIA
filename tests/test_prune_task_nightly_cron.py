#!/usr/bin/env python3
"""test_prune_task_nightly_cron.py -- tests du cablage du travail nocturne de
prune_merged_worktrees.

Ce que ces tests mesurent : l'ARGUMENTATION que la tache planifiee passe
effectivement a l'organe. C'est la que se joue le defaut #127 : l'organe
sait decontaminer un worktree MERGED a sous-modules (#21743, voie
quarantaine), mais ce n'est qu'un drapeau OPT-IN -- et la tache nocturne ne
le passait pas. Le worktree livre restait alors refuse (`contains_submodules`)
nuit apres nuit.

Les tests n'ont PAS besoin de GH_TOKEN ni de reseau : `subprocess.run` est
patche, seule l'argv reellement construite est observee.
"""
from __future__ import annotations

import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_REPO, "scripts", "ci"))

import install_prune_task as ipt  # noqa: E402


class _FakeProc:
    returncode = 0


class TestNightlyRunArgv(unittest.TestCase):
    """L'argv du travail nocturne : ce que la tache passe a l'organe."""

    def _capture_argv(self, tmpdir: str) -> list[str]:
        captured: dict[str, list[str]] = {}

        def fake_run(argv, **kwargs):
            captured["argv"] = list(argv)
            return _FakeProc()

        with mock.patch.object(ipt.subprocess, "run", fake_run), \
                mock.patch.object(ipt, "LOG_DIR", Path(tmpdir)), \
                mock.patch.object(ipt, "prune_script_path",
                                  lambda repo: os.path.join(str(repo), "prune.py")):
            rc = ipt.cmd_run(Path(tmpdir))
        self.assertEqual(rc, 0)
        return captured["argv"]

    def test_nightly_run_passes_quarantine_submodules(self):
        """#127 : sans ce drapeau, un worktree MERGED a sous-modules reste
        colle au disque, nuit apres nuit."""
        with tempfile.TemporaryDirectory() as d:
            argv = self._capture_argv(d)
        self.assertIn("--quarantine-submodules", argv)

    def test_nightly_run_keeps_apply_and_path(self):
        """Le geste reste une purge, sur le depot vise, avec le seuil
        d'alerte : la decontamination ne doit pas degrader le reste."""
        with tempfile.TemporaryDirectory() as d:
            argv = self._capture_argv(d)
        self.assertIn("--apply", argv)
        self.assertIn("--path", argv)
        self.assertIn("--warn-threshold", argv)

    def test_nightly_run_never_forces_removal(self):
        """`--force` est interdit par #14619 point 4 : le retrait passe par
        `git worktree remove` sans drapeau, ou par la quarantaine."""
        with tempfile.TemporaryDirectory() as d:
            argv = self._capture_argv(d)
        self.assertNotIn("--force", argv)
        self.assertNotIn("-f", argv)


if __name__ == "__main__":
    unittest.main()
