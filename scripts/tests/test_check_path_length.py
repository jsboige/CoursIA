#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests pour le garde cliquet de longueur de chemin (#27676).

Le contrat de l'organe tient en trois controles :
- un **rouge fondateur** : un chemin ajoute au-dessus de la borne doit etre
  attrape (le cas qui a casse les worktrees Windows) ;
- des **contreles faux-positif** : un chemin modifie ou supprime ne doit PAS
  etre juge (le cliquet ne porte que sur les chemins introduits), et un chemin
  de longueur exactement egale a la borne doit passer ;
- un **verdict stable** : sur le depot, le nombre de chemins trop longs parmi
  les ajouts est une metrique (le stock pre-existant n'est pas rouge).

L'organe est appele en sous-process pour isoler le test de l'etat du working
tree : les fixtures vivent dans un repertoire temporaire et un depot jetable.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "ci" / "check_path_length.py"


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False,  # le verdict se lit dans returncode
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} a echoue : {proc.stderr}")
    return proc.stdout


def _make_repo(root: Path) -> Path:
    repo = root / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    (repo / "base.txt").write_text("base\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    return repo


def _run(repo: Path, *extra: str) -> tuple[int, str, str]:
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--base", "HEAD~1", "--head", "HEAD",
         *extra],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=False,  # le verdict se lit dans returncode
        cwd=str(repo),
    )
    return proc.returncode, proc.stdout, proc.stderr


class CheckPathLength(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.repo = _make_repo(self.root)

    def tearDown(self) -> None:
        self._tmp.cleanup()

    def test_chemin_trop_long_ajoute_est_rouge(self) -> None:
        """Le cas fondateur : un chemin ajoute au-dessus de la borne est rouge."""
        long_path = "d/" + "x" * 200 + ".md"
        target = self.repo / long_path
        target.parent.mkdir(parents=True)
        target.write_text("x\n", encoding="utf-8")
        _git(self.repo, "add", "-A")
        _git(self.repo, "commit", "-q", "-m", "ajout long")

        rc, out, err = _run(self.repo, "--json")
        payload = json.loads(out)
        self.assertEqual(rc, 1, err)
        self.assertEqual(payload["verdict"], "FAIL")
        self.assertEqual(len(payload["overlong"]), 1)
        self.assertEqual(payload["overlong"][0]["path"], long_path)
        self.assertGreater(payload["overlong"][0]["length"], 160)

    def test_modification_d_un_chemin_long_existant_ne_rougit_pas(self) -> None:
        """Le cliquet ne juge que les chemins INTRODUITS."""
        long_path = "d/" + "y" * 200 + ".md"
        target = self.repo / long_path
        target.parent.mkdir(parents=True)
        target.write_text("x\n", encoding="utf-8")
        _git(self.repo, "add", "-A")
        _git(self.repo, "commit", "-q", "-m", "ajout long")
        target.write_text("y\n", encoding="utf-8")
        _git(self.repo, "commit", "-q", "-am", "modification")

        rc, out, err = _run(self.repo, "--json")
        payload = json.loads(out)
        self.assertEqual(rc, 0, err)
        self.assertEqual(payload["verdict"], "OK")
        self.assertEqual(payload["overlong"], [])

    def test_chemin_de_longueur_exactement_egale_a_la_borne_passe(self) -> None:
        """La borne est inclusive : 160 passe, 161 rougit."""
        name = "z" * 157 + ".md"          # 157 + 3 = 160
        self.assertEqual(len(name), 160)
        target = self.repo / name
        target.write_text("x\n", encoding="utf-8")
        _git(self.repo, "add", "-A")
        _git(self.repo, "commit", "-q", "-m", "ajout pile")

        rc, out, err = _run(self.repo, "--json")
        self.assertEqual(rc, 0, err)
        self.assertEqual(json.loads(out)["overlong"], [])

    def test_base_introuvable_rend_un_verdict_inconnu(self) -> None:
        """Une base illisible n'est jamais un quitus : exit 2, pas exit 0."""
        proc = subprocess.run(
            [sys.executable, str(SCRIPT), "--base", "ref-inexistante",
             "--head", "HEAD"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=False,  # le verdict se lit dans returncode
            cwd=str(self.repo),
        )
        self.assertEqual(proc.returncode, 2)
        self.assertIn("INCIDENT", proc.stderr)

    def test_auto_controle_du_scripte(self) -> None:
        """Le `--self` de l'organe passe."""
        proc = subprocess.run(
            [sys.executable, str(SCRIPT), "--self"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=False,  # le verdict se lit dans returncode
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("OK", proc.stdout)


if __name__ == "__main__":
    unittest.main()
