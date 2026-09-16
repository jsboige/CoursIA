#!/usr/bin/env python3
"""Tests du garde de collision d'index, angle mort des renames (#15489).

Le defaut corrige est un angle mort de la VUE `git diff` : un `git mv` vers un
index deja tenu sort en `R100` et `--diff-filter=A` l'ecarte. Le tester sur une
liste d'ajouts fabriquee ne prouverait rien -- la liste fabriquee n'a pas de
renames, c'est-a-dire pas de defaut. Les deux controles de l'acceptance sont donc
joues contre un **vrai depot git temporaire**, et le positif commence par
verifier que Git voit effectivement un rename : sans cette assertion, le test
passerait au vert meme sur un garde aveugle, et ne controlerait rien.

    positif : git mv <fichier> -> index deja pris  => le garde rougit
    negatif : git mv <fichier> -> index libre      => le garde reste vert
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "notebook_tools" / \
    "check_duplicate_notebook_index.py"


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git"] + list(args), cwd=str(repo), capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise AssertionError("git %s -> %s" % (" ".join(args), r.stderr.strip()[:200]))
    return r.stdout


def _write(repo: Path, rel: str, body: str = "{}\n") -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")


def _init_repo(repo: Path) -> str:
    """Depot initial avec deux notebooks d'index distincts. Rend le sha de base."""
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    _git(repo, "config", "diff.renames", "true")
    _write(repo, "a/03-DL/3.1-Retropropagation.ipynb")
    _write(repo, "a/03-DL/5.2-Annexe.ipynb", '{"cells": []}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    return _git(repo, "rev-parse", "HEAD").strip()


def _run_guard(repo: Path, base: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(_SCRIPT), "--base", base, "--head", "HEAD"],
        cwd=str(repo), capture_output=True, text=True, encoding="utf-8",
        errors="replace")


class TestRenameAwareness(unittest.TestCase):
    """Acceptance #15489 : un rename ne doit plus etre un trou dans le garde."""

    def test_positive_control_rename_onto_taken_index_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            _git(repo, "mv", "a/03-DL/5.2-Annexe.ipynb",
                 "a/03-DL/3.1-Autre.ipynb")
            _git(repo, "commit", "-qm", "rename onto taken index")

            # Le controle n'a de valeur que si Git classe bien ce commit comme un
            # rename : c'est ce classement qui rendait le defaut invisible.
            status = _git(repo, "diff", "--name-status", base, "HEAD")
            self.assertIn("R", status,
                          "Git ne classe pas ce commit en rename : le controle "
                          "positif ne reproduit plus la condition du defaut.")

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 1,
                             "un rename vers un index deja tenu doit rougir\n"
                             "stdout:\n%s\nstderr:\n%s" % (r.stdout, r.stderr))
            self.assertIn("3.1-Autre.ipynb", r.stdout)
            self.assertIn("COLLISION", r.stdout)

    def test_negative_control_rename_onto_free_index_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            _git(repo, "mv", "a/03-DL/5.2-Annexe.ipynb",
                 "a/03-DL/5.3-Annexe.ipynb")
            _git(repo, "commit", "-qm", "rename onto free index")

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 0,
                             "un rename vers un index libre doit rester vert\n"
                             "stdout:\n%s\nstderr:\n%s" % (r.stdout, r.stderr))
            self.assertIn("OK", r.stdout)

    def test_plain_addition_onto_taken_index_reddens(self):
        """Le chemin historique (ajout pur) ne doit pas regresser."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            _write(repo, "a/03-DL/3.1-Retropropagation-From-Scratch.ipynb")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "addition onto taken index")

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("COLLISION", r.stdout)

    def test_language_sibling_rename_stays_green(self):
        """Un rename vers le rendu de langue du meme item reste legitime."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            _git(repo, "mv", "a/03-DL/5.2-Annexe.ipynb",
                 "a/03-DL/3.1-Retropropagation-Csharp.ipynb")
            _git(repo, "commit", "-qm", "rename to language sibling")

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class TestPerimeterIsStated(unittest.TestCase):
    """Acceptance #16040 : la portee du LECTEUR est imprimee avant le verdict.

    Le defaut ferme n'est pas un faux vert mais un vert MAL LU : le garde ne
    compare que les noms dont l'index ouvre le nom, or la convention majoritaire
    du depot est `<Prefixe>-<num>`. Sans denombrement, « OK » se lisait « aucune
    collision dans cette serie » au lieu de « aucune collision dans mon
    perimetre ». Les deux tests ci-dessous portent sur le COMPTE (il doit tirer,
    pas etre decoratif) et sur sa PRESENCE quand il n'y a rien a verifier.
    """

    def test_perimeter_line_printed_even_with_no_addition(self):
        """Le cas ou l'on croit n'avoir rien a verifier est celui ou la portee
        manque le plus : la ligne sort malgre `added == 0`."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("aucun notebook ajoute", r.stdout)
            self.assertIn("PERIMETRE du lecteur d'index", r.stdout)
            # Les deux notebooks de la fixture portent un index ouvrant : le
            # compte doit etre MESURE sur la base, pas ecrit en dur.
            self.assertIn("2/2 notebooks lisibles", r.stdout)
            self.assertIn("0 a prefixe de serie", r.stdout)

    def test_perimeter_counts_the_majority_convention_out_of_scope(self):
        """La convention majoritaire (`<Prefixe>-<num>`, lue par `parse_name`
        mais rendue `None` par `index_key`) doit tomber HORS portee -- c'est
        exactement l'angle mort que l'issue mesure."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _git(repo, "init", "-q")
            _git(repo, "config", "user.email", "test@example.invalid")
            _git(repo, "config", "user.name", "test")
            _write(repo, "g/GameTheory-04c-NashExistence.ipynb")
            _write(repo, "g/GameTheory-04d-Pareto.ipynb")
            _write(repo, "g/README-notes.ipynb")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "base")
            base = _git(repo, "rev-parse", "HEAD").strip()

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("0/3 notebooks lisibles", r.stdout)
            self.assertIn("2 a prefixe de serie", r.stdout)

            # Un ajout reel a index LIBRE : la comparaison a effectivement lieu
            # et ne trouve rien -- c'est le seul vert qui pouvait se mal lire
            # comme « aucune collision dans cette serie ». Il doit porter sa
            # borne, la ou le vert « rien a verifier » (added == 0) n'a pas
            # besoin de la porter puisqu'il ne dit deja rien d'autre.
            _write(repo, "g/GameTheory-05a-Nouveau.ipynb")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "addition onto free index")

            r = _run_guard(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("aucun index de serie en conflit", r.stdout)
            self.assertIn("DANS LE PERIMETRE", r.stdout)


if __name__ == "__main__":
    unittest.main()
