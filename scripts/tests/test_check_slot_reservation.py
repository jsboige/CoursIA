#!/usr/bin/env python3
"""Tests du preflight de reservation de slot (#15489, defaut 4).

Le defaut que cette tranche ferme a ete **mesure par execution**, pas lu : la
fonction `collisions(added, base_files)` de l'organe frere compare les ajouts a
la base, jamais les ajouts ENTRE EUX, donc deux notebooks neufs au meme index
dans une meme revision sortent a zero hit. Le premier test ci-dessous est la
non-regression de cette mesure : si quelqu'un re-branche l'organe sur la seule
comparaison a la base, il rougit.

Trois pieges sont tendus, et chaque classe de test en couvre un :

1. **Crier a tort.** Les negatifs portent le poids : paires de langue
   (`-Csharp`, `_en`), series a deux niveaux (`04-1` contre `04-2`), meme index
   dans un autre repertoire, lettre d'accretion (`2.8b` contre `2.8c`). Un
   organe qui signale ces cas-la est un organe qu'on desactive.

2. **Se taire a tort.** Chaque test assert un ETAT nomme et un code retour, pas
   seulement « pas d'erreur ». Le denombrement des sources est verifie imprime
   meme quand la reponse est zero, et une source indisponible doit se dire
   indisponible.

3. **Diverger en silence de l'organe frere.** Ce preflight-ci ne compte pas
   comme occupant un fichier que la revision examinee libere -- un retitle dans
   le meme slot n'est pas un conflit, l'organe d'index le signale pourtant
   (mesure : 1 hit). Le test exige d'abord que Git classe bien le commit en
   rename, faute de quoi il ne reproduirait plus la condition et passerait au
   vert a vide.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_SCRIPT = (Path(__file__).resolve().parent.parent / "notebook_tools"
           / "check_slot_reservation.py")

SERIES = "MyIA.AI.Notebooks/GenAI/Audio"


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git"] + list(args), cwd=str(repo), capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise AssertionError("git %s -> %s"
                             % (" ".join(args), r.stderr.strip()[:200]))
    return r.stdout


def _notebook() -> str:
    return json.dumps({"cells": [], "metadata": {},
                       "nbformat": 4, "nbformat_minor": 5}, indent=1) + "\n"


def _write(repo: Path, rel: str, body: str | None = None) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body if body is not None else _notebook(), encoding="utf-8")


def _init_repo(repo: Path, base_files: list[str]) -> str:
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    _git(repo, "config", "diff.renames", "true")
    for rel in base_files:
        _write(repo, rel)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    return _git(repo, "rev-parse", "HEAD").strip()


def _commit(repo: Path, msg: str = "rev") -> None:
    _git(repo, "add", "-A")
    # --allow-empty : plusieurs scenarios eprouvent le mode `--target`, ou la
    # revision examinee n'apporte aucun fichier -- le commit vide fixe la
    # reference sans rien changer a l'arbre.
    _git(repo, "commit", "-qm", msg, "--allow-empty")


def _run(repo: Path, base: str, *extra: str,
         reservations: str | None = None) -> subprocess.CompletedProcess:
    """Toujours --offline : un test ne depend jamais du reseau ni de `gh`.

    La table declaree pointe par defaut sur un chemin INEXISTANT du depot
    temporaire : la source doit se dire absente sans jamais lire la vraie table
    du depot, sinon un test dependrait d'un contenu qui peut changer.
    """
    args = [sys.executable, str(_SCRIPT), "--base", base, "--head", "HEAD",
            "--offline",
            "--reservations", reservations or str(repo / "no_such_reservations.json")
            ] + list(extra)
    return subprocess.run(args, cwd=str(repo), capture_output=True, text=True,
                          encoding="utf-8", errors="replace")


class TestTwoClaimsInOneRevision(unittest.TestCase):
    """Le trou mesure : deux cibles du meme slot dans une meme revision."""

    def test_two_additions_sharing_a_slot_are_flagged(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _write(repo, SERIES + "/04-2-Beta.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1,
                             "deux ajouts du meme slot doivent rougir\n" + r.stdout + r.stderr)
            self.assertEqual(r.stdout.count("duplicate_within_revision"), 2,
                             r.stdout)

    def test_language_siblings_sharing_a_slot_stay_green(self):
        """Deux rendus du meme item, pas deux items : aucun conflit."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _write(repo, SERIES + "/04-2-Alpha-Csharp.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("exempt_sibling", r.stdout)
            self.assertNotIn("duplicate_within_revision", r.stdout)

    def test_single_addition_in_a_free_slot_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("free", r.stdout)


class TestBaseReservation(unittest.TestCase):
    """L'arbre : la source que l'organe frere couvre deja -- verifiee ici pour
    que la scission de responsabilite soit mesurable, pas affirmee."""

    def test_addition_on_a_slot_taken_on_base_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-2-Existing.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("taken_on_base", r.stdout)
            self.assertIn("04-2-Existing.ipynb", r.stdout)

    def test_same_index_in_another_directory_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, ["MyIA.AI.Notebooks/Other/04-2-Existing.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_two_level_series_stays_green(self):
        """`04-1` et `04-2` sont deux items, pas une collision : le faux positif
        que le premier jet de l'organe frere produisait sur 13 notebooks."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Following.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_accretion_letter_variants_stay_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            d = "MyIA.AI.Notebooks/ML/02-ML-Cours"
            base = _init_repo(repo, [d + "/2.8b-Theorie.ipynb"])
            _write(repo, d + "/2.8c-Borne.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class TestReleaseAwareness(unittest.TestCase):
    """La divergence deliberee avec l'organe frere : un slot que la revision
    libere n'est pas un slot tenu par quelqu'un d'autre."""

    def test_rename_within_the_same_slot_is_not_a_conflict(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            old = SERIES + "/04-2-Old-Title.ipynb"
            base = _init_repo(repo, [old])
            _git(repo, "mv", old, SERIES + "/04-2-New-Title.ipynb")
            _commit(repo, "retitle dans le meme slot")

            # Controle de la condition : sans rename detecte, le test ne
            # reproduirait plus le cas et passerait au vert a vide.
            status = _git(repo, "diff", "--name-status", "%s...HEAD" % base).strip()
            self.assertIn("R", status,
                          "Git doit classer ce commit en rename, sinon le test ne "
                          "couvre plus rien : %r" % status)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0,
                             "un retitle dans le meme slot n'est pas une collision\n"
                             + r.stdout + r.stderr)

    def test_rename_into_an_occupied_slot_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            moving = SERIES + "/04-1-Moving.ipynb"
            base = _init_repo(repo, [moving, SERIES + "/04-2-Taken.ipynb"])
            _git(repo, "mv", moving, SERIES + "/04-2-New-Name.ipynb")
            _commit(repo, "rename vers un slot occupe")

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("taken_on_base", r.stdout)


class TestTargetPreflight(unittest.TestCase):
    """Le mode preflight : la question posee AVANT d'editer."""

    def test_free_target_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", SERIES + "/04-3-Nouveau.ipynb")
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("free", r.stdout)

    def test_target_taken_on_base_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-2-Existing.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", SERIES + "/04-2-Alpha.ipynb")
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("taken_on_base", r.stdout)

    def test_target_matching_a_base_file_by_exact_name_is_taken(self):
        """Regression mesuree sur le pool vivant : une cible qui porte exactement
        le nom d'un fichier deja sur la base n'est pas « soi-meme », c'est un
        slot tenu. La confondre avec un rendu alternatif du meme item la faisait
        passer au vert."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            existing = SERIES + "/04-2-Existing.ipynb"
            base = _init_repo(repo, [existing])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", existing)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("taken_on_base", r.stdout)

    def test_same_target_stays_green_when_the_branch_itself_added_it(self):
        """Le pendant du test precedent : en mode cible, une cible que MA propre
        revision porte deja est la mienne, pas celle d'un autre."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            mine = SERIES + "/04-3-Mine.ipynb"
            _write(repo, mine)
            _commit(repo)

            r = _run(repo, base, "--target", mine)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("free", r.stdout)

    def test_target_already_claimed_by_the_branch_itself_reddens(self):
        """« Ma branche prend deja ce slot sous un autre nom » : la source
        revision doit repondre, meme quand la cible n'est pas encore ecrite."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-3-Premier.ipynb")
            _commit(repo)

            r = _run(repo, base, "--target", SERIES + "/04-3-Second.ipynb")
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("duplicate_within_revision", r.stdout)

    def test_declared_reservation_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _commit(repo, "vide")
            cfg = repo / "reservations.test.json"
            cfg.write_text(json.dumps({"reserved": [
                {"dir": SERIES, "index": "4.3", "holder": "lane X",
                 "note": "sommaire de cours", "since": "2026-09-11"}]}), encoding="utf-8")

            r = _run(repo, base, "--target", SERIES + "/04-3-Nouveau.ipynb",
                     reservations=str(cfg))
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("declared_reserved", r.stdout)
            self.assertIn("lane X", r.stdout)


class TestDistinctStates(unittest.TestCase):
    """Rien regarde n'est pas rien trouve, et une source absente doit se dire."""

    def test_slotless_target_is_reported_not_silent(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, ["MyIA.AI.Notebooks/Sudoku/MGS-26-Equilibrium.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", "MyIA.AI.Notebooks/Sudoku/MGS-27-Forensic.ipynb")
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("sans slot", r.stdout)

    def test_every_source_is_counted_even_when_nothing_is_added(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("base      : 1 notebooks", r.stdout)
            self.assertIn("revision  : 0 cible(s) examinee(s)", r.stdout)
            self.assertIn("aucune cible", r.stdout)

    def test_unavailable_source_is_named_never_silent(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base)
            self.assertIn("open_prs  : INDISPONIBLE (--offline)", r.stdout)
            self.assertIn("declared  : absent", r.stdout)

    def test_json_payload_carries_sources_and_states(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _write(repo, SERIES + "/04-2-Beta.ipynb")
            _commit(repo)

            r = _run(repo, base, "--json")
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            doc = json.loads(r.stdout)
            self.assertEqual(doc["conflicts"], 2)
            self.assertEqual(doc["mode"], "revision")
            self.assertEqual(doc["states"]["duplicate_within_revision"], 2)
            self.assertEqual(doc["sources"]["open_prs"]["status"], "unavailable")
            self.assertEqual(doc["sources"]["base"]["notebooks"], 1)


if __name__ == "__main__":
    unittest.main()
