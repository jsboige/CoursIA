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
from unittest import mock

_SCRIPT = (Path(__file__).resolve().parent.parent / "notebook_tools"
           / "check_slot_reservation.py")

# Le module est importe pour eprouver ses fonctions pures (`pr_claims`,
# `ambiguous_pr_numbers`) et son lecteur `gh`, que le harnais `--offline`
# ci-dessus ne peut pas atteindre.
sys.path.insert(0, str(_SCRIPT.parent))
import check_slot_reservation as csr  # noqa: E402

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
            # La lecture de `status` est une source a part, et elle se dit
            # indisponible elle aussi : une source muette n'est pas une source
            # absente (cf #15734).
            self.assertEqual(doc["sources"]["open_prs_removed"]["status"],
                             "unavailable")
            self.assertEqual(doc["sources"]["base"]["notebooks"], 1)


class TestOpenPrSourceDiscriminatesOnStatus(unittest.TestCase):
    """#15734 -- « une entree a `additions == 0` » ne veut pas dire « suppression ».

    Mesure du 2026-09-12, 54 PRs ouvertes / 101 entrees `.ipynb`, les deux API
    croisees (0 desaccord de compteur) : `modified` 70, `renamed` 27, `added` 4,
    `removed` **0**. La source n'avait donc jamais vu la seule chose que son
    filtre `additions > 0` pretendait ecarter.

    Severite honnete : **latente, nulle sur ce pool**. La seule entree vivante a
    `additions == 0` (#15729) porte un nom sans index, que `slot_of` ecartait
    deja -- l'ancien filtre et le nouveau rendent le meme verdict sur elle. Ce
    qui est faux est la REGLE, et la classe qu'elle rouvre est celle d'un
    `git mv` pur (`(0, 0)`) sur un `NN-N-Nom.ipynb` indexe, c'est-a-dire le
    premier commit d'une tranche de renumeration.

    La charge `gh pr list --json files` ne permet PAS de trancher -- c'est
    exactement pourquoi `removed` est un parametre, resolu par `status`
    ailleurs, et pourquoi son absence veut dire « reserver ».
    """

    SLOT = SERIES + "/04-2-Alpha.ipynb"

    def _claims(self, prs, removed):
        return csr.pr_claims(prs, removed).get(csr.slot_of(self.SLOT), [])

    def test_modification_that_only_deletes_lines_holds_the_slot(self):
        """La forme vivante dans le pool : #15729, `(0, 12)`, `status=modified`.

        Le nom de ce notebook ne porte pas d'index, donc l'impact du defaut est
        latent -- c'est la regle qui est fautive, et elle l'est pour tout
        `NN-N-Nom.ipynb` (cf docstring du module)."""
        prs = [{"number": 15729, "files": [
            {"path": self.SLOT, "additions": 0, "deletions": 12}]}]
        self.assertEqual(len(self._claims(prs, {15729: set()})), 1,
                         "retirer 12 lignes d'un notebook, c'est l'EDITER, pas "
                         "le supprimer : le slot reste tenu")

    def test_byte_identical_rename_holds_the_slot(self):
        """Le cas nomme par #15734 : `(0, 0)`. Aucune instance vivante, mais a
        couvert par la meme regle -- c'est la forme d'un `git mv` pur."""
        prs = [{"number": 1, "files": [
            {"path": self.SLOT, "additions": 0, "deletions": 0}]}]
        self.assertEqual(len(self._claims(prs, {1: set()})), 1)

    def test_unresolved_status_reserves_rather_than_releases(self):
        """Sens d'echec : cet organe est un preflight, sous-reserver en silence
        est son seul mode de panne non rattrapable."""
        prs = [{"number": 2, "files": [
            {"path": self.SLOT, "additions": 0, "deletions": 12}]}]
        self.assertEqual(len(self._claims(prs, None)), 1)
        self.assertEqual(len(self._claims(prs, {})), 1)
        self.assertEqual(len(self._claims(prs, {2: set()})), 1)

    def test_real_removal_releases(self):
        """Le seul cas ou le slot est REELLEMENT libere : `status=removed`."""
        prs = [{"number": 3, "files": [
            {"path": self.SLOT, "additions": 0, "deletions": 12}]}]
        self.assertEqual(self._claims(prs, {3: {self.SLOT}}), [])

    def test_written_entries_are_untouched_by_the_change(self):
        """Non-regression : les 100/101 entrees a `additions > 0` reservent
        exactement comme avant, `removed` vide ou non."""
        prs = [{"number": 4, "files": [
            {"path": self.SLOT, "additions": 8, "deletions": 2}]}]
        self.assertEqual(len(self._claims(prs, {4: set()})), 1)
        self.assertEqual(len(self._claims(prs, {})), 1)

    def test_ambiguous_set_is_exactly_the_zero_addition_notebooks(self):
        prs = [
            {"number": 1, "files": [{"path": self.SLOT, "additions": 0, "deletions": 1}]},
            {"number": 2, "files": [{"path": self.SLOT, "additions": 4, "deletions": 0}]},
            {"number": 3, "files": [{"path": "docs/x.md", "additions": 0, "deletions": 4}]},
            {"number": 4, "files": [{"path": self.SLOT, "additions": 0, "deletions": 4},
                                    {"path": self.SLOT, "additions": 2, "deletions": 0}]},
        ]
        self.assertEqual(csr.ambiguous_pr_numbers(prs), [1, 4],
                         "seules les PRs a entree .ipynb `additions == 0` exigent "
                         "une lecture de `status` ; un .md n'en est pas une, et "
                         "une PR ne compte qu'une fois")


class TestRemovalReaderContract(unittest.TestCase):
    """Le contrat du LECTEUR de `status`, epingle.

    Lecon de #15759 : un test qui devine la forme du producteur, ou qui la lui
    fournit a la main, passe vert par construction. Ici on epingle donc les
    arguments `gh` reellement passes ET le sens d'echec -- pas seulement la
    fonction de parsing.
    """

    def _patched(self, stdout, returncode=0):
        seen = {}

        class _Result:
            def __init__(self):
                self.stdout = stdout
                self.stderr = "boom" if returncode else ""
                self.returncode = returncode

        def fake(argv, **kwargs):
            seen["argv"] = list(argv)
            return _Result()

        status: dict = {}
        with mock.patch.object(csr.subprocess, "run", fake):
            removed = csr.load_removed_paths([15729], None, status)
        return removed, status, seen

    def test_reader_asks_the_files_endpoint_for_status_and_paginates(self):
        removed, _status, seen = self._patched("")
        argv = seen["argv"]
        joined = " ".join(argv)
        self.assertEqual(argv[0], "gh")
        self.assertEqual(argv[1], "api")
        self.assertIn("pulls/15729/files", argv[2])
        self.assertIn("--paginate", argv,
                      "un PR a plus de 100 fichiers doit rendre toutes ses pages")
        self.assertIn(".status", joined,
                      "le discriminant est `status` ; le lire est tout l'objet "
                      "de cette lecture")

    def test_reader_uses_the_repo_placeholder_when_no_repo_is_imposed(self):
        _removed, _status, seen = self._patched("")
        self.assertIn("{owner}/{repo}", seen["argv"][2],
                      "sans --repo explicite, `gh` doit resoudre le depot courant "
                      "comme le fait deja la source PRs")

    def test_only_removed_rows_are_collected(self):
        out = ("MyIA.AI.Notebooks/GenAI/Audio/04-1-Gone.ipynb\tremoved\n"
               "MyIA.AI.Notebooks/GenAI/Audio/04-2-Edited.ipynb\tmodified\n")
        removed, status, _seen = self._patched(out)
        self.assertEqual(removed, {15729: {
            "MyIA.AI.Notebooks/GenAI/Audio/04-1-Gone.ipynb"}})
        self.assertEqual(status["open_prs_removed"]["status"], "ok")
        self.assertEqual(status["open_prs_removed"]["removed"], 1)

    def test_a_failed_read_keeps_the_slots_reserved_and_says_so(self):
        removed, status, _seen = self._patched("", returncode=1)
        self.assertEqual(removed, {},
                         "aucune PR dans la carte => ses slots restent RESERVES")
        self.assertEqual(status["open_prs_removed"]["status"], "partial")
        self.assertEqual(status["open_prs_removed"]["failed"], [15729])

    def test_no_ambiguous_pr_costs_no_call(self):
        called = []

        def fake(argv, **kwargs):
            called.append(argv)
            raise AssertionError("aucun appel `gh` ne doit partir sans PR ambigue")

        status: dict = {}
        with mock.patch.object(csr.subprocess, "run", fake):
            removed = csr.load_removed_paths([], None, status)
        self.assertEqual(removed, {})
        self.assertEqual(called, [])
        self.assertEqual(status["open_prs_removed"]["status"], "not_needed")


if __name__ == "__main__":
    unittest.main()
