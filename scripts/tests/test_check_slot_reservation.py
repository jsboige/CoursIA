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
        """Une cible qui ne porte NI serie NI index doit se dire telle.

        Le nom employe ici ne porte volontairement aucun chiffre de tete :
        depuis #21959, `MGS-27` (prefixe de serie alphabetique) PORTE une
        position, et l'echantillon qui portait ce nom verifiait le cas
        inverse -- il ne verifiait plus rien.
        """
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, ["MyIA.AI.Notebooks/Sudoku/MGS-26-Equilibrium.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", "MyIA.AI.Notebooks/Sudoku/notes-Sans-Position.ipynb")
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


class TestOpenPrsUnavailableInOnlineModeIsFailClosed(unittest.TestCase):
    """#20913-fixes -- fail-closed en mode en ligne quand `gh pr list` echoue.

    En mode en ligne, la source `open_prs` est lue par `subprocess` (vs `--offline`
    qui rend la source indisponible par construction). Si `gh` echoue (reseau, auth,
    jeton expire), l'organe NE doit PAS continuer son verdict sur sources
    residuelles (base + revision + declared) en rendant rc=0 ou rc=1 : la
    detection de collision cross-PR est incomplete et une collision pourrait
    passer au merge exactement comme avant #20774 dans ce scenario. On rend
    rc=2 pour ramener le consommateur (merge_ready etape 5bis.bis) en mode
    `slot-collision-unreadable`.
    """

    def _run_online_with_failing_gh(self, repo: Path, base: str) -> subprocess.CompletedProcess:
        """Run l'organe SANS `--offline`, avec `gh` qui echoue (rc != 0)."""
        from unittest import mock
        from scripts.notebook_tools import check_slot_reservation as csr
        import subprocess as _real_sp

        # Capture la reference reelle de `subprocess.run` AVANT le patch.
        # `csr.subprocess` est le meme module que `_real_sp` (singleton), donc
        # appeler `_real_sp.run` apres `mock.patch.object(csr.subprocess, "run", ...)`
        # passe par le mock -- il faut capturer la fonction elle-meme.
        _real_run = _real_sp.run

        def fake_gh(argv, **kwargs):
            # Toute commande `gh` en mode revision echoue (rc=1) avec stderr
            # explicite -- simule un crash reseau ou un auth refuse.
            if argv and argv[0] == "gh" and "pr" in argv[:3]:
                return _real_sp.CompletedProcess(
                    argv, returncode=1,
                    stdout="", stderr="gh: GraphQL: Could not resolve to a Repository",
                )
            # Delegue tout autre subprocess (git, etc.) au vrai `run`,
            # qui est la fonction ORIGINALE capturee avant le patch.
            return _real_run(argv, **kwargs)

        with mock.patch.object(csr.subprocess, "run", fake_gh):
            args = [sys.executable, str(_SCRIPT), "--base", base, "--head", "HEAD",
                    "--reservations", str(repo / "no_such_reservations.json"),
                    "--json"]
            return _real_run(args, cwd=str(repo), capture_output=True, text=True,
                             encoding="utf-8", errors="replace")

    def test_online_mode_with_failing_gh_returns_rc2_when_targets_exist(self):
        """Mode en ligne + au moins un carnet vise + `gh` en echec => rc=2."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _commit(repo)

            r = self._run_online_with_failing_gh(repo, base)
            self.assertEqual(r.returncode, 2,
                             "mode en ligne + targets + gh en echec => fail-closed rc=2\n"
                             + r.stdout + r.stderr)
            doc = json.loads(r.stdout)
            self.assertTrue(doc.get("unavailable_open_prs"),
                            "le payload doit signaler unavailable_open_prs=True\n"
                            + r.stdout)
            self.assertEqual(doc["sources"]["open_prs"]["status"], "unavailable",
                             "le statut de la source open_prs doit etre 'unavailable'")

    def test_online_mode_with_failing_gh_returns_rc0_when_no_targets(self):
        """Mode en ligne + aucun carnet vise + `gh` en echec => rc=0 (rien a verifier).

        Si la PR ne touche aucun carnet, la source `open_prs` n'est pas requise :
        l'organe rend rc=0 avec verdict vide, comme en mode revision sans cible.
        Ce test protege contre une regression qui fail-closed a tort.
        """
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, "README.md")
            _commit(repo)

            r = self._run_online_with_failing_gh(repo, base)
            self.assertEqual(r.returncode, 0,
                             "mode en ligne + SANS targets + gh en echec => rc=0 (rien a verifier)\n"
                             + r.stdout + r.stderr)


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


_REPO_ROOT = _SCRIPT.parent.parent.parent


def _has_history(*shas: str) -> bool:
    """Le clone porte-t-il ces commits ? (les checkouts CI sont souvent superficiels)

    Un temoin d'historique absent se DIT -- `skipTest` -- plutot que de rendre un
    vert qui ne prouve rien : c'est la meme discipline que le garde lui-meme.
    """
    for sha in shas:
        r = subprocess.run(["git", "cat-file", "-e", sha + "^{commit}"],
                           cwd=str(_REPO_ROOT), capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        if r.returncode != 0:
            return False
    return True


class TestAccretionEndToEnd(unittest.TestCase):
    """Les trois constats d'accretion (#19144), de bout en bout par le CLI.

    Le contrat qui porte tout le reste : **advisory**. Aucun constat ne change le
    code retour -- un organe advisory qui rougit est un organe qu'on desactive,
    et c'est exactement ce que #16762 -> #16786 a mis deux iterations a montrer.
    """

    def test_depth_is_reported_while_the_exit_code_stays_zero(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/Search-03-Informed.ipynb",
                                     SERIES + "/Search-03f-Reparer.ipynb"])
            _write(repo, SERIES + "/Search-03g-Neuf.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0,
                             "un constat advisory ne rougit JAMAIS le garde\n"
                             + r.stdout + r.stderr)
            self.assertIn("DEPTH", r.stdout)

    def test_accretion_only_says_nothing_about_a_real_slot_conflict(self):
        """Le check-run dedie ne redit pas le verdict du garde bloquant."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _write(repo, SERIES + "/04-2-Beta.ipynb")
            _commit(repo)

            plain = _run(repo, base)
            self.assertEqual(plain.returncode, 1, plain.stdout + plain.stderr)

            only = _run(repo, base, "--accretion-only")
            self.assertEqual(only.returncode, 0,
                             "le mode advisory ne porte aucun verdict de slot\n"
                             + only.stdout + only.stderr)
            self.assertNotIn("CONFLIT DE SLOT", only.stdout)

    def test_accretion_only_is_honoured_in_json_too(self):
        """Le mode advisory ne porte aucun verdict -- y compris en sortie machine."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/04-1-Previous.ipynb"])
            _write(repo, SERIES + "/04-2-Alpha.ipynb")
            _write(repo, SERIES + "/04-2-Beta.ipynb")
            _commit(repo)

            r = _run(repo, base, "--accretion-only", "--json")
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertEqual(json.loads(r.stdout)["conflicts"], 2,
                             "le conflit reste RAPPELE, il ne fait plus rougir")

    def test_a_declared_pending_table_fires_on_a_readme_only_revision(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [SERIES + "/Tweety-01-Setup-Python.ipynb"])
            _write(repo, SERIES + "/README.md", "# Serie\n")
            _commit(repo)

            table = Path(td) / "res.json"
            table.write_text(json.dumps({"reserved": [
                {"kind": "pending_table", "dir": SERIES, "note": "#16231"}]}),
                encoding="utf-8")
            r = _run(repo, base, reservations=str(table))
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("PENDING_TABLE", r.stdout)


class TestSelfTestTable(unittest.TestCase):
    """La table d'auto-controle est un GATE, pas une commande qu'on pense a lancer."""

    def test_self_test_passes(self):
        r = subprocess.run([sys.executable, str(_SCRIPT), "--self-test"],
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("SUCCES", r.stdout)


# Temoins NOMMES par l'issue #19144, rejoues sur l'historique REEL du depot. Le
# SHA est celui du commit qui AJOUTE le carnet : la base est son parent, donc le
# temoin ne depend pas de l'etat courant de `main` (un `main` qui avance ne peut
# pas lui faire perdre son sens -- seulement un clone superficiel, qui se DIT).
_HISTORY_CASES = [
    ("520539d70f05a824bed946ec46d6ce5ae5aab1ce", "DEPTH",
     "GameTheory-06g-Simulation-Based-Program-Equilibria.ipynb"),
    ("44f7bb55f792e6998bc0db380a5e2734e7fe989a", "NO_BASE",
     "Search-12a-Composer-Regards.ipynb"),
    ("ad17a578365b68eafbda7aa8c374b28af9c1b940", "NO_BASE",
     "Search-13a-Traverser-Murs-Certifies.ipynb"),
]


class TestAccretionOnRealHistory(unittest.TestCase):
    """Les temoins du 04/10, rejoues : positifs nommes, negatifs nommes.

    Un jeu de cas ecrit a la main ne contient que les formes auxquelles on a
    pense ; ces cinq-la viennent du depot, pas de l'imagination du redacteur.
    """

    def _findings(self, sha):
        r = subprocess.run([sys.executable, str(_SCRIPT), "--offline", "--json",
                            "--base", sha + "^", "--head", sha],
                           cwd=str(_REPO_ROOT), capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        self.assertIn(r.returncode, (0, 1), r.stdout + r.stderr)
        return json.loads(r.stdout)["accretion"]

    def test_named_positive_controls(self):
        missing = [s for s, _, _ in _HISTORY_CASES if not _has_history(s)]
        if missing:
            self.skipTest("historique absent (clone superficiel ?) : %s" % missing)
        for sha, kind, name in _HISTORY_CASES:
            kinds = {f["kind"] for f in self._findings(sha) if f["path"].endswith(name)}
            self.assertIn(kind, kinds,
                          "le temoin %s devait sortir %s sur %s" % (sha[:10], kind, name))

    def test_the_csharp_twin_of_an_existing_python_notebook_is_not_an_accretion(self):
        sha = "35695217e99b1b9da9c7d5c265f2f848266dab07"
        if not _has_history(sha):
            self.skipTest("historique absent")
        self.assertEqual(self._findings(sha), [],
                         "un jumeau C# ajoute au slot de son Python n'est pas une accretion (§7)")

    def test_a_clean_reclassification_reports_nothing(self):
        sha = "34f95b718e42c2044770241fdce68b6cd1b0c3ae"
        if not _has_history(sha):
            self.skipTest("historique absent")
        self.assertEqual(self._findings(sha), [],
                         "le reclassement 42 -> 41b (#18986) est propre")


# ---------------------------------------------------------------- series alphabetiques (#21959)

Z3 = "MyIA.AI.Notebooks/SymbolicAI/SMT/Z3-API"
GT = "MyIA.AI.Notebooks/GameTheory"


class TestAlphabeticSeriesSlots(unittest.TestCase):
    """#21959 -- le verdict par PR voit enfin les series a prefixe alphabetique.

    Le chemin de verdict passait par `slot_of(index_key)`, qui ne produit
    d'index que pour un stem COMMENCANT PAR UN CHIFFRE : tout carnet de serie
    alphabetique (`Z3-19`, `GameTheory-04c`, `ICT-48`) sortait `no_slot`, et
    deux PRs qui revendiquaient le meme numero ne se voyaient qu'au conflit de
    merge (#20664 contre #20922, sur `Z3-19`).

    Les controles positifs reprennent les formes nommees dans l'issue ; les
    controles negatifs prouvent que la cle ne confond ni `3D-01`/`3D-02` (que
    `index_key` mettait sous `3d`) ni deux rendus du meme item.
    """

    def test_two_additions_sharing_a_series_number_are_flagged(self):
        """Controle positif de l'issue : `Z3-19` x2 dans la meme revision."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-18-Ancien-Sujet-Python.ipynb"])
            _write(repo, Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb")
            _write(repo, Z3 + "/Z3-19-Optimization-Lexicographic-Python.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1,
                             "deux ajouts du meme numero de serie doivent rougir\n"
                             + r.stdout + r.stderr)
            self.assertEqual(r.stdout.count("duplicate_within_revision"), 2, r.stdout)

    def test_a_series_number_taken_on_base_reddens(self):
        """Controle positif : le numero est deja sur la base, sous un autre titre."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-19-Optimization-Lexicographic-Python.ipynb"])
            _write(repo, Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("taken_on_base", r.stdout)

    def test_a_series_number_reserved_by_an_open_pr_reddens(self):
        """Controle positif : la source `open_prs` voit les series aussi."""
        claims = csr.pr_claims([{"number": 20664, "files": [
            {"path": Z3 + "/Z3-19-Optimization-Lexicographic-Python.ipynb",
             "additions": 4, "deletions": 0}]}])
        self.assertTrue(claims, "la serie alphabetique doit tenir un slot")
        slot = csr._scan_slot(Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb")
        self.assertIn(slot, claims, "les deux notebooks visent le meme slot")

    def test_a_declared_series_reservation_reddens(self):
        """Controle positif de la table DECLAREE sur une serie : une entree qui
        nomme la position d'un carnet de serie doit le reserver.

        C'est le mode de panne mesure par la revue du 2026-10-22 : la cle de la
        table etait comparée par egalite stricte a la position analysee, dont
        la casse est celle du nom de fichier. Une entree qui ecrit la position
        autrement ne declarait RIEN, sans erreur -- une table de slots declares
        qui ne declare rien en silence.
        """
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-18-Ancien-Sujet-Python.ipynb"])
            _commit(repo, "vide")
            cfg = repo / "reservations.test.json"
            cfg.write_text(json.dumps({"reserved": [
                {"dir": Z3, "index": "Z3-19", "holder": "lane X",
                 "note": "serie complete", "since": "2026-09-11"}]}), encoding="utf-8")

            r = _run(repo, base, "--target", Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb",
                     reservations=str(cfg))
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("declared_reserved", r.stdout)
            self.assertIn("lane X", r.stdout)

    def test_a_declared_series_reservation_ignores_the_case(self):
        """Le meme slot, ecrit autrement : la reservation tient quand meme.

        C'est la decision explicite (comparaison sans egard a la casse, des
        deux cotes) -- l'autre voie, une convention documentee, laissait le
        mode de panne muet intact.
        """
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-18-Ancien-Sujet-Python.ipynb"])
            _commit(repo, "vide")
            cfg = repo / "reservations.test.json"
            cfg.write_text(json.dumps({"reserved": [
                {"dir": Z3.lower(), "index": "z3-19", "holder": "lane X",
                 "note": "serie complete", "since": "2026-09-11"}]}), encoding="utf-8")

            r = _run(repo, base, "--target", Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb",
                     reservations=str(cfg))
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("declared_reserved", r.stdout)
            self.assertIn("lane X", r.stdout)

    def test_an_accretion_letter_is_part_of_the_series_slot(self):
        """`GameTheory-04c` contre `GameTheory-04c` : meme position, sujets
        differents -- c'est le second controle positif de l'issue."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [GT + "/GameTheory-04b-Twins-Python.ipynb"])
            _write(repo, GT + "/GameTheory-04c-NashExistence-Python.ipynb")
            _write(repo, GT + "/GameTheory-04c-NashEquilibrium-Python.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertEqual(r.stdout.count("duplicate_within_revision"), 2, r.stdout)

    def test_two_different_series_numbers_stay_green(self):
        """Controle negatif : `Z3-19` et `Z3-20` sont deux positions."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-19-Optimization-Lexicographic-Python.ipynb"])
            _write(repo, Z3 + "/Z3-20-Autre-Sujet-Python.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("free", r.stdout)

    def test_digit_leading_numbers_do_not_collide(self):
        """Controle negatif de l'issue : `3D-01` et `3D-02` sont DEUX
        positions -- `index_key` les confondait sous `3d`."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, ["MyIA.AI.Notebooks/GenAI/3D/3D-01-NeRF-From-Scratch.ipynb"])
            _write(repo, "MyIA.AI.Notebooks/GenAI/3D/3D-02-NeRF-Critic.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("free", r.stdout)

    def test_language_siblings_in_a_series_stay_green(self):
        """Controle negatif de l'issue : deux rendus du meme item restent non
        concurrents (le suffixe de langue seul differe)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [GT + "/GameTheory-04c-NashExistence-Python.ipynb"])
            _write(repo, GT + "/GameTheory-04c-NashExistence-CSharp.ipynb")
            _commit(repo)

            r = _run(repo, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("exempt_sibling", r.stdout)

    def test_a_series_target_is_no_longer_slotless(self):
        """La non-regression directe du defaut : la cible porte une position."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo, [Z3 + "/Z3-18-Ancien-Sujet-Python.ipynb"])
            _commit(repo, "vide")

            r = _run(repo, base, "--target", Z3 + "/Z3-19-Machine-de-Goedel-Python.ipynb")
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertNotIn("sans slot", r.stdout)
            self.assertIn("Z3-19", r.stdout)

    def test_slot_of_keeps_its_historical_behaviour(self):
        """`slot_of` reste l'API historique : une serie alphabetique n'y porte
        AUCUN index. C'est ce que les autres gardes qui l'importent attendent."""
        self.assertIsNone(csr.slot_of("MGS-26-Equilibrium.ipynb"))
        self.assertEqual(csr.slot_of("04-2-Alpha.ipynb"), ("", "4.2"))


# ---------------------------------------------------------------- scan-main (#20774)

class ScanMainCollisionTests(unittest.TestCase):
    """Le balayage main detecte les numeros occupes par 2+ sujets differents
    dans une meme serie, en excluant les jumeaux (suffixe ou noyau en milieu
    de nom) et les sorties papermill. Les controles positifs utilisent des
    collisions documentees ; les controles negatifs verifient que la cle
    de slot distingue ce que `index_key` confond (3D-01 / 3D-02) et que
    `_same_item_scan` apparie les formes que `same_item` rate (compose
    `-Python_en`, kernel en milieu de nom).
    """

    def test_scan_slot_distinguishes_digit_leading_numbers(self):
        # 3D-01 et 3D-02 sont DEUX positions distinctes ; `index_key` les
        # confond sous `3d`, le scan les separe.
        a = "MyIA.AI.Notebooks/GenAI/3D/3D-01-NeRF-From-Scratch.ipynb"
        b = "MyIA.AI.Notebooks/GenAI/3D/3D-02-NeRF-Critic.ipynb"
        self.assertNotEqual(csr._scan_slot(a), csr._scan_slot(b),
                            "3D-01 et 3D-02 ne peuvent pas bucketer ensemble")

    def test_scan_slot_handles_series_leading_files(self):
        # ICT-48 et ICT-49 sont deux positions distinctes ; `index_key`
        # rendait None sur les deux avant le fix.
        a = "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-48-Onset9B-Aggregate-Python.ipynb"
        b = "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-49-Other-Topic.ipynb"
        sa = csr._scan_slot(a)
        sb = csr._scan_slot(b)
        self.assertIsNotNone(sa, "ICT-48 doit produire un slot")
        self.assertIsNotNone(sb, "ICT-49 doit produire un slot")
        self.assertNotEqual(sa, sb)

    def test_scan_slot_collapses_accented_letter(self):
        # SL-12b (avec lettre d'accretion 'b') produit un slot qui inclut
        # la lettre : SL-12b, pas SL-12.
        a = "MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-12b-PavlovDLS-Reproduction.ipynb"
        slot = csr._scan_slot(a)
        self.assertEqual(slot, ("MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning", "SL-12b"))

    def test_same_item_scan_matches_compound_lang_suffix(self):
        # FT-01-...-Python et FT-01-...-Python_en sont le MEME item ;
        # `same_item` (canon) rate le compose, `_same_item_scan` le couvre.
        a = "MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning-Python.ipynb"
        b = "MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning-Python_en.ipynb"
        self.assertFalse(csr.same_item(a, b),
                         "le canon `same_item` rate le compose `-Python_en` (limitation connue)")
        self.assertTrue(csr._same_item_scan(a, b),
                        "_same_item_scan doit reconnaitre le compose")

    def test_same_item_scan_matches_kernel_in_middle(self):
        # SW-10-CSharp-RDFStar et SW-10-Python-RDFStar : le kernel
        # (`CSharp` / `Python`) est en milieu de nom, pas en suffixe.
        a = "MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-10-CSharp-RDFStar.ipynb"
        b = "MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-10-Python-RDFStar.ipynb"
        self.assertTrue(csr._same_item_scan(a, b),
                        "le kernel en milieu de nom doit etre neutralise")

    def test_same_item_scan_does_not_match_different_topics(self):
        # App-14-ConnectFour-Adversarial et App-14-ConnectFour-CSharp :
        # `Adversarial` n'est PAS un token noyau, le strip ne le touche
        # pas, et la collision reste un vrai conflit de sujet.
        a = "MyIA.AI.Notebooks/Search/Applications/Search/App-14-ConnectFour-Adversarial.ipynb"
        b = "MyIA.AI.Notebooks/Search/Applications/Search/App-14-ConnectFour-CSharp.ipynb"
        self.assertFalse(csr._same_item_scan(a, b),
                         "deux sujets differents ne sont PAS un jumeau")

    def test_scan_main_finds_known_collision_ict48(self):
        # ICT-48 est la collision documentee de la tranche 1. Si le
        # balayage la manque, la garde regresse.
        try:
            collisions = csr.scan_main_collisions("origin/main")
        except RuntimeError:
            self.skipTest("origin/main indisponible")
        ict48 = [c for c in collisions
                 if c["slot"] == "ICT-48"
                 and c["dir"].endswith("IIT/ICT-Series")]
        self.assertEqual(len(ict48), 1, "ICT-48 doit remonter comme collision documentee")
        self.assertGreaterEqual(len(ict48[0]["paths"]), 2)

    def test_scan_main_finds_known_collision_sl12b(self):
        # SL-12b : PavlovDLS-Reproduction vs SpectralLogicSynthesis.
        try:
            collisions = csr.scan_main_collisions("origin/main")
        except RuntimeError:
            self.skipTest("origin/main indisponible")
        sl12b = [c for c in collisions
                 if c["slot"] == "SL-12b"
                 and c["dir"].endswith("SymbolicAI/SymbolicLearning")]
        self.assertEqual(len(sl12b), 1, "SL-12b doit remonter comme collision documentee")

    def test_scan_main_filters_papermill_outputs(self):
        # Aucune collision ne peut etre uniquement des sorties papermill
        # (`-output.ipynb` ou `_output.ipynb`) : le filtre du scan les
        # elimine avant le bucket.
        try:
            collisions = csr.scan_main_collisions("origin/main")
        except RuntimeError:
            self.skipTest("origin/main indisponible")
        for c in collisions:
            output_only = all(
                p.lower().endswith("-output.ipynb") or p.lower().endswith("_output.ipynb")
                for p in c["paths"]
            )
            self.assertFalse(output_only,
                             "collision %s ne peut pas etre uniquement des sorties papermill"
                             % c["slot"])

    def test_scan_main_returns_json_serializable(self):
        # La sortie machine passe par `json.dumps` ; les structures
        # doivent etre serialisables sans aide.
        try:
            collisions = csr.scan_main_collisions("origin/main")
        except RuntimeError:
            self.skipTest("origin/main indisponible")
        payload = {"ref": "origin/main", "count": len(collisions), "collisions": collisions}
        encoded = json.dumps(payload, ensure_ascii=False)
        decoded = json.loads(encoded)
        self.assertEqual(decoded["count"], len(collisions))
        for c in decoded["collisions"]:
            self.assertIn("kind", c)
            self.assertIn("dir", c)
            self.assertIn("slot", c)
            self.assertIn("paths", c)
            self.assertIn("ref", c)


if __name__ == "__main__":
    unittest.main()
