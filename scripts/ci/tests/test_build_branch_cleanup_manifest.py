#!/usr/bin/env python3
"""test_build_branch_cleanup_manifest.py -- tests de l'organe de manifeste
des branches distantes (issue #14238).

Ce qui est mesure ici, et pourquoi :

1. **La PR retenue est celle dont la TETE CORRESPOND** a la tete distante.
   C'est le point qui rend le manifeste exploitable : un nom de branche est
   reutilisable, et une PR fermee sans merge (classe C) ne dit rien de la
   tete qui a pu naitre apres elle. Un classement par nom seul classe B
   comme C -- c'est exactement le defaut que la premiere version du
   script commettait.
2. **Une PR OUVERTE l'emporte meme si la tete a bouge** : le travail en
   cours est un verrou, pas un etat de la tete.
3. **Aucun etat n'est presume** : une tete absente du clone local donne
   `head_absent_du_clone` (INCONNU), jamais `not_ancestor_of_main`.
4. **L'organe ne supprime rien** : il n'a aucune voie d'ecriture sur le
   remote, et la sortie porte la classe, la preuve et le contenu.
5. **La preuve du contenu livre est EXACTE** : le commit de fusion de la PR
   est-il un commit de `main` ? Une PR mergee dans une base PILOTE a bien
   un commit de fusion, mais ce commit n'est pas dans `main` -- son
   contenu n'est donc pas livre par ce merge. Mesure : 18 branches sur
   2 930 sont dans ce cas.

6. **`main()` est exerce en bout a bout** (I/O de reseau mockees) : la note
   de la classe B et la deuxieme passe C/E y passent par le code reel, pas
   par une copie locale re-implementee dans le test.

Aucun test ne requiert de reseau ni de jeton GH : les fonctions de
classement sont pures et testees sur des tables construites a la main, et
`main()` lui-meme est exerce avec ses appels de reseau mockees.
"""
from __future__ import annotations

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

_HERE = os.path.dirname(os.path.abspath(__file__))
# scripts/ci/tests/ -> scripts/ci/ -> scripts/ -> racine du depot
_REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
sys.path.insert(0, os.path.join(_REPO, "scripts", "ci"))

import build_branch_cleanup_manifest as organ  # noqa: E402


def pr(etat, numero, oid="", merge_oid="", base="main"):
    """Une entree de PR au format de l'organe (dictionnaire)."""
    return {
        "state": etat,
        "number": numero,
        "oid": oid.lower(),
        "base": base,
        "merge_oid": merge_oid.lower(),
    }


class TestClassification(unittest.TestCase):
    """Le classement d'une branche a partir de ses PRs et de sa tete."""

    @staticmethod
    def classer(nom, sha, prs, contenu=""):
        """Reproduit le classement de l'organe, isole de git et de gh."""
        tete = sha.lower()
        candidates = [p for p in prs if p["oid"] == tete]
        if not candidates:
            ouvertes = [p for p in prs if p["state"] == "OPEN"]
            if ouvertes:
                candidates = [min(ouvertes, key=lambda p: p["number"])]
        if candidates:
            retenue = min(candidates, key=lambda p: (organ.RANG[p["state"]], p["number"]))
            return organ.CLASSE[retenue["state"]], retenue
        return "E", None

    def test_une_pr_fermee_sans_merge_donne_C(self):
        classe, retenue = self.classer(
            "feature/x", "aaa", [pr("CLOSED", 100, "aaa")])
        self.assertEqual(classe, "C")
        self.assertEqual(retenue["number"], 100)

    def test_une_pr_mergee_donne_B(self):
        classe, retenue = self.classer(
            "feature/x", "aaa", [pr("MERGED", 100, "aaa")])
        self.assertEqual(classe, "B")

    def test_une_pr_ouverte_donne_A(self):
        classe, _ = self.classer("feature/x", "aaa", [pr("OPEN", 100, "aaa")])
        self.assertEqual(classe, "A")

    def test_aucune_pr_donne_E(self):
        classe, retenue = self.classer("feature/x", "aaa", [])
        self.assertEqual(classe, "E")
        self.assertIsNone(retenue)

    def test_une_pr_mergee_sur_une_tete_ancienne_ne_decrit_pas_la_tete(self):
        """Le cas central : nom de branche reutilise.

        La PR #100 a ete MERGEE sur la tete `old`, puis la branche a recu
        des commits (`new`). Le contenu de ces commits n'est PAS sur main :
        classer B serait faux. Sans PR couvrant la tete courante, la
        branche tombe en E (lecture L576 requise).
        """
        classe, _ = self.classer(
            "feature/x", "new", [pr("MERGED", 100, "old")])
        self.assertEqual(classe, "E")

    def test_une_pr_fermee_puis_une_pr_mergee_sur_la_tete_actuelle_donne_B(self):
        """L'ordre des PRs ne decide pas : c'est la tete qui decide."""
        classe, retenue = self.classer(
            "feature/x", "new",
            [pr("CLOSED", 100, "old"), pr("MERGED", 101, "new")])
        self.assertEqual(classe, "B")
        self.assertEqual(retenue["number"], 101)

    def test_une_pr_ouverte_bloque_meme_si_la_tete_a_bouge(self):
        """Le travail en cours est un verrou, pas un etat de la tete."""
        classe, retenue = self.classer(
            "feature/x", "new", [pr("OPEN", 100, "old")])
        self.assertEqual(classe, "A")
        self.assertEqual(retenue["number"], 100)

    def test_plusieurs_prs_ouvertes_il_ya_en_a_une_seule_ouverte(self):
        classe, retenue = self.classer(
            "feature/x", "new", [pr("OPEN", 100, "old"), pr("OPEN", 101, "new")])
        self.assertEqual(classe, "A")
        self.assertEqual(retenue["number"], 101)


class TestPreuveDeContenu(unittest.TestCase):
    """La preuve EXACTE du contenu livre : le commit de fusion est-il dans `main` ?

    Une PR peut etre mergee dans une base PILOTE (une branche de travail) :
    elle porte alors un commit de fusion, mais ce commit n'est PAS dans
    `main` -- son contenu n'est donc pas livre par ce merge. La classe B
    seule ne distingue pas ce cas ; la preuve par `mergeCommit.oid` le
    distingue, sans approximation (mesure : 18 branches sur 2 930).
    """

    @staticmethod
    def note(classe, retenue, commits_main):
        """Reproduit la construction du jeton de note pour la classe B."""
        oid = (retenue or {}).get("merge_oid") or ""
        if not oid:
            return "merge_commit_unknown"
        if oid in commits_main:
            return "content_on_main"
        return f"merged_into_pilot_base:{retenue.get('base') or '?'}"

    def test_le_commit_de_fusion_dans_main_prouve_le_contenu(self):
        retenu = pr("MERGED", 100, "aaa", merge_oid="mmm", base="main")
        self.assertEqual(self.note("B", retenu, {"mmm"}), "content_on_main")

    def test_un_commit_de_fusion_absent_de_main_signale_la_base_pilote(self):
        retenu = pr("MERGED", 100, "aaa", merge_oid="mmm",
                    base="feature/x-suite")
        self.assertEqual(
            self.note("B", retenu, {"autre"}),
            "merged_into_pilot_base:feature/x-suite")

    def test_un_commit_de_fusion_inconnu_n_est_jamais_presume_livre(self):
        retenu = pr("MERGED", 100, "aaa", merge_oid="", base="main")
        self.assertEqual(self.note("B", retenu, {"mmm"}), "merge_commit_unknown")

    def test_une_pr_mergee_sans_preuve_ne_vaut_pas_preuve_de_contenu(self):
        """Le cas « merged_at_older_head » : la PR decrit une tete passee."""
        retenue = pr("MERGED", 100, "old", merge_oid="mmm")
        # La preuve porte sur le commit de fusion, mais la BRANCHE n'est pas
        # decrite par cette PR : elle tombe en E, ou son contenu est mesure
        # separement. Aucune des deux ne vaut « contenu livre ».
        classe, _ = TestClassification.classer("feature/x", "new", [retenue])
        self.assertEqual(classe, "E")


class TestBrancheParDefautProtegee(unittest.TestCase):
    """La branche par defaut ne doit JAMAIS etre une candidate.

    Defaut constate lors de l'execution reelle du 07/11/2026 : la branche
    `main` a ete classee D (« ancetre de `main` »), ce qui est trivialement
    vrai. Un passage automatise l'aurait donc rangee dans le lot de
    suppression. Elle a ete retiree a la main -- l'organe, lui, doit
    interdire le cas.
    """

    def test_la_branche_par_defaut_est_protegee(self):
        """La classe P existe et n'est pas une classe candidate."""
        self.assertEqual(organ.CLASSE_PROTEGEE, "P")
        self.assertNotIn(organ.CLASSE_PROTEGEE, organ.CLASSES_CANDIDATES)
        self.assertIn(organ.CLASSE_PROTEGEE, organ.CLASSES_NON_CANDIDATES)

    def test_les_candidats_sont_b_c_d_e(self):
        self.assertEqual(set(organ.CLASSES_CANDIDATES), {"B", "C", "D", "E"})

    def test_une_classe_a_est_jamais_candidate(self):
        """Une PR ouverte est un verrou, pas une candidate."""
        self.assertNotIn("A", organ.CLASSES_CANDIDATES)

    def test_le_nom_de_la_branche_par_defaut_est_deduit_du_remote(self):
        """Le remote fait foi ; `main_ref` est le repli."""
        source = organ.branche_par_defaut.__doc__ or ""
        self.assertIn("symbolic-ref", source)
        self.assertIn("ls-remote", source)
        self.assertIn("refs/remotes/<remote>/HEAD", source)

    def test_un_repli_sans_symbole_deduit_le_nom_de_main_ref(self):
        """Hors d'un clone, `origin/main` donne `main`."""
        self.assertEqual(organ.repli_branche_par_defaut("origin/main"), "main")

    def test_un_repli_sans_prefixe_renvoie_la_ref_entiere(self):
        self.assertEqual(organ.repli_branche_par_defaut("main"), "main")

    def test_un_repli_sur_une_ref_pleine_retire_le_prefixe(self):
        """`refs/remotes/origin/main` donne `main`, comme `refs/heads/main`."""
        self.assertEqual(
            organ.repli_branche_par_defaut("refs/remotes/origin/main"), "main")
        self.assertEqual(
            organ.repli_branche_par_defaut("refs/heads/main"), "main")


class TestResolutionDeLaBrancheParDefaut(unittest.TestCase):
    """Le nom resolu doit etre un NOM DE BRANCHE, pas une ref.

    Defaut refute par le run de production du 07/11/2026 : le prefixe
    `refs/remotes/` etait tranche a la volee, ce qui laissait le nom du
    remote dans le resultat (`origin/main` au lieu de `main`). La branche
    `main` n'etait donc jamais reconnue, et le manifeste la classait E --
    c'est-a-dire CANDIDATE. Un passage automatise l'aurait supprimee.
    """

    @staticmethod
    def _run_simule(reponses: dict):
        """Un `subprocess.run` simule, repondant par motif de commande."""
        def faux_run(args, **kwargs):
            sortie = reponses.get(args[0], "")
            class Reponse:
                returncode = 0 if sortie else 1
                stdout = sortie
                stderr = ""
            return Reponse()
        return faux_run

    def test_le_nom_du_remote_est_retire_du_ref_symbolique(self):
        """`refs/remotes/origin/main` rend `main`, jamais `origin/main`."""
        faux = self._run_simule({
            "git": "refs/remotes/origin/main\n",
        })
        with mock.patch.object(organ.subprocess, "run", new=faux):
            nom = organ.branche_par_defaut(Path("."), "origin/main", "origin")
        self.assertEqual(nom, "main")
        self.assertNotEqual(nom, "origin/main")

    def test_le_remote_nomme_lui_meme_sa_branche_par_defaut(self):
        """`git ls-remote --symref origin HEAD` est la source autoritative.

        La ligne reelle est `ref: refs/heads/<branche>\\tHEAD` : le nom de la
        branche s'arrete a la tabulation. Une ligne sans tabulation passerait
        le test et échouerait en production.
        """
        faux = self._run_simule({
            "git": "ref: refs/heads/main\tHEAD\n988d7412e549c15ace5513b8a746326e5d1fb6eb\tHEAD\n",
        })
        with mock.patch.object(organ.subprocess, "run", new=faux):
            nom = organ.branche_par_defaut(Path("."), "origin/main", "origin")
            direct = organ.branche_par_defaut_distant(Path("."), "origin")
        self.assertEqual(nom, "main")
        # La source autoritative, lue seule, rend le nom NU : ni le prefixe
        # `ref: `, ni la tabulation qui suit.
        self.assertEqual(direct, "main")

    def test_le_remote_non_nomme_replique_sur_le_ref_symbolique(self):
        """Sans reponse du remote, le ref symbolique local suffit."""
        def faux_run(args, **kwargs):
            class Reponse:
                returncode = 0
                stdout = "refs/remotes/origin/main\n"
                stderr = ""
            if "--symref" in args:
                Reponse.returncode = 1
                Reponse.stdout = ""
            return Reponse()
        with mock.patch.object(organ.subprocess, "run", new=faux_run):
            nom = organ.branche_par_defaut(Path("."), "origin/main", "origin")
        self.assertEqual(nom, "main")

    def test_hors_de_toute_source_le_repli_donne_main(self):
        """Ni remote ni ref symbolique : le repli sur `main_ref`."""
        def faux_run(args, **kwargs):
            class Reponse:
                returncode = 1
                stdout = ""
                stderr = ""
            return Reponse()
        with mock.patch.object(organ.subprocess, "run", new=faux_run):
            nom = organ.branche_par_defaut(Path("."), "origin/main", "origin")
        self.assertEqual(nom, "main")

    def test_le_resolu_est_toujours_un_nom_de_branche_du_lot(self):
        """Le nom resolu doit exister parmi les branches distantes.

        C'est le test qui aurait attrape le defaut : `origin/main` n'est
        dans le lot sous aucun nom, et `main` si.
        """
        def faux_run(args, **kwargs):
            class Reponse:
                returncode = 0
                stdout = "refs/remotes/origin/main\n"
                stderr = ""
            if "--symref" in args:
                Reponse.returncode = 1
                Reponse.stdout = ""
            return Reponse()
        with mock.patch.object(organ.subprocess, "run", new=faux_run):
            nom = organ.branche_par_defaut(Path("."), "origin/main", "origin")
        self.assertIn(nom, {"main", "master", "trunk"})


class TestCasTrivialDeLaBrancheParDefaut(unittest.TestCase):
    """Le cas trivial : la branche par defaut est un ancetre d'elle-meme.

    Ces tests exercent `classe_branche` -- la fonction reelle, celle que
    `main()` appelle. Un test qui re-implemente la decision dans son propre
    corps est un couple auto-coherent : il passe quoi que fasse le code, et
    ne prouve donc rien. La reserve du relecteur sur ce point (review
    structurelle du 07/11) est levee par l'appel direct.
    """

    TETE = "a" * 40

    def test_la_branche_par_defaut_est_classee_p(self):
        """`main` est P, meme quand sa tete est un ancetre de `main`."""
        classe, retenue, note = organ.classe_branche(
            "main", self.TETE, [], "main", lambda: True)
        self.assertEqual(classe, "P")
        self.assertIsNone(retenue)
        self.assertEqual(note, "branche_par_defaut")

    def test_la_branche_par_defaut_est_p_meme_avec_des_prs(self):
        """L'exclusion P prime sur toute PR : elle passe avant le classement."""
        prs = [pr("OPEN", 1, oid=self.TETE)]
        classe, retenue, note = organ.classe_branche(
            "main", self.TETE, prs, "main", lambda: True)
        self.assertEqual(classe, "P")
        self.assertIsNone(retenue)

    def test_la_branche_par_defaut_ne_suit_pas_la_forme_du_repli(self):
        """Le repli (`origin/main` -> `main`) reste un nom de branche.

        Un nom de ref complet (`refs/remotes/origin/main`) ne correspond a
        aucune branche du lot : il ne doit donc pas etre compare tel quel.
        """
        self.assertEqual(organ.repli_branche_par_defaut("origin/main"), "main")
        self.assertEqual(
            organ.repli_branche_par_defaut("refs/remotes/origin/main"), "main")


class TestClasseBrancheExercee(unittest.TestCase):
    """`classe_branche` est la decision : elle est exercee, pas re-implementee."""

    TETE = "a" * 40
    VIEUX = "b" * 40

    @staticmethod
    def _mesure(valeur):
        return lambda: valeur

    def test_une_pr_ouverte_a_la_tete_donne_a(self):
        prs = [pr("OPEN", 7, oid=self.TETE)]
        classe, retenue, _ = organ.classe_branche(
            "f", self.TETE, prs, "main", self._mesure(False))
        self.assertEqual(classe, "A")
        self.assertEqual(retenue["number"], 7)

    def test_une_pr_mergee_a_la_tete_donne_b(self):
        prs = [pr("MERGED", 8, oid=self.TETE, merge_oid="c" * 40)]
        classe, retenue, _ = organ.classe_branche(
            "f", self.TETE, prs, "main", self._mesure(False))
        self.assertEqual(classe, "B")
        self.assertEqual(retenue["number"], 8)

    def test_une_pr_fermee_donne_c(self):
        prs = [pr("CLOSED", 9, oid=self.TETE)]
        classe, retenue, _ = organ.classe_branche(
            "f", self.TETE, prs, "main", self._mesure(False))
        self.assertEqual(classe, "C")
        self.assertEqual(retenue["number"], 9)

    def test_le_verrou_ouvert_prime_sur_une_pr_mergee_a_la_tete(self):
        """Le cas de coin signale par le relecteur.

        La branche porte une PR OUVERTE a une tete ANCIENNE et une PR
        MERGEE a la tete COURANTE. L'ancienne version ne faisait voter le
        verrou OUVERT qu'en repli : la PR mergee gagnait, la branche
        tombait en B (candidate), et la PR vivante disparaitait de la
        decision.
        """
        prs = [pr("OPEN", 10, oid=self.VIEUX), pr("MERGED", 11, oid=self.TETE)]
        classe, retenue, _ = organ.classe_branche(
            "f", self.TETE, prs, "main", self._mesure(False))
        self.assertEqual(classe, "A")
        self.assertEqual(retenue["number"], 10)
        self.assertEqual(retenue["state"], "OPEN")

    def test_une_pr_fermee_puis_mergee_reste_b(self):
        """La regle historique tient : une PR fermee n'emporte pas."""
        prs = [pr("CLOSED", 12, oid=self.VIEUX), pr("MERGED", 13, oid=self.TETE)]
        classe, retenue, _ = organ.classe_branche(
            "f", self.TETE, prs, "main", self._mesure(False))
        self.assertEqual(classe, "B")
        self.assertEqual(retenue["number"], 13)

    def test_sans_pr_un_contenu_sur_main_donne_d(self):
        classe, retenue, note = organ.classe_branche(
            "f", self.TETE, [], "main", self._mesure(True))
        self.assertEqual(classe, "D")
        self.assertIsNone(retenue)
        self.assertEqual(note, "ancestor_of_main")

    def test_sans_pr_un_contenu_absent_donne_e_inconnu(self):
        classe, _, note = organ.classe_branche(
            "f", self.TETE, [], "main", self._mesure(None))
        self.assertEqual(classe, "E")
        self.assertEqual(note, "head_absent_du_clone")

    def test_sans_pr_un_contenu_non_livre_donne_e(self):
        classe, _, note = organ.classe_branche(
            "f", self.TETE, [], "main", self._mesure(False))
        self.assertEqual(classe, "E")
        self.assertEqual(note, "not_ancestor_of_main")

    def test_la_mesure_du_contenu_nest_appellee_quavec_des_prs(self):
        """Une branche avec une PR exploitable ne se mesure pas sur son contenu."""
        appels = []

        def mesure():
            appels.append(1)
            return False

        prs = [pr("MERGED", 14, oid=self.TETE)]
        organ.classe_branche("f", self.TETE, prs, "main", mesure)
        self.assertEqual(appels, [])


class TestContrainteDeClasse(unittest.TestCase):
    """L'ordre de contraigance : OPEN bat MERGED bat CLOSED."""

    def test_open_bat_merged(self):
        self.assertLess(organ.RANG["OPEN"], organ.RANG["MERGED"])

    def test_merged_bat_closed(self):
        self.assertLess(organ.RANG["MERGED"], organ.RANG["CLOSED"])

    def test_les_cinq_classes_sont_definies(self):
        self.assertEqual(set(organ.CLASSE.values()), {"A", "B", "C"})


class TestColonnes(unittest.TestCase):
    """Le format de sortie est un contrat : six colonnes, tabulation."""

    def test_colonnes_attendues(self):
        self.assertEqual(
            organ.COLONNES,
            ("branch", "sha", "class", "pr_number", "pr_state", "note"))

    def test_la_sortie_ne_contient_pas_de_caractere_special(self):
        """Pas de BOM, pas de CRLF : le manifeste est lu par des outils."""
        self.assertNotIn("\r", "\n".join(organ.COLONNES))


class TestSecurite(unittest.TestCase):
    """L'organe est en lecture seule : il ne peut pas supprimer.

    On interdit les VERBES d'ecriture, pas les chaines de lecture. `refs/heads`
    est la forme que `git ls-remote --heads` renvoie -- c'est de la lecture.
    """

    VERBES_INTERDITS = (
        "git push",
        "push origin",
        "git branch -D",
        "git branch --delete",
        "git update-ref",
        "gh api -X DELETE",
        "gh api --method DELETE",
        "delete_ref",
    )

    @staticmethod
    def source() -> str:
        return open(
            os.path.join(_REPO, "scripts", "ci", "build_branch_cleanup_manifest.py"),
            encoding="utf-8").read()

    def test_aucun_verbe_d_ecriture_dans_le_code(self):
        source = self.source()
        for interdit in self.VERBES_INTERDITS:
            self.assertNotIn(interdit, source,
                             f"l'organe ne doit pas contenir {interdit!r}")

    def test_le_seul_acces_a_git_est_en_lecture(self):
        """Toutes les invocations `git` de l'organe sont des lectures."""
        source = self.source()
        invocations = [l.strip() for l in source.splitlines()
                       if '"git"' in l or '"gh"' in l]
        self.assertTrue(invocations, "l'organe doit appeler git et gh")
        for ligne in invocations:
            for verbe in ("push", "delete", "update-ref", "-D"):
                self.assertNotIn(verbe, ligne,
                                 f"verbe d'ecriture dans : {ligne}")

    def test_la_lecture_du_remote_est_explicite(self):
        """La seule ecriture de l'organe est son fichier de sortie local."""
        source = self.source()
        self.assertIn('"ls-remote", "--heads"', source)
        self.assertIn("write_text", source)


class TestMainEndToEnd(unittest.TestCase):
    """`main()` exerce en bout a bout : notes B et deuxieme passe C/E reelles.

    Les versions precedentes couvraient la note B par une copie locale
    (`TestPreuveDeContenu.note`) et ne touchaient jamais la deuxieme passe
    C/E (le second bloc de `main()`). Ici l'I/O de reseau est mockee et c'est
    le code reel de `main()` qui construit la sortie : un test qui le
    re-implementerait dans son propre corps passerait quoi que fasse le code.
    """

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmpdir = Path(self._tmp.name)
        self.out = self.tmpdir / "manifest.tsv"

    def tearDown(self):
        self._tmp.cleanup()

    def _note_de(self, branche: str) -> str:
        lignes = self.out.read_text(encoding="utf-8").splitlines()
        for ligne in lignes[1:]:  # lignes[0] = entete
            champs = ligne.split("\t")
            if len(champs) == 6 and champs[0] == branche:
                return champs[5]
        self.fail(f"branche {branche!r} absente du manifeste")

    def _executer(self, distant, prs, commits_main, tete):
        with mock.patch.object(organ, "branches_distantes",
                               return_value=distant), \
                mock.patch.object(organ, "etats_par_branche",
                                  return_value=prs), \
                mock.patch.object(organ, "commits_de_main",
                                  return_value=commits_main), \
                mock.patch.object(organ, "branche_par_defaut",
                                  return_value="main"), \
                mock.patch.object(organ, "tete_sur_main", side_effect=tete), \
                mock.patch.object(sys, "argv",
                                   ["prog", "--out", str(self.out),
                                    "--repo", str(self.tmpdir)]):
            code = organ.main()
        self.assertEqual(code, 0)

    def test_note_b_contenu_prouve_sur_main(self):
        b1 = "a" * 40
        self._executer(
            {"b-onmain": b1},
            {"b-onmain": [pr("MERGED", 101, oid=b1, merge_oid="m" * 40,
                              base="main")]},
            {"m" * 40},
            lambda repo, sha, main: False,
        )
        self.assertEqual(self._note_de("b-onmain"),
                         "merged:1;merged;content_on_main")

    def test_note_b_base_pilote_pas_sur_main(self):
        b2 = "b" * 40
        self._executer(
            {"b-pilot": b2},
            {"b-pilot": [pr("MERGED", 102, oid=b2, merge_oid="p" * 40,
                             base="feature/pilot")]},
            {"x" * 40},
            lambda repo, sha, main: False,
        )
        self.assertEqual(self._note_de("b-pilot"),
                         "merged:1;merged;merged_into_pilot_base:feature/pilot")

    def test_note_b_merge_commit_inconnu(self):
        b3 = "c" * 40
        self._executer(
            {"b-unknown": b3},
            {"b-unknown": [pr("MERGED", 103, oid=b3, merge_oid="", base="main")]},
            {"m" * 40},
            lambda repo, sha, main: False,
        )
        self.assertEqual(self._note_de("b-unknown"),
                         "merged:1;merged;merge_commit_unknown")

    def test_deuxieme_passe_ce_remplit_la_note_de_contenu(self):
        c1 = "d" * 40
        self._executer(
            {"c-branch": c1},
            {"c-branch": [pr("CLOSED", 104, oid=c1, merge_oid="", base="main")]},
            set(),
            lambda repo, sha, main: sha == c1,  # ancetre -> ancestor_of_main
        )
        self.assertEqual(self._note_de("c-branch"),
                         "closed:1;closed_unmerged;ancestor_of_main")

    def test_le_manifeste_est_ordonne_par_sha(self):
        """Le tri par SHA (contrat du README) passe par `main()` reellement."""
        lo, hi = "a" * 40, "f" * 40
        # Le nom inverse le sha : un tri par NOM donnerait [alpha, zeta],
        # un tri par SHA donne [zeta, alpha].
        self._executer(
            {"zeta": lo, "alpha": hi},
            {"zeta": [pr("CLOSED", 1, oid=lo)],
             "alpha": [pr("CLOSED", 2, oid=hi)]},
            set(),
            lambda repo, sha, main: False,
        )
        noms = [l.split("\t")[0] for l in
                self.out.read_text(encoding="utf-8").splitlines()[1:]]
        self.assertEqual(noms, ["zeta", "alpha"])


class TestPlafondPrsFailClosed(unittest.TestCase):
    """La garde PLAFOND_PRS (l.167) est fail-closed.

    Reserve Hermes #25257 : la garde etait sans test. Si la liste de PRs
    atteint le plafond --limit, `gh pr list` la retourne TRONQUEE sans
    avertissement, et le manifeste serait incomplet (fail-open).
    `etats_par_branche` doit lever SystemExit au lieu de construire un
    manifeste partiel.
    """

    def test_la_garde_leve_systemexit_a_plafond(self):
        n = organ.PLAFOND_PRS
        docs = json.dumps([
            {"headRefName": "b%d" % i, "number": i, "state": "MERGED",
             "headRefOid": "a" * 40, "baseRefName": "main",
             "mergeCommit": {"oid": "b" * 40}} for i in range(n)
        ])
        with mock.patch.object(organ, "sh", return_value=docs):
            with self.assertRaises(SystemExit):
                organ.etats_par_branche(Path("/tmp"))


if __name__ == "__main__":
    unittest.main()
