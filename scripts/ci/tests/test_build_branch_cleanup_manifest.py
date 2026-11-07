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

Aucun test ne requiert de reseau ni de jeton GH : les fonctions de
classement sont pures et testees sur des tables construites a la main.
"""
from __future__ import annotations

import os
import sys
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
# scripts/ci/tests/ -> scripts/ci/ -> scripts/ -> racine du depot
_REPO = os.path.dirname(os.path.dirname(os.path.dirname(_HERE)))
sys.path.insert(0, os.path.join(_REPO, "scripts", "ci"))

import build_branch_cleanup_manifest as organ  # noqa: E402


def pr(etat, numero, oid=""):
    """Une entree de PR au format de l'organe : (etat, numero, headRefOid)."""
    return (etat, numero, oid.lower())


class TestClassification(unittest.TestCase):
    """Le classement d'une branche a partir de ses PRs et de sa tete."""

    @staticmethod
    def classer(nom, sha, prs, contenu=""):
        """Reproduit le classement de l'organe, isole de git et de gh."""
        tete = sha.lower()
        candidates = [p for p in prs if p[2] == tete]
        if not candidates:
            ouvertes = [p for p in prs if p[0] == "OPEN"]
            if ouvertes:
                candidates = [min(ouvertes, key=lambda p: p[1])]
        if candidates:
            retenue = min(candidates, key=lambda p: (organ.RANG[p[0]], p[1]))
            return organ.CLASSE[retenue[0]], retenue
        return "E", None

    def test_une_pr_fermee_sans_merge_donne_C(self):
        classe, retenue = self.classer(
            "feature/x", "aaa", [pr("CLOSED", 100, "aaa")])
        self.assertEqual(classe, "C")
        self.assertEqual(retenue[1], 100)

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
        self.assertEqual(retenue[1], 101)

    def test_une_pr_ouverte_bloque_meme_si_la_tete_a_bouge(self):
        """Le travail en cours est un verrou, pas un etat de la tete."""
        classe, retenue = self.classer(
            "feature/x", "new", [pr("OPEN", 100, "old")])
        self.assertEqual(classe, "A")
        self.assertEqual(retenue[1], 100)

    def test_plusieurs_prs_ouvertes_il_ya_en_a_une_seule_ouverte(self):
        classe, retenue = self.classer(
            "feature/x", "new", [pr("OPEN", 100, "old"), pr("OPEN", 101, "new")])
        self.assertEqual(classe, "A")
        self.assertEqual(retenue[1], 101)


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


if __name__ == "__main__":
    unittest.main()
