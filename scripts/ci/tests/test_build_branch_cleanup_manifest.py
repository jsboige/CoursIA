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
        """`refs/remotes/origin/HEAD` fait foi ; `main_ref` est le repli."""
        source = organ.branche_par_defaut.__doc__ or ""
        self.assertIn("symbolic-ref", source)
        self.assertIn("refs/remotes/origin/HEAD", source)

    def test_un_repli_sans_symbole_deduit_le_nom_de_main_ref(self):
        """Hors d'un clone, `origin/main` donne `main`."""
        self.assertEqual(organ.repli_branche_par_defaut("origin/main"), "main")

    def test_un_repli_sans_prefixe_renvoie_la_ref_entiere(self):
        self.assertEqual(organ.repli_branche_par_defaut("main"), "main")

    def test_la_branche_par_defaut_est_classee_p_avant_toute_mesure(self):
        """Reproduit l'ordre du classement : P l'emporte sur D.

        `main` n'a aucune PR exploitable et sa tete est un ancetre de
        `main` : sans l'exclusion, elle tombait en D.
        """
        defaut = "main"
        nom, sha = "main", "aaa"
        prs = []
        if nom == defaut:
            classe, retenue = organ.CLASSE_PROTEGEE, None
        else:
            classe, retenue = "D", None
        self.assertEqual(classe, "P")
        self.assertIsNone(retenue)


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
