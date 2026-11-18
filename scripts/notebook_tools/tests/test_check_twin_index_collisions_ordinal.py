#!/usr/bin/env python3
"""Tests purs pour la classification semantique ON-MAIN / MULTI-PR (#18683).

Trois invariants garantis par les controles ci-dessous :

  1. `classify_ordinal_collisions` distingue ON-MAIN (refus) et
     MULTI-PR (avertissement) d'apres la presence de base_ref dans
     by_ref -- c'est le predicat qu'utilisera le merge gate.

  2. Les fixtures reproduisent les cas reels du tableau de l'issue
     #18683 (pistes collisionnees) sans dependre d'un depot reel.

  3. Le geste de correction (`ordinal_correction_gist`) nomme la voie
     `git mv PUR` (pas de re-execution, pas de contenu a toucher --
     la contiguite n'est pas testee, cf check_twin_index_collisions.py
     docstring l. 49-51) avec l'index suivant calcule sur la base.

Pourquoi des tests purs
-----------------------
La verification de bout en bout (worktree reel, registre reel) est
testee par `test_check_twin_index_collisions.py` -- l'organe jumeau.
Le contrat qui est UNIQUEMENT a nous est la **classification
semantique ON-MAIN / MULTI-PR**, qui depend du couple
`{cross_ref, base_ref}` et se pretent donc a des fixtures
deterministes sans git.
"""
from __future__ import annotations

import os
import sys
import unittest

# Le module jumeau vit dans le repertoire parent ; on l'ajoute au sys.path
# comme test_check_twin_parity.py (mecanisme de la suite de tests).
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_twin_index_collisions as ctix


class TestClassifyOrdinalCollisions(unittest.TestCase):
    """Classification semantique ON-MAIN / MULTI-PR (#18683).

    Predicat : si `base_ref` apparait dans `by_ref`, la collision est
    ON-MAIN (refus, main va rougir des le merge). Sinon MULTI-PR
    (avertissement, concurrence de lanes).
    """

    BASE = "origin/main"

    def test_on_main_base_and_head(self):
        """Cas du tableau #18683 -- `search-06-adversarialsearch 0008`.

        La base porte deja l'index, et une PR le re-prend avec un nom
        different. ON-MAIN : refus, le merge cree le doublon main.
        """
        cross = [{
            "pair": "search-06-adversarialsearch",
            "index": "0008",
            "by_ref": {
                "origin/main": ["0008-2026-08-16-myia-po-2023-CoursIA.yaml"],
                "refs/pull/18500/head": [
                    "0008-2026-09-22-myia-po-2024-CoursIA.yaml",
                ],
            },
        }]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "ON-MAIN")
        self.assertEqual(out[0]["pair"], "search-06-adversarialsearch")
        self.assertEqual(out[0]["index"], "0008")

    def test_multi_pr_two_heads_no_base(self):
        """Cas du tableau #18683 -- `planners-6-domains 0012`.

        Deux PRs prennent le meme index, mais la base ne le porte pas.
        MULTI-PR : la premiere mergee gagne, la seconde renumerote.
        """
        cross = [{
            "pair": "planners-6-domains",
            "index": "0012",
            "by_ref": {
                "refs/pull/18537/head": [
                    "0012-2026-09-25-myia-po-2023-CoursIA.yaml",
                ],
                "refs/pull/18654/head": [
                    "0012-2026-09-26-myia-po-2024-CoursIA.yaml",
                ],
            },
        }]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "MULTI-PR")

    def test_multi_pr_three_heads(self):
        """Trois PRs en parallele, toutes sans la base -- le 1er merge gagne."""
        cross = [{
            "pair": "complexity-3-p-vs-np",
            "index": "0007",
            "by_ref": {
                "refs/pull/19001/head": [
                    "0007-2026-09-30-myia-po-2023-CoursIA.yaml",
                ],
                "refs/pull/19002/head": [
                    "0007-2026-09-30-myia-po-2024-CoursIA.yaml",
                ],
                "refs/pull/19003/head": [
                    "0007-2026-09-30-myia-po-2025-CoursIA-2.yaml",
                ],
            },
        }]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "MULTI-PR")

    def test_on_main_mixed_with_multi_pr(self):
        """Un mix : un ON-MAIN + un MULTI-PR dans la meme liste."""
        cross = [
            {"pair": "p1", "index": "0001",
             "by_ref": {self.BASE: ["0001-base.yaml"],
                         "head": ["0001-head.yaml"]}},
            {"pair": "p2", "index": "0002",
             "by_ref": {"head1": ["0002-head1.yaml"],
                         "head2": ["0002-head2.yaml"]}},
        ]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "ON-MAIN")
        self.assertEqual(out[1]["verdict"], "MULTI-PR")

    def test_empty_cross_is_empty(self):
        self.assertEqual(
            ctix.classify_ordinal_collisions([], base_ref=self.BASE), [])

    def test_pure_passthrough(self):
        """Les autres champs (pair, index, by_ref) sont preserves tels quel."""
        cross = [{"pair": "x", "index": "0001",
                  "by_ref": {self.BASE: ["a.yaml"], "head": ["b.yaml"]},
                  "extra_field": "preserved"}]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["pair"], "x")
        self.assertEqual(out[0]["index"], "0001")
        self.assertEqual(out[0]["by_ref"], {self.BASE: ["a.yaml"],
                                              "head": ["b.yaml"]})
        self.assertEqual(out[0]["extra_field"], "preserved")
        self.assertEqual(out[0]["verdict"], "ON-MAIN")


class TestOrdinalCorrectionGist(unittest.TestCase):
    """Le geste de correction est-il nomme dans la sortie ?

    Issue #18683 demande que la sortie dise quoi faire : renuméroter
    via `git mv` PUR (pas de re-execution).
    """

    def test_ON_MAIN_gist_mentions_git_mv(self):
        gist = ctix.ordinal_correction_gist(
            "csp-1-fundamentals", "0022",
            by_ref={"origin/main": ["0022-base.yaml"],
                    "head": ["0022-head.yaml"]},
            base_ref="origin/main",
        )
        self.assertIn("git mv", gist)
        self.assertIn("csp-1-fundamentals", gist)

    def test_MULTI_PR_gist_explains_concurrence(self):
        gist = ctix.ordinal_correction_gist(
            "planners-6-domains", "0012",
            by_ref={"head1": ["0012-h1.yaml"],
                    "head2": ["0012-h2.yaml"]},
            base_ref="origin/main",
        )
        self.assertIn("premiere tete mergee", gist)


class TestOrdinalCollisionsFixtureFromIssue(unittest.TestCase):
    """Reproduit le tableau de collisions mesure le 01/10 (#18683 body).

    Toutes les entrees sont fixtures : aucune collision reelle n'est
    exercee sur le worktree -- on passe directement a la fonction de
    classification une liste `cross_ref` shapee comme la sortie JSON
    du module jumeau. Le contrat de l'organe jumeau est teste separement
    dans test_check_twin_index_collisions.py.
    """

    BASE = "origin/main"

    def test_table_entry_search_06_index_0008(self):
        cross = [{"pair": "search-06-adversarialsearch", "index": "0008",
                  "by_ref": {self.BASE: ["0008-base.yaml"],
                              "refs/pull/18536/head": ["0008-h.yaml"],
                              "refs/pull/18500/head": ["0008-h.yaml"]}}]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "ON-MAIN")

    def test_table_entry_app_14_index_0016(self):
        cross = [{"pair": "app-14-connectfour-adversarial", "index": "0016",
                  "by_ref": {self.BASE: ["0016-base.yaml"],
                              "refs/pull/18536/head": ["0016-different.yaml"]}}]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "ON-MAIN")

    def test_table_entry_planners_6_index_0012(self):
        cross = [{"pair": "planners-6-domains", "index": "0012",
                  "by_ref": {"refs/pull/18654/head": ["0012-a.yaml"],
                              "refs/pull/18537/head": ["0012-b.yaml"]}}]
        out = ctix.classify_ordinal_collisions(cross, base_ref=self.BASE)
        self.assertEqual(out[0]["verdict"], "MULTI-PR")


class TestFindConflictsIntegration(unittest.TestCase):
    """Integration avec `find_conflicts` du module jumeau.

    On passe directement des refs pretes (forme `{ref: {paire: {idx: [noms]}}}`),
    on regarde ce que `find_conflicts` rend, puis on applique
    `classify_ordinal_collisions` au resultat. Le test verifie que
    les deux modules composent.
    """

    BASE = "origin/main"

    def test_ON_MAIN_compose_with_find_conflicts(self):
        """Cas ON-MAIN : base porte l'index, head le re-prend."""
        import check_twin_index_collisions as ctix
        refs = {
            self.BASE: {"csp-1-fundamentals": {
                "0022": ["0022-2026-09-30-myia-po-2025-CoursIA.yaml"]}},
            "worktree": {"csp-1-fundamentals": {
                "0022": ["0022-2026-10-01-myia-ai-01-CoursIA-2.yaml"]}},
        }
        result = ctix.find_conflicts(refs)
        out = ctix.classify_ordinal_collisions(
            result["cross_ref"], base_ref=self.BASE)
        self.assertEqual(len(out), 1)
        self.assertEqual(out[0]["verdict"], "ON-MAIN")

    def test_MULTI_PR_compose_with_find_conflicts(self):
        """Cas MULTI-PR : deux heads, base ne porte pas."""
        import check_twin_index_collisions as ctix
        refs = {
            self.BASE: {"planners-6-domains": {}},
            "refs/pull/18537/head": {"planners-6-domains": {
                "0012": ["0012-h1.yaml"]}},
            "refs/pull/18654/head": {"planners-6-domains": {
                "0012": ["0012-h2.yaml"]}},
        }
        result = ctix.find_conflicts(refs)
        out = ctix.classify_ordinal_collisions(
            result["cross_ref"], base_ref=self.BASE)
        self.assertEqual(len(out), 1)
        self.assertEqual(out[0]["verdict"], "MULTI-PR")

    def test_no_collision_compose_with_find_conflicts(self):
        """Aucun collision : cross_ref vide."""
        import check_twin_index_collisions as ctix
        refs = {
            self.BASE: {"csp-1-fundamentals": {
                "0001": ["0001.yaml"], "0002": ["0002.yaml"]}},
            "worktree": {"csp-1-fundamentals": {
                "0003": ["0003.yaml"]}},
        }
        result = ctix.find_conflicts(refs)
        out = ctix.classify_ordinal_collisions(
            result["cross_ref"], base_ref=self.BASE)
        self.assertEqual(out, [])


if __name__ == "__main__":
    unittest.main()