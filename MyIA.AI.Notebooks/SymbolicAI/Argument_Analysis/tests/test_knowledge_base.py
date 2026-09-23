# -*- coding: utf-8 -*-
"""Tests de structure de knowledge_base.py — purs, sans dépendance externe.

Fige le comportement distillé (population transitive, convention lexicale de
négation, cohérence, appartenance) sur le banc du sas EPITA (#1961 Phase 5)
et les limites mesurées. La validation exécutée vit dans le notebook committé
(avec outputs), pas ici.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import knowledge_base as kb_mod
from knowledge_base import FormalArgument, KnowledgeBase, Proposition, negation


def deux_camps():
    """La base du sas : deux arguments opposés sur la concentration."""
    kb = KnowledgeBase()
    kb.add_argument(FormalArgument(
        premises=[Proposition(content="Le télétravail isole les collaborateurs")],
        conclusion=Proposition(content="Le télétravail réduit la concentration"),
        scheme="cause_effect",
    ))
    kb.add_argument(FormalArgument(
        premises=[Proposition(content="Les pauses régulières restaurent la concentration")],
        conclusion=Proposition(content="¬Le télétravail réduit la concentration"),
    ))
    return kb


def un_seul_camp():
    """La base cohérente du sas : un seul argument, aucune négation."""
    kb = KnowledgeBase()
    kb.add_argument(FormalArgument(
        premises=[Proposition(content="Le télétravail isole les collaborateurs")],
        conclusion=Proposition(content="Le télétravail réduit la concentration"),
        scheme="cause_effect",
    ))
    return kb


class TestBancSas(unittest.TestCase):
    """Le banc JSON partagé du sas, rejoué en dur (round-trip)."""

    def test_deux_camps_supporting(self):
        kb = deux_camps()
        prop = Proposition(content="Le télétravail réduit la concentration")
        self.assertEqual(len(kb.find_supporting_arguments(prop)), 1)

    def test_deux_camps_attacking(self):
        kb = deux_camps()
        prop = Proposition(content="Le télétravail réduit la concentration")
        self.assertEqual(len(kb.find_attacking_arguments(prop)), 1)

    def test_deux_camps_entails(self):
        kb = deux_camps()
        self.assertTrue(kb.entails(Proposition(content="Le télétravail isole les collaborateurs")))
        self.assertFalse(kb.entails(Proposition(content="Le télétravail augmente la productivité")))

    def test_deux_camps_incoherente(self):
        self.assertFalse(deux_camps().is_consistent())

    def test_un_seul_camp(self):
        kb = un_seul_camp()
        prop = Proposition(content="Le télétravail réduit la concentration")
        self.assertEqual(len(kb.find_supporting_arguments(prop)), 1)
        self.assertEqual(len(kb.find_attacking_arguments(prop)), 0)
        self.assertTrue(kb.is_consistent())


class TestPopulationTransitive(unittest.TestCase):
    """add_argument porte prémisses et conclusion (§1 du sas)."""

    def test_premisse_jamais_ajoutee_explicitement(self):
        kb = deux_camps()
        self.assertTrue(kb.entails(Proposition(content="Le télétravail isole les collaborateurs")))

    def test_comptes_deux_camps(self):
        kb = deux_camps()
        # 2 conclusions + 2 prémisses = 4 propositions distinctes
        self.assertEqual(len(kb.get_all_propositions()), 4)
        self.assertEqual(len(kb.get_all_arguments()), 2)


class TestLimitesMesurees(unittest.TestCase):
    """Les limites documentées du port — mesurées, pas supposées."""

    def test_entails_n_infere_rien(self):
        # Logique classique : d'une contradiction tout s'ensuit (ex falso).
        # Ici, P et ¬P cohabitent et entails(Q arbitraire) reste FAUX :
        # le test d'appartenance ne combine rien — c'est la limite mesurée.
        kb = deux_camps()  # base incohérente du sas
        self.assertFalse(kb.is_consistent())
        self.assertFalse(kb.entails(Proposition(content="Le télétravail augmente la productivité")))
        # et une proposition que PERSONNE n'a posée (ni argument ni ajout)
        kb2 = KnowledgeBase()
        kb2.add_proposition(Proposition(content="A"))
        self.assertFalse(kb2.entails(Proposition(content="B")))

    def test_double_negation_non_reconnue(self):
        # ¬¬P n'est pas P : une base P + ¬¬P est déclarée cohérente
        kb = KnowledgeBase()
        p = Proposition(content="Le débat est ouvert")
        kb.add_proposition(p)
        kb.add_proposition(negation(negation(p)))
        self.assertTrue(kb.is_consistent())
        self.assertEqual(negation(negation(p)).content, "¬¬Le débat est ouvert")

    def test_ecrasement_par_contenu(self):
        # deux Proposition de même contenu : la seconde écrase la première
        kb = KnowledgeBase()
        kb.add_proposition(Proposition(content="P", confidence=0.9))
        kb.add_proposition(Proposition(content="P", confidence=0.1))
        props = kb.get_all_propositions()
        self.assertEqual(len(props), 1)
        self.assertEqual(props[0].confidence, 0.1)

    def test_negation_est_lexicale(self):
        p = Proposition(content="X")
        self.assertEqual(negation(p).content, "¬X")
        kb = KnowledgeBase()
        kb.add_proposition(p)
        kb.add_proposition(negation(p))
        self.assertFalse(kb.is_consistent())


class TestStructure(unittest.TestCase):
    """Propriétés structurelles du port."""

    def test_eq_et_hash_par_contenu_seul(self):
        a = Proposition(content="P", confidence=0.9, source="expert")
        b = Proposition(content="P", confidence=0.2, source="sondage")
        self.assertEqual(a, b)
        self.assertEqual(hash(a), hash(b))

    def test_str_proposition_et_argument(self):
        p = Proposition(content="P")
        self.assertEqual(str(p), "P")
        arg = FormalArgument(premises=[p], conclusion=Proposition(content="Q"))
        self.assertEqual(str(arg), "[P] -> Q")

    def test_ids_distincts_arguments_identiques(self):
        a1 = FormalArgument(premises=[], conclusion=Proposition(content="C"))
        a2 = FormalArgument(premises=[], conclusion=Proposition(content="C"))
        self.assertNotEqual(a1.id, a2.id)

    def test_id_explicite_preserve(self):
        arg = FormalArgument(premises=[], conclusion=Proposition(content="C"), id="fixe")
        self.assertEqual(arg.id, "fixe")

    def test_base_vide_coherente(self):
        kb = KnowledgeBase()
        self.assertTrue(kb.is_consistent())
        self.assertEqual(kb.get_all_propositions(), [])
        self.assertEqual(kb.get_all_arguments(), [])


if __name__ == "__main__":
    unittest.main()
