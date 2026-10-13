# -*- coding: utf-8 -*-
"""Tests de structure de argumentation_schemes.py — purs, sans dépendance externe.

Fige les comptes distillés (10 schémas, forces a priori, ordre canonique) et les
propriétés structurelles du port. La validation exécutée vit dans le notebook
committé (avec outputs), pas ici.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import argumentation_schemes as a


BANC_POSITIFS = [
    ("Selon un spécialiste reconnu, la molécule est sans danger pour l'usage courant.", "expert_opinion"),
    ("L'étude repose sur une mesure directe et un échantillon représentatif du public.", "empirical_evidence"),
    ("La majorité des chercheurs parviennent à un accord sur ce point.", "consensus"),
    ("À l'instar du pilote maritime, comparable à un navigateur solitaire, le capitaine doit tracer sa route.", "analogy"),
    ("Cette cause profonde produit un effet mesurable sur le rendement.", "cause_effect"),
    ("Le coût total reste faible au regard du bénéfice annuel obtenu.", "economic_argument"),
    ("Compte tenu du risque identifié, la prévention s'impose dès maintenant.", "precautionary_principle"),
    ("Cette atteinte aux droits fondamentaux constitue une violation caractérisée.", "moral_argument"),
    ("Il existe un précédent historique : la même configuration a déjà été observée.", "historical_precedent"),
    ("La règle l'implique ; par conséquent, si la prémisse est établie, la conclusion suit.", "modus_ponens"),
]

BANC_NEGATIFS = [
    "Bonjour, il fait beau aujourd'hui.",
    "Le rapport compte douze pages et trois annexes.",
    "L'expert est attendu à la conférence.",
    "",
]


class TestComptesMesures(unittest.TestCase):
    """Fige l'inventaire de la distillation."""

    def test_dix_schemas(self):
        self.assertEqual(len(a._load_argumentation_schemes()), 10)

    def test_cles_schema(self):
        self.assertEqual(
            sorted(a._load_argumentation_schemes().keys()),
            sorted([
                "modus_ponens", "expert_opinion", "analogy", "cause_effect",
                "consensus", "empirical_evidence", "economic_argument",
                "precautionary_principle", "moral_argument", "historical_precedent",
            ]),
        )

    def test_forces_apriori_verbatim(self):
        forces = {k: s.strength for k, s in a._load_argumentation_schemes().items()}
        self.assertEqual(forces["modus_ponens"], 1.0)
        self.assertEqual(forces["empirical_evidence"], 0.9)
        self.assertEqual(forces["consensus"], 0.85)
        self.assertEqual(forces["expert_opinion"], 0.8)
        self.assertEqual(forces["moral_argument"], 0.8)
        self.assertEqual(forces["economic_argument"], 0.75)
        self.assertEqual(forces["cause_effect"], 0.7)
        self.assertEqual(forces["precautionary_principle"], 0.7)
        self.assertEqual(forces["historical_precedent"], 0.65)
        self.assertEqual(forces["analogy"], 0.6)

    def test_ordre_canonique_modus_ponens_dernier(self):
        self.assertEqual(a._CANONICAL_ORDER[-1], "modus_ponens")
        self.assertEqual(len(a._CANONICAL_ORDER), 10)
        self.assertEqual(a._CANONICAL_ORDER[0], "expert_opinion")

    def test_ordre_couvre_exactement_la_table(self):
        # Garde absente du source (divergence #3 du port) : un schéma ajouté à
        # la table mais oublié dans l'ordre serait silencieusement jamais
        # classifié. Ici, l'égalité des ensembles rend cet écart impossible.
        self.assertEqual(
            set(a._CANONICAL_ORDER),
            set(a._load_argumentation_schemes().keys()),
        )


class TestStructure(unittest.TestCase):
    """Propriétés structurelles du port."""

    def test_chaque_schema_a_questions_critiques(self):
        for key, s in a._load_argumentation_schemes().items():
            self.assertGreaterEqual(len(s.critical_questions), 2, key)

    def test_chaque_schema_a_ensembles_mots_cles(self):
        for key in a._load_argumentation_schemes():
            self.assertGreaterEqual(len(a._SCHEME_KEYWORDS[key]), 1, key)

    def test_chaque_schema_a_premisses_et_conclusion(self):
        for key, s in a._load_argumentation_schemes().items():
            self.assertGreaterEqual(len(s.premises_pattern), 1, key)
            self.assertTrue(s.conclusion_pattern, key)


class TestClassifieur(unittest.TestCase):
    """Le matcher déterministe sur le banc du source (#1961 Phase 5)."""

    def test_banc_positifs(self):
        for text, expected in BANC_POSITIFS:
            scheme = a.classify_scheme(text)
            self.assertIsNotNone(scheme, text)
            self.assertEqual(scheme.key, expected, f"{text!r} -> {scheme.key}, attendu {expected}")

    def test_banc_negatifs_rendent_none(self):
        for text in BANC_NEGATIFS:
            self.assertIsNone(a.classify_scheme(text), text)

    def test_texte_vide_none(self):
        self.assertIsNone(a.classify_scheme(""))
        self.assertIsNone(a.classify_scheme(None))

    def test_departage_specifique_bat_modus_ponens(self):
        # « donc » est présent (signal modus_ponens) MAIS « spécialiste » +
        # « selon » tirent expert_opinion d'abord : l'ordre canonique départage.
        texte = "Selon ce spécialiste, le médicament est sûr, donc on peut le prescrire."
        scheme = a.classify_scheme(texte)
        self.assertEqual(scheme.key, "expert_opinion")

    def test_donc_arme_cause_effect_avant_modus_ponens(self):
        # Divergence #4 du port : « donc »+« parce que » arment cause_effect,
        # placé AVANT modus_ponens dans l'ordre canonique — le modus ponens
        # lexical ne tire que sur ses propres paires.
        texte = "Il pleut parce que le nuage est là, donc le sol est humide."
        scheme = a.classify_scheme(texte)
        self.assertEqual(scheme.key, "cause_effect")

    def test_singleton_principe_de_precaution(self):
        # Divergence #2 du port : unique ensemble singleton de la table — la
        # locution entière suffit, sans paire.
        texte = "Nous invoquons le principe de précaution."
        scheme = a.classify_scheme(texte)
        self.assertEqual(scheme.key, "precautionary_principle")

    def test_mot_isole_ne_tire_jamais(self):
        for mot in ["donc", "si", "comme", "expert", "droit", "mesure"]:
            self.assertIsNone(a.classify_scheme(mot), mot)

    def test_texte_desaccentue_rend_none(self):
        # Les mots-clés sont accentués : la désaccentuation casse la paire
        # (garde du source, portée telle quelle — limite FR assumée).
        texte = "Selon ce specialiste reconnu, la molecule est sans danger."
        self.assertIsNone(a.classify_scheme(texte))

    def test_match_report_cohere_avec_classify(self):
        texte = "Selon ce spécialiste, la règle implique donc la conclusion."
        report = a.match_report(texte)
        self.assertTrue(report)
        self.assertEqual(report[0]["key"], a.classify_scheme(texte).key)
        # le rapport expose deux candidats : expert_opinion (rang 1) puis
        # modus_ponens (rang 10, ["donc","implique"] arme aussi)
        self.assertEqual(len(report), 2)
        self.assertEqual([r["key"] for r in report], ["expert_opinion", "modus_ponens"])


class TestRendu(unittest.TestCase):
    """Le rendu textuel de la table."""

    def test_prompt_context_dix_lignes(self):
        ctx = a.schemes_as_prompt_context()
        self.assertEqual(len(ctx.splitlines()), 10)

    def test_prompt_context_porte_force_et_questions(self):
        ctx = a.schemes_as_prompt_context()
        self.assertIn("force a priori", ctx)
        self.assertIn("questions", ctx)


if __name__ == "__main__":
    unittest.main()
