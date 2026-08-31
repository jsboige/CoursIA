#!/usr/bin/env python3
"""Resolution de la ZONE d'un grain (#13420) : par PR citante, par EPIC parent,
puis par le texte.

Pourquoi la troisieme source existe : `issue_to_family` est construit par
archeologie de PRs mergees. Une issue FRAICHE n'y est jamais -- or c'est
exactement ce qu'est le grain de consolidation qu'une zone saturee reclame.
Mesure du 2026-08-29 : #13467 (renumerotation GenAI/Texte) ne remontait a
aucune zone, donc `GenAI/Texte` restait `SANS REMEDE` alors que son remede
venait d'etre ouvert -- un garde dont le remede est invisible ne peut pas etre
satisfait, et la zone serait restee fermee a l'expansion pour toujours.

Pourquoi le titre prime sur le corps : c'est le faux positif reel qui a ete
mesure sur ce meme #13467, et il ne se voyait pas -- la resolution rendait une
zone plausible, juste pas la bonne.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from series_saturation import family_from_text, resolve_family  # noqa: E402

TEXTE = "MyIA.AI.Notebooks/GenAI/Texte"
RAG = "MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique"
RULES = ".claude/rules"
FAMS = (TEXTE, RAG, RULES)


def test_titre_prime_sur_le_corps():
    """Le cas mesure : titre GenAI/Texte, corps citant .claude/rules.

    Cherchees dans un blob unique, `.claude/rules` (13 car.) bat
    `genai/texte` (11 car.) et la zone reelle reste sans remede.
    """
    it = {"number": 13467,
          "title": "[#5081] GenAI/Texte : renumerotation -- 2 collisions",
          "body": "Catalogue byte-identique (.claude/rules/catalog-pr-hygiene.md)."}
    assert resolve_family(it, {}, FAMS) == TEXTE


def test_resolution_par_le_corps_si_titre_muet():
    it = {"number": 1, "title": "renumerotation de la serie",
          "body": "Concerne MyIA.AI.Notebooks/GenAI/Texte."}
    assert resolve_family(it, {}, FAMS) == TEXTE


def test_mot_courant_ne_matche_pas():
    """`Texte` seul est un mot francais courant : la feuille ne suffit pas.

    Le motif porte sur deux segments au minimum (`GenAI/Texte`), sinon toute
    prose mentionnant "un texte" serait rattachee a la serie.
    """
    assert family_from_text("ce notebook produit un texte en sortie", FAMS) is None
    assert family_from_text("regles et conventions du depot", FAMS) is None


def test_pr_citante_prime_sur_le_texte():
    """Une PR a REELLEMENT touche ce chemin : plus factuel qu'une mention."""
    it = {"number": 42, "title": "GenAI/Texte : quelque chose", "body": ""}
    assert resolve_family(it, {42: RAG}, FAMS) == RAG


def test_parent_prime_sur_le_texte():
    it = {"number": 43, "parent": 5081, "title": "GenAI/Texte : x", "body": ""}
    assert resolve_family(it, {5081: RAG}, FAMS) == RAG


def test_sans_familles_aucune_invention():
    """Familles non mesurees = pas de resolution. Un zero d'absence de mesure
    ne doit pas se lire comme une zone trouvee."""
    it = {"number": 1, "title": "MyIA.AI.Notebooks/GenAI/Texte", "body": ""}
    assert resolve_family(it, {}, ()) is None


def test_chemin_complet_prefere_au_suffixe():
    it = {"number": 1, "title": "MyIA.AI.Notebooks/GenAI/Texte : x", "body": ""}
    assert resolve_family(it, {}, FAMS) == TEXTE


def test_antislash_windows_normalise():
    assert family_from_text(r"MyIA.AI.Notebooks\GenAI\Texte", FAMS) == TEXTE
