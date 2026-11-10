#!/usr/bin/env python3
"""Tests de la calibration du motif « limites » (#21424 T5).

La mesure fondatrice (2026-10-27, 58 lignes vivantes portant le motif) : 12
sont des faux positifs semantiques, en six familles. Un detecteur qui les
signale envoie une lane lire des carnets pour rien — c'est exactement ce qui
s'est produit sur ce tri.

Ces tests encodent la mesure, et surtout son CONTROLE POSITIF : sans
neutralisation, le motif brut mord sur chaque ligne listee. Si un jour le
motif cesse de mordre, le test echoue aussi — il verifie que la neutralisation
est bien la cause du silence, pas une reformulation des cas.
"""

import importlib.util
import os

import pytest

_PATH = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                     "notebook_tools", "check_concession_prose.py")

_spec = importlib.util.spec_from_file_location("check_concession_prose", _PATH)
cc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cc)


# Six familles mesurees sur les 58 lignes du delta (tranches 1 et 2).
FAUX_POSITIFS = [
    # bornes de phrases (chunking)
    "Le decoupage respecte les limites de phrases, plus naturel.",
    "le chunking respecte les limites de mots",
    # cas limites (edge cases)
    "Gestion des cas limites (n < 2)",
    "Gestion des cas limites (villes inconnues)",
    # verification aux limites (bornes d'intervalle)
    "Verification aux limites : les tests valident les frontieres",
    # contraintes de portefeuille
    "respectant toutes les limites institutionnelles standards.",
    "Couche 5 - Limites d'exposition :",
    "On integre les contraintes reglementaires et les limites de position.",
    # DFS borne
    "Il execute des DFS limites par une borne sur f(n).",
    # parametres de cout et de taux
    "configure les modeles cibles et les limites de cout par image.",
    "Cette section teste les limites de taux (rate limits).",
    # figure technique
    "Les 11 puzzles sont tous charges pour tester les limites",
]

VRAIES_CONCESSIONS = [
    "**Limites du JSON Mode**",
    "Limites de l'approche : necessite un prompt bien calibre",
    "Le cote honnete du verdict",
    "Limites : ne resout pas les erreurs permanentes",
    "non disponible sur cette machine",
]


@pytest.mark.parametrize("line", FAUX_POSITIFS)
def test_faux_positif_neutralise(line):
    """Le contexte technique ne doit plus designer un travail."""
    assert cc.concession_match(cc._normalize(line)) is None


@pytest.mark.parametrize("line", FAUX_POSITIFS)
def test_controle_positif_le_motif_brut_mordait(line):
    """Controle positif : sans la neutralisation, ces lignes etaient des hits.

    Si ce test tombe, ce n'est pas la neutralisation qui produit le silence
    ci-dessus : c'est que la ligne a cesse de porter le motif, et l'autre test
    ne prouve plus rien.
    """
    assert cc.CONCESSION_RE.search(cc._normalize(line)) is not None


@pytest.mark.parametrize("line", VRAIES_CONCESSIONS)
def test_vraie_concession_preservee(line):
    """Une concession reelle reste signalee."""
    assert cc.concession_match(cc._normalize(line)) is not None


def test_autre_motif_de_la_meme_ligne_reste_actif():
    """La neutralisation porte sur l'occurrence, pas sur la ligne.

    Une phrase peut nommer un cas limite ET un etat degrade : supprimer le
    hit entier masquerait la concession reelle.
    """
    line = "Cas limites rencontres ; API non disponible pour ce run"
    match = cc.concession_match(cc._normalize(line))
    assert match is not None
    assert not match.group(0).startswith("limite")


def test_limites_seul_reste_un_aveu():
    """Garde-fou : la neutralisation ne doit pas vider le motif de son sens."""
    assert cc.concession_match(cc._normalize("Limites :")) is not None
