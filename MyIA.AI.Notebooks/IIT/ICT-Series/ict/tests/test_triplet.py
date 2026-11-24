"""Tests du module ``ict.triplet`` — assemblage du triplet (sigma, K, ordre).

Palier 21 (#23777) : la fonction d'assemblage rend les trois lectures du
gate re-decoupe cote a cote, SANS les agreger en un scalaire. Les gates
ci-dessous sont falsifiables — chacune peut rougir sur une regression de
l'assemblage :

  Gate 1 (structure) : le retour porte exactement les quatre cles attendues
    (sigma, K, ordre, meta) et AUCUN scalaire au sommet — le gate est un
    triplet, pas une note.
  Gate 2 (organ passthrough) : la TPM de la jambe sigma est identique a
    celle de ``argumentation.belief_transition_matrix`` sur les memes
    entrees — l'assemblage ne recode pas l'organe.
  Gate 3 (determinisme) : meme graine -> memes contre-factuels ; graine
    differente -> au moins un tirage different.
  Gate 4 (contre-factuels) : chaque ordre permute est une permutation de
    l'ordre narratif (meme multiset) et la liste a ``n_permuts`` entrees.
  Gate 5 (jambe K) : ``tpm_bits > 0`` et ``bits_compression > 0`` sur un
    debat non trivial.
  Gate 6 (refus) : ordre d'arrivee vide -> ``RefusDeMesure`` portant
    ``ENTREE_VIDE`` — un refus n'est pas un zero.
  Gate 7 (encodage inconnu) : ``ValueError`` avant toute mesure.

Implementation : aucune dependance externe ; un seul import numpy + import
du package ``ict``. Les debats concrets sont construits a la main pour
chaque gate.
"""

from __future__ import annotations

import sys
import os

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import argumentation
from ict import triplet
from ict.argumentation import DungAF, RefusDeMesure


def _debat_minimal() -> tuple:
    """Debat jouet : 3 arguments, une attaque qui inverse le labeling.

    Ordre [0, 1, 2] avec l'attaque (1, 0) : 0 arrive seul (in), puis 1
    l'attaque (0 passe out), puis 2 non attaque (in). La trajectoire
    summary traverse quatre etats distincts — de quoi mesurer.
    """
    af = DungAF(range(3), [(1, 0)])
    return af, [0, 1, 2]


# --------------------------------------------------------------------------- #
#  Gate 1 : structure — un triplet, pas une note                                #
# --------------------------------------------------------------------------- #


def test_gate1_structure_triplet_sans_scalaire() -> None:
    af, order = _debat_minimal()
    retour = triplet.assembler_triplet(af, order)
    assert set(retour.keys()) == {"sigma", "K", "ordre", "meta"}
    # Aucun scalaire au sommet : chaque valeur de premiere cle est un dict.
    for cle, valeur in retour.items():
        assert isinstance(valeur, dict), f"la cle {cle} porte un scalaire"


# --------------------------------------------------------------------------- #
#  Gate 2 : la TPM vient de l'organe, identique                                #
# --------------------------------------------------------------------------- #


def test_gate2_tpm_identique_a_belief_transition_matrix() -> None:
    af, order = _debat_minimal()
    for encoding in ("summary", "signature"):
        retour = triplet.assembler_triplet(af, order, encoding=encoding)
        P_organ, _ = argumentation.belief_transition_matrix(af, order, encoding=encoding)
        assert np.allclose(retour["sigma"]["tpm"], P_organ), (
            f"TPM divergente de l'organe (encoding={encoding})"
        )


# --------------------------------------------------------------------------- #
#  Gate 3 : determinisme du tirage des contre-factuels                         #
# --------------------------------------------------------------------------- #


def test_gate3_determinisme_de_la_graine() -> None:
    af = DungAF(range(6), [(1, 0), (3, 2), (5, 4)])
    order = [0, 1, 2, 3, 4, 5]
    r0a = triplet.assembler_triplet(af, order, n_permuts=5, seed=0)
    r0b = triplet.assembler_triplet(af, order, n_permuts=5, seed=0)
    r1 = triplet.assembler_triplet(af, order, n_permuts=5, seed=1)
    sig0a = [p["sigma"] for p in r0a["ordre"]["permuts"]]
    sig0b = [p["sigma"] for p in r0b["ordre"]["permuts"]]
    ordres0a = [p["ordre_permute"] for p in r0a["ordre"]["permuts"]]
    ordres0b = [p["ordre_permute"] for p in r0b["ordre"]["permuts"]]
    ordres1 = [p["ordre_permute"] for p in r1["ordre"]["permuts"]]
    assert sig0a == sig0b, "meme graine, sigmas contre-factuels differents"
    assert ordres0a == ordres0b, "meme graine, ordres tires differents"
    assert ordres0a != ordres1, "graine differente, ordres tires identiques"


# --------------------------------------------------------------------------- #
#  Gate 4 : chaque contre-factuel est une permutation de l'ordre narratif      #
# --------------------------------------------------------------------------- #


def test_gate4_permutations_valides() -> None:
    af, order = _debat_minimal()
    retour = triplet.assembler_triplet(af, order, n_permuts=6)
    permuts = retour["ordre"]["permuts"]
    assert len(permuts) == 6
    for p in permuts:
        assert sorted(p["ordre_permute"]) == sorted(order), (
            "un contre-factuel n'est pas une permutation de l'ordre narratif"
        )
        assert isinstance(p["sigma"], float)


# --------------------------------------------------------------------------- #
#  Gate 5 : la jambe K mesure bien quelque chose                                #
# --------------------------------------------------------------------------- #


def test_gate5_jambe_k_positive() -> None:
    af, order = _debat_minimal()
    retour = triplet.assembler_triplet(af, order)
    assert retour["K"]["tpm_bits"] > 0
    assert retour["K"]["bits_compression"] > 0
    assert retour["K"]["n_etats"] >= 2
    assert retour["K"]["n_transitions"] == len(order)  # prefixe vide inclus


# --------------------------------------------------------------------------- #
#  Gate 6 : ordre vide = refus de mesure, pas un zero                          #
# --------------------------------------------------------------------------- #


def test_gate6_ordre_vide_refus() -> None:
    af, _ = _debat_minimal()
    with pytest.raises(RefusDeMesure) as excinfo:
        triplet.assembler_triplet(af, [])
    assert excinfo.value.code == "ENTREE_VIDE"


# --------------------------------------------------------------------------- #
#  Gate 7 : encodage inconnu rejete avant toute mesure                          #
# --------------------------------------------------------------------------- #


def test_gate7_encodage_inconnu() -> None:
    af, order = _debat_minimal()
    with pytest.raises(ValueError):
        triplet.assembler_triplet(af, order, encoding="binaire")
