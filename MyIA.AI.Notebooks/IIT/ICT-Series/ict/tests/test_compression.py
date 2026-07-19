"""Tests unitaires pour :mod:`ict.compression` (ICT-13/16, strate 5, Epic #4588).

Le module ``compression`` attache la jambe K (compression) a la regularite
temporelle d'une trajectoire : renumerotation canonique -> longueur zlib ->
contraste shuffle (``k_gain``, le signal credite), plus la courbe de
Schmidhuber (``compression_progress``). Il est consomme par ``mdl`` (sweep
complexite-entropie), ``beauty``, ``free_energy`` -- module logic-heavy en
production, 0 test dedie avant cette PR (grep-empty ; suite du test_mdl.py,
meme veine test-coverage ICT).

Les gates couvrent les proprietes falsifiables de chaque fonction publique :
invariants de renumerotation, bornes de longueur, discrimination structurelle
(periodique vs aleatoire = la propriete centrale de k_gain), validations
d'entree. CPU-only : numpy + zlib, fixtures synthetiques deterministes,
aucun reseau/GPU/data.

Pattern herite de ``test_time_arrow.py`` / ``test_argumentation.py`` /
``test_mdl.py`` : bootstrap ``sys.path`` module-level, pas de fixtures,
tolerances commentees.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import compression as C  # noqa: E402


# --------------------------------------------------------------------------- #
#  Gate 1 : canonical_int_sequence (re-indexation ordre premiere apparition) #
# --------------------------------------------------------------------------- #


def test_canonical_first_appearance_order():
    """L'attribution d'index suit l'ordre de PREMIERE apparition :
    ['a','b','a','c'] -> [0,1,0,2] (a=0 vu en premier, b=1, c=2)."""
    assert C.canonical_int_sequence(["a", "b", "a", "c"]) == [0, 1, 0, 2]


def test_canonical_empty_and_consecutive():
    """Sequence vide -> []. Sequence d'elements distincts -> [0,1,2,...]."""
    assert C.canonical_int_sequence([]) == []
    assert C.canonical_int_sequence(["x", "y", "z"]) == [0, 1, 2]


def test_canonical_label_invariant():
    """La renumerotation est invariante au choix de labels : deux sequences
    isomorphes (meme structure d'apparition) donnent le meme indexage."""
    assert C.canonical_int_sequence([10, 20, 10, 30]) == C.canonical_int_sequence(
        ["a", "b", "a", "c"]
    )


def test_canonical_consecutive_range():
    """Les index attribues forment un range [0, k-1] contigu (pas de trou)."""
    out = C.canonical_int_sequence([3, 1, 3, 1, 9, 9, 3])
    assert sorted(set(out)) == list(range(max(out) + 1))


# --------------------------------------------------------------------------- #
#  Gate 2 : compressed_length (longueur zlib de la sequence canonique)        #
# --------------------------------------------------------------------------- #


def test_compressed_length_empty_is_zero_and_nonneg():
    """Sequence vide -> 0. Toute sequence non vide -> longueur > 0."""
    assert C.compressed_length([]) == 0
    assert C.compressed_length([0, 1, 2, 3]) > 0


def test_compressed_length_highly_compressible_sequence_shrinks():
    """Une sequence constante (1 symbole) est nettement plus courte qu'une
    sequence de meme longueur a 4 symboles alternes."""
    const = C.compressed_length([0] * 100)
    varied = C.compressed_length([0, 1, 2, 3] * 25)
    assert 0 <= const < varied, (
        f"sequence constante ({const}) doit etre plus courte que variee ({varied})"
    )


def test_compressed_length_grows_with_more_distinct_symbols():
    """A longueur fixe, plus de symboles distincts (entropie plus haute) ->
    longueur compressee plus grande (zlib compresse moins)."""
    n = 60
    few = C.compressed_length([0, 1] * (n // 2))           # 2 symboles
    many = C.compressed_length(list(range(10)) * (n // 10))  # 10 symboles
    assert few < many


def test_compressed_length_large_alphabet_uses_varint():
    """Quand max(etat) >= 256, le packing varint est utilise (pas de crash) ;
    la longueur reste positive. Sanity du chemin >256 etats."""
    seq = [0, 300, 300, 0, 300]  # maxv = 300 >= 256 -> varint packing
    assert C.compressed_length(seq) > 0


# --------------------------------------------------------------------------- #
#  Gate 3 : compression_gain (k_gain = signal credite reel vs shuffle)       #
# --------------------------------------------------------------------------- #


def test_compression_gain_returns_well_formed_dict():
    """Le dict de retour porte les 4 cles documentees et des valeurs coherentes."""
    res = C.compression_gain([0, 1, 2, 3] * 20, rng=np.random.default_rng(0), n_shuffles=5)
    assert {"len_real", "len_shuffled", "k_gain", "n_shuffles"} <= set(res.keys())
    assert res["n_shuffles"] == 5
    assert res["len_real"] > 0


def test_compression_gain_periodic_strongly_positive():
    """LA PROPRIETE CENTRALE : une trajectoire periodique (structure d'ordre
    forte) a un k_gain nettement positif (la realite est bien plus compressible
    que sa permutation). C'est le signal credite."""
    periodic = [0, 1, 2, 3] * 50
    res = C.compression_gain(periodic, rng=np.random.default_rng(1), n_shuffles=10)
    assert res["k_gain"] > 0.5, (
        f"periodique doit avoir k_gain > 0.5, recu {res['k_gain']}"
    )


def test_compression_gain_random_near_zero():
    """Une trajectoire aleatoire iid (pas de structure temporelle) a un k_gain
    proche de 0 : la realite n'est guere plus compressible que ses permutations.

    Note honnete : k_gain n'est pas EXACTEMENT 0 sur iid car l'overhead zlib
    domine aux courtes longueurs (documente dans la docstring). On teste la
    borne relative (random << periodic), pas l'egalite stricte a 0."""
    rng = np.random.default_rng(42)
    random_seq = list(rng.integers(0, 4, size=200))
    res = C.compression_gain(random_seq, rng=np.random.default_rng(7), n_shuffles=10)
    assert res["k_gain"] < 0.1, (
        f"aleatoire doit avoir k_gain < 0.1 (proche 0), recu {res['k_gain']}"
    )


def test_compression_gain_periodic_higher_than_random():
    """Discrimination structurelle : k_gain(periodique) >> k_gain(aleatoire).
    C'est le contrat du signal credite K (anti-regression critique)."""
    periodic = [0, 1, 2, 3] * 50
    rng = np.random.default_rng(99)
    random_seq = list(rng.integers(0, 4, size=200))
    kp = C.compression_gain(periodic, rng=np.random.default_rng(1), n_shuffles=10)["k_gain"]
    kr = C.compression_gain(random_seq, rng=np.random.default_rng(2), n_shuffles=10)["k_gain"]
    assert kp > kr, (
        f"periodique ({kp}) doit avoir k_gain > aleatoire ({kr})"
    )


def test_compression_gain_deterministic_with_seeded_rng():
    """Avec un rng seed fixe, deux appels identiques donnent le meme k_gain
    (reproductibilite, pas de nondeterminisme cache)."""
    seq = [0, 1, 0, 2, 0, 1, 0, 2] * 10
    r1 = C.compression_gain(seq, rng=np.random.default_rng(123), n_shuffles=8)
    r2 = C.compression_gain(seq, rng=np.random.default_rng(123), n_shuffles=8)
    assert r1["k_gain"] == r2["k_gain"]


# --------------------------------------------------------------------------- #
#  Gate 4 : compression_progress (courbe de Schmidhuber)                      #
# --------------------------------------------------------------------------- #


def test_compression_progress_validates_window():
    """``window < 1`` -> ValueError."""
    with pytest.raises(ValueError):
        C.compression_progress([0, 1, 2, 3], window=0)


def test_compression_progress_length_and_types():
    """Le nombre de steps == len(seq) - window + 1 ; ratio est un array numpy
    de meme longueur ; window est renvoye."""
    seq = [0, 1, 2, 3, 0, 1, 2, 3]
    w = 2
    res = C.compression_progress(seq, window=w)
    assert len(res["steps"]) == len(seq) - w + 1
    assert len(res["ratio"]) == len(res["steps"])
    assert res["window"] == w
    assert isinstance(res["ratio"], np.ndarray)


def test_compression_progress_ratios_positive():
    """Tous les ratios sont strictement positifs (longueurs compressee > 0
    pour toute sequence non vide ; denom=1 si prefixe vide)."""
    seq = [0, 1, 2, 3] * 4
    res = C.compression_progress(seq, window=3)
    assert np.all(res["ratio"] > 0)
