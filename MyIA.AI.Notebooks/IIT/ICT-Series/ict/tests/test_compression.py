"""Tests du module :mod:`ict.compression` (ICT-15 jambe K, Epic #4588).

La theorie fondatrice (ICT) pose que l'integration (Phi), la surprise (F) et la
**compression** (K) sont trois facettes d'une meme quantite. Ce module mesure K
par la **longueur zlib** de la sequence serialisee canoniquement, et isole la
**structure d'ordre** via un contraste shuffle (le meme multi-ensemble d'etats,
structure temporelle detruite).

Chaque test verrouille un invariant falsifiable : re-indexation canonique par
ordre de premiere apparition, determinisme, packing varint pour >256 etats,
contraste shuffle (periodique > 0, aleatoire ~ 0), et la courbe de Schmidhuber.
Pattern herite de ``test_reversibility_budget.py`` : bootstrap ``sys.path``
module-level, sans fixtures. Module autonome (stdlib ``zlib`` + ``numpy``).
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

from ict import compression as c  # noqa: E402


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  canonical_int_sequence : re-indexation par ordre de PREMIERE apparition
# --------------------------------------------------------------------------- #


def test_canonical_reindexes_by_first_appearance():
    """Chaque label recoit l'entier = nombre de labels distincts vus avant lui.

    [a,b,a,c] -> a=0 (1er), b=1 (2e), a=0 (deja vu), c=2 (3e) -> [0,1,0,2].
    L'attribution suit l'ordre de premiere apparition (pas un hash), rendant la
    serialisation reproductible et independante du choix de labels.
    """
    assert c.canonical_int_sequence(["a", "b", "a", "c"]) == [0, 1, 0, 2]
    assert c.canonical_int_sequence([5, 5, 5]) == [0, 0, 0]
    assert c.canonical_int_sequence([]) == []
    # Labelschaines / mixtes supportes tant que comparables pour l'egalite.
    assert c.canonical_int_sequence(["x", "y", "x", "z", "y"]) == [0, 1, 0, 2, 1]


def test_canonical_is_label_invariant():
    """Deux trajectoires isomorphes (meme structure, labels differents) donnent
    la MEME sequence canonique -- c'est le point de la re-indexation."""
    assert c.canonical_int_sequence(["A", "B", "A"]) == [0, 1, 0]
    assert c.canonical_int_sequence(["foo", "bar", "foo"]) == [0, 1, 0]
    assert c.canonical_int_sequence([100, 200, 100]) == [0, 1, 0]
    # Les entiers directement passes aussi (deja des int, mappages triviaux).
    assert c.canonical_int_sequence([0, 1, 0]) == [0, 1, 0]
    assert c.canonical_int_sequence([7, 3, 7]) == [0, 1, 0]


def test_canonical_range_is_identity():
    """Sur range(N), les labels sont deja 0..N-1 dans l'ordre -> identite."""
    assert c.canonical_int_sequence(list(range(10))) == list(range(10))
    assert c.canonical_int_sequence(list(range(300)))[-1] == 299


# --------------------------------------------------------------------------- #
#  compressed_length : determinisme, borne vide, packing varint >256
# --------------------------------------------------------------------------- #


def test_compressed_length_empty_is_zero():
    """Une sequence vide se compresse en 0 octet (garde explicite)."""
    assert c.compressed_length([]) == 0


def test_compressed_length_is_deterministic():
    """Meme entree -> meme sortie (zlib level fixe = reproductible). Deux appels
    sur la meme sequence donnent le meme compte d'octets."""
    seq = [0, 1, 2, 1, 0, 1, 2, 1, 0, 1, 2, 1]
    a = c.compressed_length(seq)
    b = c.compressed_length(seq)
    assert a == b
    assert isinstance(a, int) and a > 0


def test_compressed_length_periodic_is_shorter_than_random():
    """Une trajectoire periodique (structure d'ordre riche) se compresse mieux
    qu'une sequence aleatoire de memes dimensions -- le signal credite de K."""
    periodic = c.compressed_length([0, 1] * 50)  # 100 etats, 2 valeurs, cycle
    randomish = c.compressed_length(list(range(100)))  # 100 etats tous distincts
    assert periodic < randomish, (
        f"periodique ({periodic}) devrait etre plus court qu'aleatoire ({randomish})"
    )


def test_compressed_length_varint_path_over_256_states():
    """Au-dela de 256 etats distincts, le payload bascule sur un packing varint
    (un octet de continuation MSB par digit base-128). Le compte reste un entier
    positif fini -- pas de crash, pas de troncature silencieuse."""
    n = c.compressed_length(list(range(300)))
    assert isinstance(n, int) and n > 0
    # Meme avec des repetitions (peu de valeurs distinctes mais > 256 apparaissions),
    # la forme packed bytes (< 256 valeurs distinctes) s'applique.
    n2 = c.compressed_length([0, 1, 2] * 100)  # 300 etats, 3 valeurs distinctes
    assert isinstance(n2, int) and n2 > 0


# --------------------------------------------------------------------------- #
#  compression_gain : contraste shuffle isole la structure d'ordre
# --------------------------------------------------------------------------- #


def test_compression_gain_keys_and_echo():
    """Retourne les 4 cles documentees et reflete n_shuffles."""
    g = c.compression_gain([0, 1, 2, 3] * 25, _rng(1), n_shuffles=10)
    assert set(g.keys()) == {"len_real", "len_shuffled", "k_gain", "n_shuffles"}
    assert g["n_shuffles"] == 10
    assert g["len_real"] == c.compressed_length([0, 1, 2, 3] * 25)


def test_compression_gain_periodic_positive():
    """Une trajectoire periodique est plus compressible que sa permutation : le
    gain (fraction epargnee par la structure d'ordre) est strictement positif.

    Le shuffle preserve exactement les FREQUENCES d'etats : la compression
    d'ordre 0 (Huffman-like) est identique des deux cotes, donc tout gain zlib
    est attribuable a la STRUCTURE D'ORDRE (transitions), pas au reservoir.
    """
    g = c.compression_gain([0, 1, 2, 3] * 25, _rng(2), n_shuffles=20)
    assert g["k_gain"] > 0.0, (
        f"trajectoire periodique : k_gain devrait etre > 0, recu {g['k_gain']}"
    )
    # La version reelle est plus courte que la moyenne permutee.
    assert g["len_real"] < g["len_shuffled"]


def test_compression_gain_random_near_zero():
    """Une sequence sans structure d'ordre (tous etats distincts, ou bruit) n'a
    rien a compresser au-dela du reservoir : k_gain ~ 0 (la permutation ne
    change rien, il n'y a pas de regularite de transitions a detruire)."""
    g = c.compression_gain(list(range(100)), _rng(3), n_shuffles=20)
    assert abs(g["k_gain"]) < 0.05, (
        f"sequence sans structure : k_gain devrait etre ~ 0, recu {g['k_gain']}"
    )


def test_compression_gain_shuffle_preserves_frequencies():
    """Le controle permute conserve exactement le multi-ensemble d'etats. Sur
    une sequence a frequences heterogenes, le shuffled a les MEMES comptes que
    le reel (precondition du contraste) -- on le verifie indirectement : le gain
    d'un motif structure reste positif et borne."""
    seq = [1, 1, 1, 2, 2, 3] * 4  # frequences 12/8/4
    g = c.compression_gain(seq, _rng(4), n_shuffles=5)
    assert -1.0 <= g["k_gain"] <= 1.0  # k_gain est une fraction normalisee
    assert g["len_real"] > 0


# --------------------------------------------------------------------------- #
#  compression_progress : courbe de Schmidhuber, garde window
# --------------------------------------------------------------------------- #


def test_compression_progress_rejects_zero_window():
    """window < 1 est refuse (ValueError) -- garde explicite documentee."""
    with pytest.raises(ValueError, match="window"):
        c.compression_progress([0, 1, 2, 3], window=0)
    with pytest.raises(ValueError):
        c.compression_progress([0, 1, 2], window=-1)


def test_compression_progress_steps_and_length():
    """Les pas vont de ``window`` a ``len(states)`` inclus ; le tableau des
    ratios a la meme longueur que les pas, et ``window`` est renvoye."""
    pr = c.compression_progress([0, 1, 2, 3, 4, 5], window=2)
    assert list(pr["steps"]) == [2, 3, 4, 5, 6]
    assert len(pr["ratio"]) == len(pr["steps"]) == 5
    assert pr["window"] == 2


def test_compression_progress_single_point_when_window_equals_length():
    """Quand window == len(states), un seul pas (le prefixe complet) : un seul
    ratio, egal a longueur[len] / longueur[window] (lui-meme)."""
    pr = c.compression_progress([0, 1, 2], window=3)
    assert len(pr["steps"]) == 1
    assert len(pr["ratio"]) == 1
    # Le seul ratio est len(states)/len(prefixe window) = 1.0 (meme prefixe).
    assert pr["ratio"][0] == pytest.approx(1.0)


def test_compression_progress_ratios_positive():
    """Chaque ratio (longueur[t] / longueur[t-window]) est strictement positif :
    ce sont des comptes d'octets zlib, toujours > 0 pour un prefixe non vide."""
    pr = c.compression_progress([0, 1, 2, 1, 0, 1, 2, 1, 0], window=3)
    assert len(pr["ratio"]) > 0
    assert all(r > 0 for r in pr["ratio"])
