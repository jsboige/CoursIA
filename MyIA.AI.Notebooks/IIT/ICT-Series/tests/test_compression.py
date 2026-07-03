"""Tests du module ict.compression (jambe K du capstone ICT-15, See #5090).

Verifient la serialisation canonique, la longueur zlib, le gain de compression
contraste au shuffle, et la courbe de Schmidhuber. Le controle *sans
complaisance* est central : un cycle deterministe DOIT etre nettement plus
compressible qu'une permutation de memes etats (structure d'ordre), alors qu'un
bruit iid ne l'est pas (k_gain ~ 0).

Numpy + pytest, comme les tests existants du package.
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import compression as CMP  # noqa: E402


# --------------------------------------------------------------------------- #
#  Serialisation canonique                                                    #
# --------------------------------------------------------------------------- #


def test_canonical_int_sequence_first_appearance_order():
    # les labels sont re-indexes par ordre de PREMIERE apparition
    seq = ["b", "a", "b", "c", "a"]
    assert CMP.canonical_int_sequence(seq) == [0, 1, 0, 2, 1]


def test_canonical_int_sequence_independent_of_label_type():
    # meme structure, labels differents -> meme sequence d'entiers
    a = CMP.canonical_int_sequence(["x", "y", "x"])
    b = CMP.canonical_int_sequence([(0,), (1,), (0,)])
    assert a == b == [0, 1, 0]


def test_canonical_int_sequence_empty():
    assert CMP.canonical_int_sequence([]) == []


# --------------------------------------------------------------------------- #
#  Longueur compressee                                                        #
# --------------------------------------------------------------------------- #


def test_compressed_length_empty_is_zero():
    assert CMP.compressed_length([]) == 0


def test_compressed_length_positive_and_bounded():
    seq = [i % 4 for i in range(100)]
    n = CMP.compressed_length(seq)
    assert n > 0
    # zlib ajoute un overhead constant (~11 octets min) ; un cycle 4-etats
    # de 100 pas doit tenir en bien moins de 100 octets
    assert n < 100


def test_compressed_length_cycle_beats_noise():
    rng = np.random.default_rng(0)
    cycle = [i % 4 for i in range(300)]
    noise = list(rng.integers(0, 4, size=300))
    assert CMP.compressed_length(cycle) < CMP.compressed_length(noise)


def test_compressed_length_more_than_256_states():
    # > 256 etats distincts -> packing varint, ne doit pas planter ni diverger
    seq = list(range(400))
    n = CMP.compressed_length(seq)
    assert n > 0
    # borne large : le varint produit <= 2 octets/etat pour <16384 etats, donc
    # la sortie comprese reste raisonnablement bornee (on verifie surtout que
    # le chemin varint tourne sans erreur ni explosion).
    assert n < 2 * 400 + 100


# --------------------------------------------------------------------------- #
#  Gain de compression (controle shuffle)                                     #
# --------------------------------------------------------------------------- #


def test_compression_gain_keys_and_n_shuffles():
    rng = np.random.default_rng(1)
    seq = [i % 4 for i in range(100)]
    g = CMP.compression_gain(seq, rng, n_shuffles=8)
    assert set(g) == {"len_real", "len_shuffled", "k_gain", "n_shuffles"}
    assert g["n_shuffles"] == 8


def test_compression_gain_cycle_positive():
    # un cycle deterministe est nettement plus compressible que sa permutation
    rng = np.random.default_rng(2)
    cycle = [i % 4 for i in range(300)]
    g = CMP.compression_gain(cycle, rng, n_shuffles=10)
    assert g["k_gain"] > 0.5
    assert g["len_real"] < g["len_shuffled"]


def test_compression_gain_iid_near_zero():
    # un bruit iid : la structure d'ordre est absente, k_gain ~ 0
    rng = np.random.default_rng(3)
    noise = list(rng.integers(0, 4, size=300))
    g = CMP.compression_gain(noise, rng, n_shuffles=10)
    assert abs(g["k_gain"]) < 0.1


def test_compression_gain_invariant_to_label_permutation():
    # renommer les labels d'un cycle ne change pas k_gain (canonisation)
    rng = np.random.default_rng(4)
    cycle = [i % 4 for i in range(200)]
    relabeled = [{0: "a", 1: "b", 2: "c", 3: "d"}[x] for x in cycle]
    g1 = CMP.compression_gain(cycle, rng, n_shuffles=10)
    g2 = CMP.compression_gain(relabeled, rng, n_shuffles=10)
    assert g1["k_gain"] == pytest.approx(g2["k_gain"], abs=0.02)


# --------------------------------------------------------------------------- #
#  Courbe de Schmidhuber (compression_progress)                               #
# --------------------------------------------------------------------------- #


def test_compression_progress_shape_and_window():
    seq = [i % 4 for i in range(100)]
    p = CMP.compression_progress(seq, window=10)
    assert set(p) == {"steps", "ratio", "window"}
    assert p["window"] == 10
    assert p["steps"].shape == p["ratio"].shape
    # steps commence a `window` et va jusqu'a len(seq)
    assert p["steps"][0] == 10
    assert p["steps"][-1] == 100


def test_compression_progress_ratio_positive():
    seq = [i % 4 for i in range(100)]
    p = CMP.compression_progress(seq, window=10)
    assert np.all(p["ratio"] > 0)


def test_compression_progress_rejects_bad_window():
    with pytest.raises(ValueError):
        CMP.compression_progress([0, 1, 2], window=0)
