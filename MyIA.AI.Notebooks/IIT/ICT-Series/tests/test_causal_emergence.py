"""Tests du module ict.causal_emergence (stdlib + numpy, sans PyPhi).

Verifie les primitives causales (determinisme / degenerescence / specificite /
effectiveness / EI) sur des TPM dont les valeurs sont connues analytiquement,
puis le coarse-graining, l'apportionment glouton et la complexite emergente.
"""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import causal_emergence as CE  # noqa: E402


# --------------------------------------------------------------- TPM de reference
def identity_tpm(n):
    """TPM identite : chaque etat se repete (det=1, deg=0, EI=log2(n))."""
    return np.eye(n)


def uniform_tpm(n):
    """TPM uniforme : chaque ligne est uniforme (det=0, eff=0, EI=0)."""
    return np.full((n, n), 1.0 / n)


def block_noise_tpm():
    """Systeme a 4 etats avec emergence causale.

    Deux blocs {0,1} et {2,3} ; a l'interieur d'un bloc la dynamique est
    bruitee (uniforme sur l'autre bloc), mais au niveau MACRO (2 etats) les
    blocs alternent de facon deterministe. L'effectiveness passe de 0.5 (micro)
    a 1.0 (macro) : emergence.
    """
    return np.array([
        [0.0, 0.0, 0.5, 0.5],
        [0.0, 0.0, 0.5, 0.5],
        [0.5, 0.5, 0.0, 0.0],
        [0.5, 0.5, 0.0, 0.0],
    ])


# --------------------------------------------------------------- validation
def test_validate_rejects_non_square():
    try:
        CE.validate_tpm(np.zeros((2, 3)))
        assert False, "aurait du lever ValueError"
    except ValueError:
        pass


def test_validate_rejects_unnormalized_rows():
    try:
        CE.validate_tpm(np.array([[0.5, 0.2], [0.0, 1.0]]))
        assert False, "aurait du lever ValueError"
    except ValueError:
        pass


# --------------------------------------------------------------- primitives
def test_identity_is_maximally_causal():
    n = 4
    tpm = identity_tpm(n)
    assert abs(CE.determinism(tpm) - 1.0) < 1e-9
    assert abs(CE.degeneracy(tpm) - 0.0) < 1e-9
    assert abs(CE.specificity(tpm) - 1.0) < 1e-9
    assert abs(CE.effectiveness(tpm) - 1.0) < 1e-9
    assert abs(CE.effective_information(tpm) - np.log2(n)) < 1e-9


def test_uniform_has_no_causal_information():
    tpm = uniform_tpm(4)
    assert abs(CE.determinism(tpm) - 0.0) < 1e-9
    assert abs(CE.effectiveness(tpm) - 0.0) < 1e-9
    assert abs(CE.effective_information(tpm) - 0.0) < 1e-9


def test_ei_equals_marginal_minus_mean_entropy():
    # EI = H(marginal) - <H(rows)>, definition KL-moyenne, doit egaler eff*log2(n)
    tpm = block_noise_tpm()
    m = CE.validate_tpm(tpm)
    marginal = m.mean(axis=0)
    mean_row_H = np.mean([CE._entropy_bits(m[i]) for i in range(4)])
    kl_form = CE._entropy_bits(marginal) - mean_row_H
    assert abs(CE.effective_information(tpm) - kl_form) < 1e-9


def test_block_noise_micro_effectiveness_is_half():
    # chaque ligne uniforme sur 2 etats : H=1 bit, det=1-1/2=0.5 ; marginal
    # uniforme sur 4 -> deg=0 -> eff=0.5
    tpm = block_noise_tpm()
    assert abs(CE.effectiveness(tpm) - 0.5) < 1e-9


# --------------------------------------------------------------- coarse-graining
def test_merge_reduces_size_and_stays_stochastic():
    tpm = block_noise_tpm()
    macro = CE.merge_states(tpm, 0, 1)
    assert macro.shape == (3, 3)
    assert np.allclose(macro.sum(axis=1), 1.0)


def test_merge_labels_bookkeeping():
    labels = CE.initial_labels(4)
    labels = CE.merge_labels(labels, 0, 1)
    assert labels[0] == (0, 1)
    assert len(labels) == 3
    labels = CE.merge_labels(labels, 1, 2)  # fusionne (2,) et (3,) en positions 1,2
    assert (2, 3) in labels
    assert len(labels) == 2


def test_merge_invalid_indices():
    tpm = identity_tpm(3)
    for bad in [(0, 0), (0, 3), (-1, 1)]:
        try:
            CE.merge_states(tpm, *bad)
            assert False, f"aurait du lever ValueError pour {bad}"
        except ValueError:
            pass


# --------------------------------------------------------------- apportionment
def test_identity_has_no_emergence():
    # systeme deja maximalement causal : aucune fusion n'ameliore l'effectiveness
    res = CE.greedy_apportionment(identity_tpm(4))
    assert len(res["scales"]) == 1          # micro-echelle seule
    assert res["deltas"] == []
    assert res["emergent_complexity"] == 0.0


def test_block_noise_shows_emergence():
    tpm = block_noise_tpm()
    res = CE.greedy_apportionment(tpm)
    micro_eff = res["scales"][0]["effectiveness"]
    macro_eff = res["scales"][-1]["effectiveness"]
    # le macro est strictement plus causal que le micro : emergence
    assert macro_eff > micro_eff + 1e-6
    # le macro final est l'alternateur 2-etats (effectiveness = 1.0)
    assert res["scales"][-1]["size"] == 2
    assert abs(macro_eff - 1.0) < 1e-9
    # tous les gains enregistres sont positifs
    assert all(d > 0 for d in res["deltas"])
    assert res["emergent_complexity"] > 0.0


def test_scales_sizes_strictly_decreasing():
    res = CE.greedy_apportionment(block_noise_tpm())
    sizes = [s["size"] for s in res["scales"]]
    assert all(b < a for a, b in zip(sizes, sizes[1:]))


# --------------------------------------------------------------- complexite emergente
def test_emergent_complexity_edge_cases():
    assert CE.emergent_complexity([]) == 0.0
    assert CE.emergent_complexity([1.0]) == 0.0           # une seule echelle
    assert CE.emergent_complexity([-1.0, -2.0]) == 0.0    # aucun gain positif


def test_emergent_complexity_uniform_vs_concentrated():
    # L=2 : repartition uniforme -> EC = log2(2) + H([.5,.5]) = 1 + 1 = 2
    assert abs(CE.emergent_complexity([1.0, 1.0]) - 2.0) < 1e-9
    # L=4 uniforme -> EC = log2(4) + H(unif_4) = 2 + 2 = 4
    assert abs(CE.emergent_complexity([1.0, 1.0, 1.0, 1.0]) - 4.0) < 1e-9
    # concentre (moins distribue) -> EC plus faible a L egal
    assert CE.emergent_complexity([3.0, 1.0]) < CE.emergent_complexity([1.0, 1.0])


# --------------------------------------------------------------- presentation
def test_apportionment_table_shape():
    res = CE.greedy_apportionment(block_noise_tpm())
    table = CE.apportionment_table(res)
    assert len(table) == len(res["scales"])
    assert table[0][-1] is None       # delta_cp du micro = None
    assert all(len(row) == 6 for row in table)
