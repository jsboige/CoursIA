"""Tests du module ict.tpm_estimation (pont trajectoires -> TPM, stdlib+numpy)."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import tpm_estimation as E  # noqa: E402
from ict import causal_emergence as CE  # noqa: E402
from ict import trajectories as T  # noqa: E402


# --------------------------------------------------------------- indexation
def test_state_index_map_first_appearance_order():
    mapping = E.state_index_map(["b", "a", "b", "c", "a"])
    assert mapping == {"b": 0, "a": 1, "c": 2}


# --------------------------------------------------------------- estimation
def test_tpm_from_trajectory_deterministic_cycle():
    # cycle deterministe 0 -> 1 -> 2 -> 0 ...
    states = [0, 1, 2, 0, 1, 2, 0]
    tpm, mapping = E.tpm_from_trajectory(states)
    assert mapping == {0: 0, 1: 1, 2: 2}
    expected = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]], dtype=float)
    assert np.allclose(tpm, expected)
    # un cycle deterministe est maximalement causal (effectiveness = 1)
    assert abs(CE.effectiveness(tpm) - 1.0) < 1e-9


def test_tpm_from_transitions_counts_probabilities():
    # depuis 0 : deux fois vers 1, une fois vers 2 -> [0, 2/3, 1/3]
    transitions = [(0, 1), (0, 1), (0, 2), (1, 1), (2, 2)]
    tpm, mapping = E.tpm_from_transitions(transitions)
    i0 = mapping[0]
    assert abs(tpm[i0, mapping[1]] - 2.0 / 3.0) < 1e-9
    assert abs(tpm[i0, mapping[2]] - 1.0 / 3.0) < 1e-9
    assert np.allclose(tpm.sum(axis=1), 1.0)


def test_unseen_self_absorbing():
    # etat 1 jamais quitte (aucune transition sortante) -> auto-transition
    transitions = [(0, 1)]
    mapping = {0: 0, 1: 1}
    tpm, _ = E.tpm_from_transitions(transitions, mapping, unseen="self")
    assert abs(tpm[1, 1] - 1.0) < 1e-9
    assert np.allclose(tpm.sum(axis=1), 1.0)


def test_unseen_uniform():
    transitions = [(0, 1)]
    mapping = {0: 0, 1: 1}
    tpm, _ = E.tpm_from_transitions(transitions, mapping, unseen="uniform")
    assert np.allclose(tpm[1], [0.5, 0.5])


def test_tpm_from_trajectories_pools_transitions():
    trajs = [[0, 1, 0], [0, 1, 1]]
    tpm, mapping = E.tpm_from_trajectories(trajs)
    # depuis 0 : deux fois vers 1 -> P(0->1)=1 ; depuis 1 : une fois 0, une fois 1
    assert abs(tpm[mapping[0], mapping[1]] - 1.0) < 1e-9
    assert abs(tpm[mapping[1], mapping[0]] - 0.5) < 1e-9
    assert abs(tpm[mapping[1], mapping[1]] - 0.5) < 1e-9


def test_unknown_label_with_fixed_mapping_raises():
    try:
        E.tpm_from_transitions([(0, 9)], mapping={0: 0, 1: 1})
        assert False, "aurait du lever KeyError"
    except KeyError:
        pass


# --------------------------------------------------------------- pont state-by-node
def test_flat_tpm_from_sbn_matches_andor_network():
    # meme reseau AND/OR a 3 noeuds que test_trajectories
    flat = np.array([
        [0, 0, 0], [0, 0, 1], [1, 0, 1], [1, 0, 0],
        [1, 1, 0], [1, 1, 1], [1, 1, 1], [1, 1, 0],
    ])
    sbn = np.zeros((2, 2, 2, 3))
    for idx, state in enumerate(T.all_states(3)):
        sbn[state] = flat[idx]
    tpm = E.flat_tpm_from_sbn(sbn, 3)
    assert tpm.shape == (8, 8)
    assert np.allclose(tpm.sum(axis=1), 1.0)
    # reseau deterministe -> chaque ligne est un Dirac -> determinisme = 1
    assert abs(CE.determinism(tpm) - 1.0) < 1e-9
    # (1,0,0) [index 1] -> (0,0,1) [index 4]
    assert tpm[1, 4] == 1.0
