"""Tests du module ict.trajectories (stdlib + numpy, sans PyPhi)."""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import trajectories as T  # noqa: E402


# TPM state-by-node du reseau AND/OR a 3 noeuds, au format multidim de PyPhi.
# On place chaque ligne (plate, indexee par l'index little-endian) a sa position
# de tuple, de sorte que ANDOR_TPM[etat] == ligne d'index state_index(etat),
# exactement la convention que `network.tpm` de PyPhi expose.
_FLAT = np.array([
    [0, 0, 0], [0, 0, 1], [1, 0, 1], [1, 0, 0],
    [1, 1, 0], [1, 1, 1], [1, 1, 1], [1, 1, 0],
])
ANDOR_TPM = np.zeros((2, 2, 2, 3))
for _idx, _state in enumerate(T.all_states(3)):
    ANDOR_TPM[_state] = _FLAT[_idx]


def test_all_states_count_and_endianness():
    states = list(T.all_states(3))
    assert len(states) == 8
    # little-endian : index 1 -> bit 0 actif -> (1, 0, 0)
    assert states[0] == (0, 0, 0)
    assert states[1] == (1, 0, 0)
    assert T.state_index((1, 0, 0)) == 1
    assert T.state_index((0, 0, 1)) == 4


def test_deterministic_successor_matches_tpm():
    # (1,0,0) -> (0,0,1) d'apres la TPM AND/OR
    assert T.deterministic_successor(ANDOR_TPM, (1, 0, 0)) == (0, 0, 1)
    # (0,0,0) est un point fixe
    assert T.deterministic_successor(ANDOR_TPM, (0, 0, 0)) == (0, 0, 0)


def test_fixed_point_trajectory():
    path, cyc = T.state_trajectory(ANDOR_TPM, (0, 0, 0))
    assert cyc == 0
    assert T.attractor_of(ANDOR_TPM, (0, 0, 0)) == [(0, 0, 0)]


def test_limit_cycle_attractor():
    attr = T.attractor_of(ANDOR_TPM, (1, 0, 0))
    # cycle-3 : (1,0,0) -> (0,0,1) -> (1,1,0) -> (1,0,0)
    assert len(attr) == 3
    assert set(attr) == {(1, 0, 0), (0, 0, 1), (1, 1, 0)}


def test_basins_partition_state_space():
    basins = T.basin_sizes(ANDOR_TPM, 3)
    assert sum(basins.values()) == 8
    # un point fixe (bassin 1) + le cycle-3 (bassin 7)
    assert sorted(basins.values()) == [1, 7]


def test_phi_trajectory_and_events():
    phi_map = {s: float(T.state_index(s)) for s in T.all_states(3)}
    path = [(0, 0, 0), (1, 0, 0), (0, 0, 0)]  # index 0,1,0 -> creux/pic
    vals = T.phi_trajectory(phi_map, path)
    assert vals == [0.0, 1.0, 0.0]
    ev = T.detect_events(vals)
    assert ev["maxima"] == [1]
    assert ev["minima"] == []


def test_flip_bit():
    assert T.flip_bit((1, 1, 0), 0) == (0, 1, 0)
    assert T.flip_bit((1, 1, 0), 2) == (1, 1, 1)
