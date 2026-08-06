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


# --------------------------------------------------------------- gap coverage
def test_normalize_counts_invalid_unseen_raises():
    """Le garde ``unseen`` invalide leve ValueError (branche d'erreur, ligne 69).
    Les chemins 'self' et 'uniform' sont couverts ; le garde de validation ne
    l'etait pas."""
    # une matrice de comptes avec une ligne nulle force l'entree dans la branche
    # ``if row_sums[i] <= 0`` ou ``unseen`` est valide.
    counts_zero_row = np.array([[0.0, 0.0], [1.0, 1.0]])
    try:
        E.tpm_from_transitions([(0, 1)], mapping={0: 0, 1: 1}, unseen="bogus")
        assert False, "aurait du lever ValueError pour unseen invalide"
    except ValueError:
        pass


def test_state_index_map_accepts_hashable_tuple_labels():
    """Le docstring promet ``n'importe quel label hachable (entier, tuple,
    chaine)``. Seuls les entiers etaient testes ; on verifie les tuples (un
    etat = configuration multi-noeuds, le cas d'usage reel des reseaux booleens)
    et l'ordre de premiere apparition les preserve."""
    states = [("a", 0), ("b", 1), ("a", 0), ("c", 2)]
    mapping = E.state_index_map(states)
    assert mapping == {("a", 0): 0, ("b", 1): 1, ("c", 2): 2}
    # la TPM se construit correctement sur ces labels composites.
    tpm, m2 = E.tpm_from_trajectory([("a", 0), ("b", 1), ("a", 0)])
    assert m2 == {("a", 0): 0, ("b", 1): 1}
    assert tpm.shape == (2, 2)


def test_tpm_from_trajectories_with_provided_mapping():
    """La branche ``mapping is not None`` (lignes 129-132) est un chemin de code
    distinct du default : le mapping fourni est reutilise tel quel (pas de
    reconstruction depuis l'union des etats). Etait non couvert."""
    trajs = [[0, 1], [0, 1]]
    provided = {0: 0, 1: 1}
    tpm, mapping = E.tpm_from_trajectories(trajs, mapping=provided)
    assert mapping is provided                      # reuse, pas de nouvel objet
    assert abs(tpm[0, 1] - 1.0) < 1e-9             # 0 -> 1 deux fois = deterministe
    assert np.allclose(tpm.sum(axis=1), 1.0)


def test_tpm_from_trajectory_single_absorbing_state():
    """Une trajectoire revenant toujours au meme etat ([0,0,0]) produit une TPM
    1x1 auto-absorbante (Dirac sur soi-meme), sans crash. Cas limite d'un etat
    puits."""
    tpm, mapping = E.tpm_from_trajectory([0, 0, 0])
    assert mapping == {0: 0}
    assert tpm.shape == (1, 1)
    assert abs(tpm[0, 0] - 1.0) < 1e-9


def test_flat_tpm_from_sbn_single_node_oscillator():
    """Le cas minimal ``n_nodes=1`` (TPM 2x2) etait non couvert (test existant =
    3 noeuds). Un reseau NON (inverseur) oscille : 0 -> 1 -> 0 -> 1."""
    sbn = np.array([[1], [0]])   # state 0 -> node devient 1 ; state 1 -> 0
    tpm = E.flat_tpm_from_sbn(sbn, 1)
    assert tpm.shape == (2, 2)
    assert np.allclose(tpm.sum(axis=1), 1.0)
    assert abs(CE.determinism(tpm) - 1.0) < 1e-9   # deterministe -> determinism=1
    expected = np.array([[0.0, 1.0], [1.0, 0.0]])
    assert np.allclose(tpm, expected)


def test_tpm_from_transitions_empty_is_degenerate_but_safe():
    """Une liste de transitions vide produit une TPM vide (0x0) et un mapping
    vide -- cas degeneré (aucune observation) qui ne doit pas crasher. Le
    comportement borne est documente ici."""
    tpm, mapping = E.tpm_from_transitions([])
    assert mapping == {}
    assert tpm.shape == (0, 0)
