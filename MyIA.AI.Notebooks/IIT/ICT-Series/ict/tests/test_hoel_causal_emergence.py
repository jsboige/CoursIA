"""Tests du banc case 25 (Hoel 2013) — portes instrumentales et proprietes.

Couvre aussi, pour la premiere fois, l'organe ``ict.causal_emergence``
directement (cas analytiques G2) : aucun ``test_causal_emergence.py``
n'existait avant ce banc (prereg §4, instrument 1).

Le balayage complet de calibrage Fig. 2 (~6561 cablages x 8 bruits) est trop
lent pour l'unitaire : il vit dans le banc (``run_all`` -> results JSON).
Ici : portes G1/G2/G4, constructeurs, proprietes analytiques des systemes
Fig. 4/Fig. 5, temoin negatif H4.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.causal_emergence import causal_profile, partition_profile
from ict.hoel_causal_emergence import (
    calibrate_fig4,
    ei_mi,
    element_pair_groups,
    fig5_tpms,
    is_legal_grouping,
    legal_groupings_4ind,
    tpm_from_gates,
    witness_h4,
)

# cablage croise canonique Fig. 2 : {A,B} lisent {C,D} et reciproquement
FIG2_GATES = {0: (2, 3), 1: (2, 3), 2: (0, 1), 3: (0, 1)}

_G1_TPMS = [
    np.eye(4),
    np.full((4, 4), 0.25),
    np.array([[0.9, 0.1], [0.2, 0.8]]),
    np.array([[0.5, 0.5, 0.0], [0.0, 0.5, 0.5], [0.5, 0.0, 0.5]]),
    tpm_from_gates(3, {0: (1, 2), 1: (0, 2), 2: (0, 1)}, noise=0.15),
    tpm_from_gates(4, FIG2_GATES, noise=0.2),
]


# ------------------------------------------------------------------ G2 : analytique
def test_g2_copy_perfect_four_states():
    """COPY parfait : EI = log2(n), Eff = 1, degenerescence nulle."""
    prof = causal_profile(np.eye(4))
    assert abs(prof["effective_information"] - 2.0) < 1e-9
    assert abs(prof["effectiveness"] - 1.0) < 1e-9
    assert abs(prof["degeneracy"]) < 1e-9


def test_g2_total_noise():
    """Bruit total (TPM uniforme) : EI nulle."""
    prof = causal_profile(np.full((4, 4), 0.25))
    assert abs(prof["effective_information"]) < 1e-9


def test_g2_total_degeneracy():
    """Lignes identiques non uniformes : Eff nulle, determinisme maximal."""
    tpm = np.tile([1.0, 0.0, 0.0, 0.0], (4, 1))
    prof = causal_profile(tpm)
    assert abs(prof["effectiveness"]) < 1e-9
    assert abs(prof["determinism"] - 1.0) < 1e-9


# ------------------------------------------------------------------ G1 : double implémentation
@pytest.mark.parametrize("tpm", _G1_TPMS)
def test_g1_ei_mi_agrees_with_organ(tpm):
    """EI forme MI (banc) == EI forme det-deg (organe) a 1e-9 pres."""
    assert abs(ei_mi(tpm) - causal_profile(tpm)["effective_information"]) < 1e-9


def test_g1_ei_mi_analytic_bounds():
    assert abs(ei_mi(np.eye(4)) - 2.0) < 1e-9
    assert abs(ei_mi(np.full((4, 4), 0.25))) < 1e-9


# ------------------------------------------------------------------ G4 : garde de légalité
def test_g4_legal_on_off_pairs():
    """[[00,01,10],[11]] par paire : legal (perte d'identite)."""
    groups = element_pair_groups(4, [(0, 1), (2, 3)])
    assert is_legal_grouping(groups, [(0, 1), (2, 3)])


def test_g4_illegal_identity_split():
    """[[00,01],[10,11]] : distinguer 01 de 10 exige l'identite -> rejete."""
    assert not is_legal_grouping([[0, 1], [2, 3]], [(0, 1)])


def test_g4_rejects_broken_partitions():
    # etat 2 absent de la partition
    assert not is_legal_grouping([[0, 1], [3]], [(0, 1)])
    # partition d'un espace de 5 etats pour k = 2 (n = 4)
    assert not is_legal_grouping([[0, 1, 2, 3, 4]], [(0, 1)])
    # macro-elements qui ne partitionnent pas range(4)
    assert not is_legal_grouping([[0], [1], [2], [3]], [(0, 1), (1, 2)])


def test_g4_legal_total_macro_on_four_elements():
    """Macro unique on/off sur 4 elements (on = 1111) : legal."""
    groups = [[s for s in range(16) if s != 15], [15]]
    assert is_legal_grouping(groups, [(0, 1, 2, 3)])


# ------------------------------------------------------------------ constructeurs
def test_tpm_from_gates_row_stochastic():
    tpm = tpm_from_gates(4, FIG2_GATES, noise=0.25)
    assert tpm.shape == (16, 16)
    assert np.allclose(tpm.sum(axis=1), 1.0)
    assert (tpm >= 0).all()


def test_tpm_from_gates_deterministic_and():
    """Sans bruit, le systeme AND croise est deterministe : det = 1."""
    prof = causal_profile(tpm_from_gates(4, FIG2_GATES, noise=0.0))
    assert abs(prof["determinism"] - 1.0) < 1e-9


def test_tpm_from_gates_rejects_bad_wirings_and_noise():
    with pytest.raises(ValueError):  # auto-connexion
        tpm_from_gates(3, {0: (0, 1), 1: (0, 2), 2: (0, 1)})
    with pytest.raises(ValueError):  # entree dupliquee
        tpm_from_gates(3, {0: (1, 1), 1: (0, 2), 2: (0, 1)})
    with pytest.raises(ValueError):  # bruit hors [0, 1]
        tpm_from_gates(3, {0: (1, 2), 1: (0, 2), 2: (0, 1)}, noise=1.5)


# ------------------------------------------------------------------ Fig. 5 : propriétés
def test_fig5_macro_is_exact_copy_when_deterministic():
    """A bruit nul, le macro temporel Fig. 5 est un COPY parfait : EI = 2.0."""
    tp = fig5_tpms("quiet", noise=0.0)
    pm = partition_profile(tp["two_step"], tp["groups"])
    assert abs(pm["effective_information"] - 2.0) < 1e-9
    assert abs(pm["effectiveness"] - 1.0) < 1e-9


def test_fig5_tpms_valid_at_noise():
    tp = fig5_tpms("copy", noise=0.1)
    for m in (tp["one_step"], tp["two_step"]):
        assert np.allclose(m.sum(axis=1), 1.0)
    assert sorted(s for g in tp["groups"] for s in g) == list(range(16))


# ------------------------------------------------------------------ H4 : témoin négatif
def test_h4_no_emergence_on_independent_copies():
    """4 COPY bruitees independantes : CE <= 0 sur chaque regroupement legal."""
    res = witness_h4(0.1)
    assert len(res["rows"]) == 4
    assert all(row["CE"] <= 1e-9 for row in res["rows"])
    assert res["verdict"] == "CONFIRMEE"


def test_h4_groupings_exhaustive():
    for _label, groups in legal_groupings_4ind():
        assert sorted(s for g in groups for s in g) == list(range(16))


def test_h4_micro_effective():
    """Le micro du temoin est efficace (structure de groupe absente)."""
    res = witness_h4(0.1)
    assert res["micro"]["effectiveness"] > 0.4


# ------------------------------------------------------------------ Fig. 4 : classe bornée
def test_fig4_calibration_class_bounded():
    """12 cablages de cycle ; la lecture paires-dupliquees calibre exactement."""
    cal = calibrate_fig4()
    assert cal is not None, "Fig. 4 doit calibrer (famille paires dupliquees)"
    assert cal["exhaustive"]
    assert abs(cal["micro"]["determinism"] - 1.0) < 1e-9
    assert abs(cal["micro"]["effective_information"] - 2.43) < 0.06
    assert abs(cal["macro"]["effective_information"] - 3.0) < 1e-9
    assert abs(cal["macro"]["effectiveness"] - 1.0) < 1e-9


def test_fig4_duplicated_pair_cycle_analytic():
    """Le cycle de paires dupliquees : EI micro = 3*H(1/4) = 2.435 bits
    (analytique), macro = permutation deterministe -> EI = 3 bits exact."""
    from ict.hoel_causal_emergence import tpm_from_gates as tfg

    gates = {0: (2, 3), 1: (2, 3), 2: (4, 5), 3: (4, 5), 4: (0, 1), 5: (0, 1)}
    tpm = tfg(6, gates)
    micro = causal_profile(tpm)
    h_quarter = -(0.25 * np.log2(0.25) + 0.75 * np.log2(0.75))
    assert abs(micro["effective_information"] - 3 * h_quarter) < 1e-9
    groups = element_pair_groups(6, [(0, 1), (2, 3), (4, 5)])
    macro = partition_profile(tpm, groups)
    assert abs(macro["effective_information"] - 3.0) < 1e-9


# ------------------------------------------------------------------ Fig. 2 : exclusion structurelle
def test_fig2_symmetric_output_noise_det_identity():
    """Sous bruit symetrique de sortie : det = 1 - H(p) pour TOUT cablage."""
    def h(x):
        return -(x * np.log2(x) + (1 - x) * np.log2(1 - x))

    for p in (0.1, 0.2, 0.3):
        prof = causal_profile(tpm_from_gates(4, FIG2_GATES, noise=p))
        assert abs(prof["determinism"] - (1 - h(p))) < 1e-9


def test_fig2_exclusion_note_unreachable():
    """Le diagnostic d'exclusion demontre l'impossibilite (borne deg)."""
    from ict.hoel_causal_emergence import fig2_exclusion_note

    note = fig2_exclusion_note()
    assert note["impossible"]
    assert note["output_site"]["unreachable"]
    assert note["input_site"]["unreachable"]


def test_tpm_input_noise_site_valid():
    """Bruit d'entree : lignes stochastiques, determinisme < 1."""
    tpm = tpm_from_gates(4, FIG2_GATES, noise=0.2, noise_site="input")
    assert np.allclose(tpm.sum(axis=1), 1.0)
    assert causal_profile(tpm)["determinism"] < 1.0
