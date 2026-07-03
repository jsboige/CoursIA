"""Tests du module ict.synthesis (batterie cross-substrat, stdlib+numpy).

Verifie l'appareil de mesure unifie de la synthese ICT : trajectoire -> TPM ->
batterie d'emergence causale, et surtout le controle degenere *sans
complaisance* (shuffle) qui distingue une emergence reelle d'un artefact du
reservoir d'etats. Cf Epic #4588, issue #4946.
"""

import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import synthesis as S  # noqa: E402


# --------------------------------------------------------------- generateurs de test
def _deterministic_cycle(length: int = 30) -> list:
    """Cycle deterministe 0 -> 1 -> 2 -> 0 ... (maximalement causal au micro)."""
    return [t % 3 for t in range(length)]


def _macro_deterministic_micro_random(rng, length: int = 600) -> list:
    """Macro-cycle deterministe, micro-etat bruite (emergence multi-echelles).

    L'etat macro suit le cycle 0 -> 1 -> 2 -> 0 (deterministe), mais chaque
    macro-etat emet un micro-etat ``(macro, bit)`` avec ``bit`` aleatoire. Le
    micro est donc partiellement indeterministe ; un coarse-graining qui
    regroupe les deux micro-etats d'un meme macro RECOUVRE le determinisme ->
    emergence causale positive. Le shuffle de cette trajectoire detruit le
    cycle et donc l'emergence : c'est le contraste que la synthese credite.
    """
    return [(t % 3, int(rng.integers(0, 2))) for t in range(length)]


# --------------------------------------------------------------- batterie de base
def test_emergence_battery_deterministic_cycle():
    tpm = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]], dtype=float)
    bat = S.emergence_battery(tpm)
    # cycle deterministe : effectiveness maximale, EI = log2(3)
    assert abs(bat["effectiveness"] - 1.0) < 1e-9
    assert abs(bat["effective_information"] - np.log2(3)) < 1e-9
    # tout le travail causal est deja au micro : aucune fusion n'aide -> EC nulle
    assert bat["emergent_complexity"] == 0.0
    assert bat["n_scales"] == 1
    assert bat["n"] == 3


def test_trajectory_battery_counts():
    states = _deterministic_cycle(30)
    bat = S.trajectory_battery(states)
    assert bat["n_states"] == 3
    assert bat["n_transitions"] == 29
    assert abs(bat["effectiveness"] - 1.0) < 1e-9


# --------------------------------------------------------------- controle degenere
def test_shuffle_preserves_marginals():
    rng = np.random.default_rng(0)
    states = _macro_deterministic_micro_random(rng, length=200)
    shuffled = S.shuffle_states(states, rng)
    # meme multi-ensemble d'etats (seul l'ORDRE change)
    assert sorted(shuffled) == sorted(states)
    assert len(shuffled) == len(states)


def test_shuffled_baseline_keys():
    rng = np.random.default_rng(1)
    states = _deterministic_cycle(30)
    base = S.shuffled_baseline(states, rng, n_shuffles=5)
    assert base["n_shuffles"] == 5
    for key in ("effective_information", "effective_information_std",
                "emergent_complexity", "emergent_complexity_std"):
        assert key in base


# --------------------------------------------------------------- gain d'emergence
def test_emergence_gain_structured_beats_shuffle():
    # substrat structure multi-echelles : le reel doit dominer son shuffle
    rng = np.random.default_rng(42)
    states = _macro_deterministic_micro_random(rng, length=600)
    gain = S.emergence_gain(states, rng, n_shuffles=30)
    # la structure temporelle porte plus d'information effective que son shuffle
    assert gain["ei_real"] > gain["ei_shuffled"]
    assert gain["ei_gain"] > 0.0
    # une emergence multi-echelles reelle existe (EC micro->macro > 0)
    assert gain["ec_real"] > 0.0


def test_emergence_gain_iid_not_credited():
    # substrat sans structure temporelle : reel ~ shuffle -> non credite
    rng = np.random.default_rng(7)
    states = [int(rng.integers(0, 4)) for _ in range(600)]
    gain = S.emergence_gain(states, rng, n_shuffles=30)
    # une suite iid n'a pas de dynamique : le shuffle ne change (presque) rien
    assert gain["credited"] is False
    assert abs(gain["ei_gain"]) < 0.3


# --------------------------------------------------------------- gate inter-substrat
def test_cross_substrate_summary_keys():
    rng = np.random.default_rng(3)
    trajs = {
        "cycle": _deterministic_cycle(60),
        "emergent": _macro_deterministic_micro_random(rng, length=300),
    }
    summary = S.cross_substrate_summary(trajs, rng, n_shuffles=5)
    assert set(summary) == {"cycle", "emergent"}
    for entry in summary.values():
        for key in ("ei_real", "ei_gain", "ec_real", "ec_gain", "credited"):
            assert key in entry


def test_kendall_tau_identical_and_inverse():
    assert abs(S._kendall_tau([3, 2, 1], [6, 4, 2]) - 1.0) < 1e-12
    assert abs(S._kendall_tau([3, 2, 1], [1, 2, 3]) - (-1.0)) < 1e-12
    # moins de deux points : pas de paire departageable
    assert S._kendall_tau([1.0], [2.0]) == 0.0


def test_rank_consistency_detects_disagreement():
    # ei_real classe A>B>C, ec_gain classe C>B>A -> aucun scalaire ne transfere
    summary = {
        "A": {"ei_real": 3.0, "ec_gain": 0.1},
        "B": {"ei_real": 2.0, "ec_gain": 0.5},
        "C": {"ei_real": 1.0, "ec_gain": 0.9},
    }
    rc = S.rank_consistency(summary)
    assert rc["order_by_ei_real"] == ["A", "B", "C"]
    assert rc["order_by_ec_gain"] == ["C", "B", "A"]
    assert abs(rc["kendall_tau"] - (-1.0)) < 1e-12
    assert rc["consistent"] is False


def test_rank_consistency_detects_agreement():
    summary = {
        "A": {"ei_real": 3.0, "ec_gain": 0.9},
        "B": {"ei_real": 2.0, "ec_gain": 0.5},
        "C": {"ei_real": 1.0, "ec_gain": 0.1},
    }
    rc = S.rank_consistency(summary)
    assert abs(rc["kendall_tau"] - 1.0) < 1e-12
    assert rc["consistent"] is True


# --------------------------------------------------------------------------- #
#  Capstone ICT-15 (#5090) : cles fe_gain / k_gain retro-compatibles          #
# --------------------------------------------------------------------------- #


def test_emergence_gain_has_capstone_keys():
    # emergence_gain enrichi des deux facettes du capstone, sans casser les anciennes
    rng = np.random.default_rng(7)
    eg = S.emergence_gain(_macro_deterministic_micro_random(rng), rng, n_shuffles=3)
    # anciennes cles preservees (retro-compatibilite)
    for k in ["ei_real", "ei_shuffled", "ei_gain", "ec_real", "ec_shuffled",
              "ec_gain", "credited", "n_states"]:
        assert k in eg
    # nouvelles cles du capstone ICT-15
    assert "fe_gain" in eg
    assert "k_gain" in eg
    assert isinstance(eg["fe_gain"], float)
    assert isinstance(eg["k_gain"], float)


def test_capstone_keys_contrast_structured_vs_iid():
    # un cycle macro-deterministe : fe_gain et k_gain positifs (structure)
    rng = np.random.default_rng(8)
    structured = _macro_deterministic_micro_random(rng)
    iid = [(int(rng.integers(0, 3)), int(rng.integers(0, 2))) for _ in range(600)]
    eg_s = S.emergence_gain(structured, rng, n_shuffles=5)
    eg_n = S.emergence_gain(iid, rng, n_shuffles=5)
    # la structure batt nettement le shuffle sur les deux nouvelles facettes
    assert eg_s["fe_gain"] > eg_n["fe_gain"]
    assert eg_s["k_gain"] > eg_n["k_gain"]


def test_rank_consistency_works_with_capstone_keys():
    # rank_consistency est generique sur les cles : fe_gain/k_gain fonctionnent aussi
    summary = {
        "A": {"ec_gain": 0.9, "fe_gain": 2.0, "k_gain": 0.8},
        "B": {"ec_gain": 0.5, "fe_gain": 1.0, "k_gain": 0.4},
        "C": {"ec_gain": 0.1, "fe_gain": 0.2, "k_gain": 0.1},
    }
    rc_fe = S.rank_consistency(summary, key_a="fe_gain", key_b="k_gain")
    assert abs(rc_fe["kendall_tau"] - 1.0) < 1e-12

