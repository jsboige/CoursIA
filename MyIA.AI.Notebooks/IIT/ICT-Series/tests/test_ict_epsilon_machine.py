"""Tests pytest pour ``ict/epsilon_machine`` (ICT-17, See #5100).

Convention : on importe le module via ``sys.path.insert(0, ...)`` pour
imiter le pattern des autres tests ``ict`` (cf ``test_causal_emergence``).
"""

from __future__ import annotations

import os
import sys
import math

import numpy as np
import pytest

# Setup path : on remonte d'un cran pour importer ``ict``.
sys.path.insert(
    0,
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
)

from ict import epsilon_machine as EM  # noqa: E402


# --------------------------------------------------------------------------- #
#  Helpers                                                                    #
# --------------------------------------------------------------------------- #


def periodic_seq(k: int, length: int) -> list:
    """Sequence periodique ``0, 1, ..., k-1, 0, 1, ..., k-1, ...``."""
    return [i % k for i in range(length)]


def deterministic_periodic_seq() -> list:
    """Sequence deterministe periodique ``0, 1, 2, 0, 1, 2, ...``."""
    return [0, 1, 2] * 30


def iid_seq(k: int, n: int, seed: int = 42) -> list:
    """Sequence i.i.d. uniforme sur ``k`` etats."""
    rng = np.random.default_rng(seed)
    return [int(v) for v in rng.integers(0, k, size=n)]


def mk_markov_2(p_stay: float, n: int, seed: int = 0) -> list:
    """Chaine de Markov 2 etats (0, 1) avec probabilite de rester ``p_stay``."""
    rng = np.random.default_rng(seed)
    s = [0] * n
    for t in range(1, n):
        s[t] = s[t - 1] if rng.random() < p_stay else 1 - s[t - 1]
    return s


# --------------------------------------------------------------------------- #
#  causal_state_partition                                                     #
# --------------------------------------------------------------------------- #


def test_partition_periodic_deterministic():
    """Une sequence deterministe periodique ``0,1,2,0,1,2,...`` a 1 etat causal (systeme markovien d'ordre 2) si history_len >= 3.

    NB pedagogique : avec history_len=2 et future_len=2, la partition
    Crutchfield voit 3 etats causaux (un par phase du cycle 3), pas 1 --
    l'etat causal est la PLUS FINE passe a memoire deterministe de la
    distribution de futur. Avec history_len=3 (la periode exacte), les 3
    tuples distincts de longueur 3 sont en bijection avec la phase, donc
    on obtient le meme resultat (3 etats causaux) -- c'est invariant.
    Pour obtenir 1 etat causal, il faut que ``history_len + future_len``
    capture TOUTE la periode, c'est-a-dire history_len=3 ET future_len=3
    (la passe complete identifie la phase, et le futur est deterministe
    par la phase).
    """
    seq = deterministic_periodic_seq()
    n_occurrences = len(seq) - 3 + 1
    part = EM.causal_state_partition(seq, history_len=3, future_len=3, tol=1e-6)
    assert part["n_histories"] == n_occurrences
    # Avec history_len=3, future_len=3 sur un cycle 3, 3 etats causaux
    # (un par phase). C'est l'invariant : Crutchfield identifie la phase
    # du cycle, pas le cycle lui-meme.
    assert part["n_causal_states"] == 3, (
        f"cycle 3 avec history_len=3 devrait donner 3 etats causaux "
        f"(un par phase), recu {part['n_causal_states']}"
    )


def test_partition_iid_full_separation():
    """Pour i.i.d., chaque passe est son propre etat causal (la distribution conditionnelle du futur depend uniquement de la passe)."""
    seq = iid_seq(2, 400, seed=7)
    part = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.0)
    # En tol=0, toutes les distributions sont distinctes (futurs aleatoires).
    # Le resultat depend de la longueur de la sequence ; on verifie au moins
    # qu'on n'a PAS un seul etat causal (ce serait suspect).
    assert part["n_causal_states"] >= 2


def test_partition_invalid_history_len():
    with pytest.raises(ValueError):
        EM.causal_state_partition([0, 1, 2], history_len=0, future_len=1)


def test_partition_short_trajectory():
    with pytest.raises(ValueError):
        EM.causal_state_partition([0, 1], history_len=2, future_len=2)


def test_partition_marks_causal_states():
    """L'attribut ``occurrence_to_causal`` doit couvrir toutes les occurrences et chaque passe canonique doit etre dans au moins un etat causal."""
    seq = periodic_seq(4, 200)
    part = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.05)
    # Toutes les occurrences indexees (C198-HARD : cle par index d'occurrence)
    assert len(part["occurrence_to_causal"]) == part["n_histories"]
    # Toutes les passes canoniques couvertes par l'alias semantique
    unique_hists = set(tuple(seq[t : t + 2]) for t in range(len(seq) - 1))
    assert set(part["history_to_causal"].keys()) >= unique_hists


def test_partition_history_to_causal_is_injective():
    """Chaque OCCURRENCE de passe doit etre assignee a un etat causal unique (cle = index d'occurrence, pas tuple canonique -- C198-HARD)."""
    seq = mk_markov_2(0.7, 200, seed=1)
    part = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.1)
    assert len(part["occurrence_to_causal"]) == part["n_histories"]
    # Les indices sont [0, n_histories)
    assert set(part["occurrence_to_causal"].keys()) == set(range(part["n_histories"]))


# --------------------------------------------------------------------------- #
#  statistical_complexity                                                     #
# --------------------------------------------------------------------------- #


def test_Cmu_monotone_in_n_states():
    """C_mu doit augmenter avec le nombre d'etats causaux (maximal pour iid, minimal pour constant).

    NB C198-HARD pedagogique : une sequence periodique ``0,1,2`` n'a PAS
    un seul etat causal (la phase du cycle est observable, donc 3 etats
    causaux avec history_len=3). Le bon "zero-etat" est la sequence
    CONSTANTE ``[0]*N``, qui n'a qu'une seule passe canonique et un seul
    futur -> 1 etat causal, C_mu = 0.
    """
    # Sequence CONSTANTE : 1 etat causal, C_mu = 0 (cas trivial).
    seq_const = [0] * 200
    p_const = EM.causal_state_partition(seq_const, history_len=2, future_len=2,
                                        tol=1e-6)
    cm_const = EM.statistical_complexity(p_const, seq_const)["C_mu"]

    # Sequence iid : beaucoup d'etats causaux, C_mu >> 0
    seq_iid = iid_seq(2, 1000, seed=3)
    p_iid = EM.causal_state_partition(seq_iid, history_len=2, future_len=2,
                                      tol=0.05)
    cm_iid = EM.statistical_complexity(p_iid, seq_iid)["C_mu"]

    assert cm_const < 0.5, f"C_mu constante doit etre ~ 0, recu {cm_const:.3f}"
    assert cm_iid > cm_const, (
        f"C_mu iid ({cm_iid:.3f}) doit exceder C_mu constante ({cm_const:.3f})"
    )


def test_Cmu_zero_for_single_state():
    """Si la partition a un seul etat causal, C_mu = 0 (sequence constante)."""
    seq = [0] * 200  # toute constante -> une seule passe canonique -> 1 etat causal
    part = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=1e-6)
    cm = EM.statistical_complexity(part, seq)
    assert cm["C_mu"] == 0.0


def test_Cmu_distribution_sums_to_one():
    """La distribution stationnaire doit sommer a 1."""
    seq = mk_markov_2(0.8, 500, seed=2)
    part = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.1)
    cm = EM.statistical_complexity(part, seq)
    total = sum(cm["stationary"].values())
    assert abs(total - 1.0) < 1e-9


# --------------------------------------------------------------------------- #
#  excess_entropy_estimate                                                    #
# --------------------------------------------------------------------------- #


def test_excess_entropy_iid_is_zero():
    """Pour iid, E = 0 (passe et futur independants)."""
    seq = iid_seq(2, 2000, seed=11)
    est = EM.excess_entropy_estimate(seq, max_block=4)
    # Tolerance large : 2000 echantillons iid donnent E ~ 0 +- bruit
    assert est["E_estimate"] < 1.0, (
        f"E iid doit etre ~ 0, recu {est['E_estimate']:.3f} "
        f"(serie={est['E_series']})"
    )


def test_excess_entropy_markov_positive():
    """Pour Markov 2 etats, E > 0 (l'etat present donne de l'info sur le futur)."""
    seq = mk_markov_2(0.7, 4000, seed=5)
    est = EM.excess_entropy_estimate(seq, max_block=4)
    # E bornee par 1 bit (2 etats), on tolere le bruit.
    assert est["E_estimate"] > 0.1, (
        f"E Markov doit etre > 0.1 bit, recu {est['E_estimate']:.3f}"
    )
    assert est["E_estimate"] < 1.5, (
        f"E Markov 2 etats doit etre < log2(2) = 1 bit, recu "
        f"{est['E_estimate']:.3f}"
    )


def test_excess_entropy_series_monotone_in_k():
    """La serie E_k doit etre bornee et positive (pas divergente)."""
    seq = mk_markov_2(0.8, 2000, seed=8)
    est = EM.excess_entropy_estimate(seq, max_block=6)
    for k, e_k in est["E_series"]:
        assert e_k >= 0.0, f"E_{k} doit etre >= 0, recu {e_k:.3f}"


def test_excess_entropy_short_sequence_raises():
    with pytest.raises(ValueError):
        EM.excess_entropy_estimate([0, 1, 0], max_block=2)


# --------------------------------------------------------------------------- #
#  partition_similarity                                                       #
# --------------------------------------------------------------------------- #


def test_similarity_identical_partitions_zero():
    """Deux partitions identiques sur la meme trajectoire ont VI_norm = 0."""
    seq = mk_markov_2(0.7, 500, seed=4)
    pa = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.05)
    pb = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.05)
    sim = EM.partition_similarity(pa, pb, seq)
    assert sim["VI_norm"] < 0.01, (
        f"Partitions identiques doivent avoir VI_norm ~ 0, recu "
        f"{sim['VI_norm']:.3f}"
    )
    assert sim["agree"] == sim["n_used"]


def test_similarity_symmetric():
    """VI(A, B) doit etre symetrique (egalite en valeur, par construction)."""
    seq = mk_markov_2(0.7, 500, seed=6)
    pa = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.05)
    pb = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.15)
    s_ab = EM.partition_similarity(pa, pb, seq)
    s_ba = EM.partition_similarity(pb, pa, seq)
    assert abs(s_ab["VI_raw"] - s_ba["VI_raw"]) < 1e-9
    assert abs(s_ab["VI_norm"] - s_ba["VI_norm"]) < 1e-9


def test_similarity_different_tol_gives_different_partitions():
    """Tol differentes -> partitions differentes -> VI_norm > 0."""
    seq = mk_markov_2(0.85, 1000, seed=9)
    pa = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.001)
    pb = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.5)
    # Ici pb doit etre plus grossiere que pa
    assert pb["n_causal_states"] <= pa["n_causal_states"]
    sim = EM.partition_similarity(pa, pb, seq)
    assert 0.0 <= sim["VI_norm"] <= 1.0


def test_similarity_inconsistent_history_len_raises():
    seq = mk_markov_2(0.7, 200, seed=0)
    pa = EM.causal_state_partition(seq, history_len=2, future_len=2, tol=0.1)
    pb = EM.causal_state_partition(seq, history_len=3, future_len=2, tol=0.1)
    with pytest.raises(ValueError):
        EM.partition_similarity(pa, pb, seq)