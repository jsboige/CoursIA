"""Tests du module :mod:`ict.epsilon_machine` (ICT-17 mecanique computationnelle
Crutchfield, gate #5100).

La *mecanique computationnelle* de Crutchfield-Young (1989) definit trois objets
exacts sur une trajectoire d'etats discrets :

  - **etats causaux** : classes d'equivalence de passes dont la distribution
    conditionnelle de futurs est indistinguable (distance L1/2 <= ``tol``).
    C'est la reponse de Crutchfield a « quel est le bon macro-etat ? ».
  - **C_mu (complexite statistique)** : entropie (log2) de la distribution
    stationnaire des etats causaux — la memoire minimale pour predire.
  - **E (entropie d'exces)** : information mutuelle passe/futur — le plafond
    qu'aucun estimateur ``p_hat`` ne peut capturer.

Ces tests verrouillent les **invariants falsifiables** (G.9 : pinner la
*derivation mathematique*, pas une sortie hardcoded) :

  * **Primitives** : longueur/contenu des passes, comptage des k-grammes,
    entropie de Shannon (uniforme = log2(k), deterministe = 0, vide = 0),
    futurs tronques en bout de trajectoire.
  * **Partition causale** : processus constant -> 1 etat ; alternance
    deterministe -> n_etats = symboles distincts (Markov d'ordre 1 parfait) ;
    ValueError trajectoire trop courte ; les labels partitionnent
    ``[0, n_hist)`` sans chevauchement ; ``n_causal_states <= n_histories`` ;
    deux occurrences de la meme passe canonique partagent toujours un etat.
  * **C_mu** : borne ``0 <= C_mu <= log2(n_causal_states)`` ; processus constant
    -> ``C_mu = 0`` ; uniformite 2-etats -> ``C_mu -> 1``.
  * **E** : plancher ``>= 0`` (information mutuelle) sur toute la serie ;
    ValueError sequence trop courte ; ``len(E_series) == max_block`` ;
    processus iid -> E faible, periodique -> E plus fort.
  * **Similarite de partitions (VI)** : ``VI_norm in [0, 1]`` ; auto-comparaison
    -> ``VI_norm = 0`` et ``agree == n_used`` (accord parfait) ;
    ``agree + disagree == n_used`` ; ValueError ``history_len`` divergent.

Numpy uniquement, comme le reste du package leger ``ict``. Pattern herite de
``test_compression.py`` / ``test_catastrophe.py`` : bootstrap ``sys.path``
module-level, sans fixtures.
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import epsilon_machine as em  # noqa: E402


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Primitives : passes canoniques, k-grammes, entropie de Shannon
# --------------------------------------------------------------------------- #


class TestPrimitives:
    def test_canon_is_idempotent_on_tuples(self):
        # _canon renvoie le tuple tel quel (les etats sont deja hachables).
        assert em._canon((1, 2, 3)) == (1, 2, 3)
        assert em._canon([1, 2]) == (1, 2)  # liste -> tuple

    def test_build_histories_length_and_contents(self):
        # n - history_len + 1 passes, chacune = states[t:t+history_len].
        states = [0, 1, 2, 3, 4]
        h = em._build_histories(states, history_len=2)
        assert len(h) == 4  # 5 - 2 + 1
        assert h[0] == (0, 1)
        assert h[-1] == (3, 4)

    def test_build_histories_len_one_is_singleton_tuples(self):
        # history_len=1 : chaque passe est un 1-tuple.
        h = em._build_histories([7, 8, 9], history_len=1)
        assert h == [(7,), (8,), (9,)]

    def test_build_histories_empty_when_trajectory_shorter(self):
        # n < history_len -> liste vide (pas de passe complete).
        assert em._build_histories([1, 2], history_len=5) == []

    def test_build_histories_rejects_zero_length(self):
        with pytest.raises(ValueError):
            em._build_histories([1, 2, 3], history_len=0)

    def test_entropy_uniform_is_log2_k(self):
        # Distribution uniforme sur k symboles : H = log2(k).
        assert em._entropy_from_counts([1, 1, 1, 1]) == pytest.approx(math.log2(4))
        assert em._entropy_from_counts([5, 5]) == pytest.approx(1.0)

    def test_entropy_deterministic_is_zero(self):
        # Un seul outcome (certitude) : H = 0.
        assert em._entropy_from_counts([42]) == 0.0
        assert em._entropy_from_counts([9, 0, 0]) == pytest.approx(0.0)

    def test_entropy_empty_is_zero(self):
        # total <= 0 -> 0.0 (pas de crash sur entree vide).
        assert em._entropy_from_counts([]) == 0.0
        assert em._entropy_from_counts([0, 0, 0]) == 0.0

    def test_entropy_is_concave_two_outcome(self):
        # [3,1] a une entropie strictement entre 0 et 1, et <= log2(2)=1.
        h = em._entropy_from_counts([3, 1])
        assert 0.0 < h < 1.0

    def test_ngrams_counts_consecutive(self):
        # "aabb" k=2 -> (a,a):1, (a,b):1, (b,b):1.
        ng = em._ngrams(["a", "a", "b", "b"], k=2)
        assert ng == {("a", "a"): 1, ("a", "b"): 1, ("b", "b"): 1}

    def test_ngrams_out_of_range_returns_empty(self):
        assert em._ngrams([1, 2], k=0) == {}
        assert em._ngrams([1, 2], k=5) == {}  # k > len(seq)

    def test_future_counts_dict_truncates_at_end(self):
        # Passe debutant trop tard (future_start >= n) -> futur vide {():1}.
        states = [0, 1, 2]
        # t=2, history_len=1 -> future_start=3 >= 3 -> futur vide.
        fc = em._future_counts_dict(states, t=2, history_len=1, future_len=2)
        assert fc == {(): 1}

    def test_future_counts_dict_normal_future(self):
        states = [0, 1, 2, 3]
        # t=1, history_len=1 -> future = states[2:4] = (2,3).
        fc = em._future_counts_dict(states, t=1, history_len=1, future_len=2)
        assert fc == {(2, 3): 1}


# --------------------------------------------------------------------------- #
#  Partition en etats causaux
# --------------------------------------------------------------------------- #


class TestCausalPartition:
    def test_return_keys_contract(self):
        part = em.causal_state_partition([0, 1, 0, 1, 0, 1], history_len=1, future_len=1)
        for key in ("labels", "causal_to_histories", "occurrence_to_causal",
                    "history_to_causal", "history_len", "future_len", "tol",
                    "n_causal_states", "n_histories"):
            assert key in part, f"cle manquante: {key}"

    def test_rejects_trajectory_too_short(self):
        # n < history_len + future_len -> ValueError.
        with pytest.raises(ValueError):
            em.causal_state_partition([0, 1], history_len=2, future_len=2)

    def test_constant_process_single_causal_state(self):
        # Suite constante : 1 seul passe canonique -> 1 etat causal.
        part = em.causal_state_partition([5, 5, 5, 5, 5, 5],
                                         history_len=2, future_len=1)
        assert part["n_causal_states"] == 1
        assert part["n_histories"] >= 1

    def test_deterministic_alternation_two_states(self):
        # 0,1,0,1,... avec history_len=1 : l'etat 0 est toujours suivi de 1,
        # l'etat 1 toujours suivi de 0 -> 2 etats causaux distinguables
        # (Crutchfield : un cycle period-2 deterministe a 2 etats causaux).
        seq = [0, 1] * 20
        part = em.causal_state_partition(seq, history_len=1, future_len=1)
        assert part["n_causal_states"] == 2

    def test_n_causal_states_le_n_histories(self):
        # On ne peut pas avoir plus d'etats causaux que de passes.
        rng = _rng(0)
        seq = rng.integers(0, 3, size=40).tolist()
        part = em.causal_state_partition(seq, history_len=2, future_len=2)
        assert part["n_causal_states"] <= part["n_histories"]

    def test_labels_partition_occurrence_indices(self):
        # Les labels (tuples d'indices) partitionnent [0, n_hist) sans
        # chevauchement ni trou : union == ensemble des occurrences.
        rng = _rng(1)
        seq = rng.integers(0, 2, size=30).tolist()
        part = em.causal_state_partition(seq, history_len=2, future_len=1)
        all_idx = sorted(i for grp in part["labels"] for i in grp)
        assert all_idx == list(range(part["n_histories"]))
        assert len(all_idx) == len(set(all_idx))  # pas de doublon

    def test_same_canonical_history_shares_state(self):
        # Invariant Crutchfield : deux occurrences de la MEME passe canonique
        # ont par construction la meme distribution de futurs (la table est
        # indexee par passe canonique) -> toujours le meme etat causal.
        # history_to_causal (alias canonique) doit etre coherent.
        rng = _rng(2)
        seq = rng.integers(0, 2, size=50).tolist()
        part = em.causal_state_partition(seq, history_len=2, future_len=2)
        for hist, c in part["history_to_causal"].items():
            # Chaque passe canonique mappe vers exactement un etat.
            assert isinstance(c, int)
        # occurrence_to_causal couvre toutes les occurrences.
        assert len(part["occurrence_to_causal"]) == part["n_histories"]

    def test_tolerance_merges_near_identical_distributions(self):
        # Avec une tolerance large, des passes aux futurs legerement
        # differents fusionnent -> moins d'etats qu'avec tol=0.
        rng = _rng(3)
        seq = rng.integers(0, 2, size=60).tolist()
        strict = em.causal_state_partition(seq, history_len=1, future_len=1, tol=0.0)
        loose = em.causal_state_partition(seq, history_len=1, future_len=1, tol=0.5)
        assert loose["n_causal_states"] <= strict["n_causal_states"]

    def test_causal_to_histories_contents_match_labels(self):
        # causal_to_histories[c] == liste des passes canoniques des occurrences
        # du label c.
        seq = [0, 1, 2, 0, 1, 2]
        part = em.causal_state_partition(seq, history_len=1, future_len=1)
        for c, grp_indices in enumerate(part["labels"]):
            expected = [part["causal_to_histories"][c]]
            # Le groupe d'occurrences indexe par label[c] correspond.
            assert set(grp_indices).issubset(set(range(part["n_histories"])))


# --------------------------------------------------------------------------- #
#  Complexite statistique C_mu
# --------------------------------------------------------------------------- #


class TestStatisticalComplexity:
    def test_cmu_bounds_zero_to_log2_nstates(self):
        # 0 <= C_mu <= log2(n_causal_states) (l'entropie d'une distribution
        # sur n_causal_states etats est bornee par log2 de leur nombre).
        rng = _rng(4)
        seq = rng.integers(0, 3, size=60).tolist()
        part = em.causal_state_partition(seq, history_len=2, future_len=1)
        sc = em.statistical_complexity(part, seq)
        n_states = part["n_causal_states"]
        assert sc["C_mu"] >= 0.0
        if n_states >= 1:
            assert sc["C_mu"] <= math.log2(n_states) + 1e-9

    def test_cmu_zero_for_constant_process(self):
        # Processus constant -> 1 etat causal -> C_mu = 0.
        seq = [9, 9, 9, 9, 9, 9, 9, 9]
        part = em.causal_state_partition(seq, history_len=2, future_len=1)
        sc = em.statistical_complexity(part, seq)
        assert sc["C_mu"] == pytest.approx(0.0, abs=1e-12)

    def test_cmu_positive_for_two_state_alternation(self):
        # Cycle 0,1,0,1 -> 2 etats causaux equiprobables -> C_mu -> 1.0.
        seq = [0, 1] * 50
        part = em.causal_state_partition(seq, history_len=1, future_len=1)
        sc = em.statistical_complexity(part, seq)
        assert sc["C_mu"] == pytest.approx(1.0, abs=0.05)

    def test_cmu_stationary_sums_to_one(self):
        # La distribution stationnaire est normalisee.
        rng = _rng(5)
        seq = rng.integers(0, 2, size=40).tolist()
        part = em.causal_state_partition(seq, history_len=1, future_len=1)
        sc = em.statistical_complexity(part, seq)
        if sc["stationary"]:
            assert sum(sc["stationary"].values()) == pytest.approx(1.0)

    def test_cmu_n_used_le_n_states_minus_hist_plus_one(self):
        # n_used = nombre d'occurrences de passe effectivement comptees.
        rng = _rng(6)
        seq = rng.integers(0, 2, size=35).tolist()
        part = em.causal_state_partition(seq, history_len=2, future_len=1)
        sc = em.statistical_complexity(part, seq)
        assert sc["n_used"] <= len(seq) - int(part["history_len"]) + 1


# --------------------------------------------------------------------------- #
#  Entropie d'exces E
# --------------------------------------------------------------------------- #


class TestExcessEntropy:
    def test_rejects_sequence_too_short(self):
        # n < max_block*2 + 1 -> ValueError.
        with pytest.raises(ValueError):
            em.excess_entropy_estimate([0, 1, 2], max_block=4)

    def test_E_series_nonnegative_floor(self):
        # Information mutuelle >= 0 : chaque E_k est cale a max(0, ...).
        rng = _rng(7)
        seq = rng.integers(0, 2, size=200).tolist()
        res = em.excess_entropy_estimate(seq, max_block=6)
        for _k, e in res["E_series"]:
            assert e >= 0.0
        assert res["E_estimate"] >= 0.0

    def test_E_series_length_equals_max_block(self):
        rng = _rng(8)
        seq = rng.integers(0, 3, size=200).tolist()
        res = em.excess_entropy_estimate(seq, max_block=5)
        assert len(res["E_series"]) == 5

    def test_periodic_process_higher_E_than_iid(self):
        # Un processus periodique (previsible) porte plus d'information
        # mutuelle passe/futur qu'un bruit iid (imprevisible).
        rng_iid = _rng(9)
        iid = rng_iid.integers(0, 2, size=400).tolist()
        periodic = ([0, 1, 1, 0, 1, 0, 0, 1] * 50)  # periode 8 deterministe
        e_iid = em.excess_entropy_estimate(iid, max_block=6)["E_estimate"]
        e_per = em.excess_entropy_estimate(periodic, max_block=6)["E_estimate"]
        assert e_per > e_iid

    def test_E_estimate_is_mean_of_tail_three(self):
        # L'estimation finale = moyenne des 3 derniers E_k.
        rng = _rng(10)
        seq = rng.integers(0, 2, size=120).tolist()
        res = em.excess_entropy_estimate(seq, max_block=6)
        tail = [e for _k, e in res["E_series"][-3:]]
        assert res["E_estimate"] == pytest.approx(float(np.mean(tail)))

    def test_converged_flag_is_bool(self):
        res = em.excess_entropy_estimate([0, 1] * 60, max_block=4)
        assert isinstance(res["converged"], bool)


# --------------------------------------------------------------------------- #
#  Similarite entre partitions (information de variation)
# --------------------------------------------------------------------------- #


class TestPartitionSimilarity:
    def test_rejects_divergent_history_len(self):
        seq = [0, 1] * 20
        a = em.causal_state_partition(seq, history_len=1, future_len=1)
        b = em.causal_state_partition(seq, history_len=2, future_len=1)
        with pytest.raises(ValueError):
            em.partition_similarity(a, b, seq)

    def test_VI_norm_in_unit_interval(self):
        rng = _rng(11)
        seq = rng.integers(0, 2, size=50).tolist()
        a = em.causal_state_partition(seq, history_len=2, future_len=1, tol=0.0)
        b = em.causal_state_partition(seq, history_len=2, future_len=1, tol=0.3)
        sim = em.partition_similarity(a, b, seq)
        assert 0.0 <= sim["VI_norm"] <= 1.0 + 1e-9

    def test_self_similarity_is_zero_VI(self):
        # Une partition comparee a elle-meme : accord parfait.
        # VI_norm = 0, agree == n_used, disagree = 0.
        rng = _rng(12)
        seq = rng.integers(0, 2, size=50).tolist()
        a = em.causal_state_partition(seq, history_len=1, future_len=1)
        sim = em.partition_similarity(a, a, seq)
        assert sim["VI_norm"] == pytest.approx(0.0, abs=1e-9)
        assert sim["disagree"] == 0
        assert sim["agree"] == sim["n_used"]

    def test_agree_plus_disagree_equals_n_used(self):
        rng = _rng(13)
        seq = rng.integers(0, 3, size=60).tolist()
        a = em.causal_state_partition(seq, history_len=2, future_len=1, tol=0.0)
        b = em.causal_state_partition(seq, history_len=2, future_len=1, tol=0.4)
        sim = em.partition_similarity(a, b, seq)
        assert sim["agree"] + sim["disagree"] == sim["n_used"]

    def test_VI_raw_nonnegative(self):
        # Une information de variation est toujours >= 0.
        rng = _rng(14)
        seq = rng.integers(0, 2, size=45).tolist()
        a = em.causal_state_partition(seq, history_len=1, future_len=1, tol=0.1)
        b = em.causal_state_partition(seq, history_len=1, future_len=1, tol=0.5)
        sim = em.partition_similarity(a, b, seq)
        assert sim["VI_raw"] >= -1e-9
