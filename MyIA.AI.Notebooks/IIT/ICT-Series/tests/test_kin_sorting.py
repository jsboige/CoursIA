"""Tests du modele a regles enrichies (reparation bidirectionnelle + affinite
kin) introduit dans ICT-4. Stdlib only + pytest."""

import os
import random
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.kin_sorting import KinSortingArray  # noqa: E402
from ict.self_sorting import SelfSortingArray, ALGOTYPES  # noqa: E402
from ict import sorting_metrics as m  # noqa: E402


def _alternating(n):
    return [ALGOTYPES[i % 2] for i in range(n)]


def _value_classes(n_classes, copies, seed=0):
    r = random.Random(seed)
    vals = [c for c in range(n_classes) for _ in range(copies)]
    algos = [ALGOTYPES[r.randint(0, 1)] for _ in vals]
    idx = list(range(len(vals)))
    r.shuffle(idx)
    return [vals[i] for i in idx], [algos[i] for i in idx]


def _sorted_mixed(n_classes, copies, seed=0):
    r = random.Random(seed)
    vals = [c for c in range(n_classes) for _ in range(copies)]
    algos = [ALGOTYPES[r.randint(0, 1)] for _ in vals]
    return vals, algos


def test_bidirectional_cures_chimeric_deadlock():
    # le modele minimal cale sur l'alternance ; la reparation bidirectionnelle trie.
    n = 20
    minimal_failed = bidir_failed = 0
    for s in range(20):
        v = random.Random(s).sample(range(n), n)
        algos = _alternating(n)
        if SelfSortingArray(v, algotypes=algos, seed=s).run().values != sorted(v):
            minimal_failed += 1
        if KinSortingArray(v, algotypes=algos, seed=s, kin_affinity=False).run().values != sorted(v):
            bidir_failed += 1
    assert minimal_failed > 0          # le minimal cale au moins parfois (en realite : souvent)
    assert bidir_failed == 0           # la reparation bidirectionnelle trie toujours


def test_kin_affinity_increases_aggregation():
    # sur des tableaux a valeurs repetees, l'elan kin augmente l'agregation.
    on, off = [], []
    for s in range(8):
        vals, algos = _value_classes(6, 4, seed=s)
        a = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=True).run()
        b = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=False).run()
        assert a.values == sorted(vals) and b.values == sorted(vals)   # tri preserve
        on.append(m.aggregation_index(a.algotypes))
        off.append(m.aggregation_index(b.algotypes))
    assert sum(on) / len(on) > sum(off) / len(off) + 0.1


def test_kin_only_from_sorted_is_monotone():
    # depart deja trie par valeur : seuls les mouvements kin operent -> montee monotone.
    vals, algos = _sorted_mixed(6, 4, seed=1)
    arr = KinSortingArray(vals, algotypes=algos, seed=1, kin_affinity=True).run()
    curve = m.aggregation_curve(arr.probe.algotypes)
    assert arr.values == sorted(vals)
    assert all(b >= a - 1e-9 for a, b in zip(curve, curve[1:]))        # non decroissante
    assert curve[-1] > curve[0]


def test_no_freedom_no_aggregation():
    # valeurs toutes distinctes (copies=1) : aucun degre de liberte -> kin sans effet.
    for s in range(5):
        vals, algos = _value_classes(24, 1, seed=s)
        a = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=True).run()
        b = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=False).run()
        assert a.values == sorted(vals)
        assert abs(m.aggregation_index(a.algotypes) - m.aggregation_index(b.algotypes)) < 1e-9


def test_repulsion_segregates():
    # kin_sign=-1 : repulsion -> agregation negative, tri toujours preserve.
    rep, neutral = [], []
    for s in range(8):
        vals, algos = _value_classes(6, 4, seed=s)
        c = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=True, kin_sign=-1).run()
        n0 = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=False).run()
        assert c.values == sorted(vals)
        rep.append(m.aggregation_index(c.algotypes))
        neutral.append(m.aggregation_index(n0.algotypes))
    assert sum(rep) / len(rep) < sum(neutral) / len(neutral) - 0.1


def test_kin_sign_validation():
    with pytest.raises(ValueError):
        KinSortingArray([1, 2, 3], kin_sign=0)
