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


# --- Contrats supplementaires : branches et cibles non couvertes ---


def test_record_false_reaches_fixed_point_without_per_step_snapshots():
    """run(record=False) suit un chemin de code separe (pas d'appel a step(),
    donc pas de snapshot par pas) : il n'enregistre que l'etat final. Doit
    quand meme atteindre le point fixe (tri + aucun mouvement), mais la sonde
    ne contient que l'instantane initial + le final -- jamais la trajectoire
    pas-a-pas. Contraste avec record=True qui accumule un instantane par pas."""
    vals, algos = _value_classes(6, 4, seed=2)
    a = KinSortingArray(vals, algotypes=algos, seed=2, kin_affinity=True).run(record=False)
    assert a.values == sorted(vals)          # tri preserve malgre l'absence de snapshots par pas
    assert a.has_move() is False             # point fixe atteint (ni tri ni kin)
    assert len(a.probe.values) == 2          # initial + final seulement
    # Contraste : record=True accumule un instantane par pas (init + un par step).
    b = KinSortingArray(vals, algotypes=algos, seed=2, kin_affinity=True).run()
    assert len(b.probe.values) == b.steps + 1
    assert len(b.probe.values) > 2


def test_max_steps_caps_run_before_convergence():
    """max_steps plafonne le nombre d'activations : sur un grand tableau non
    trie, run(max_steps=5) s'arrete au bout d'exactement 5 pas sans avoir
    converge (has_move encore vrai) -- c'est le plafond, pas le point fixe,
    qui arrete la dynamique."""
    for s in range(5):
        v = random.Random(s).sample(range(24), 24)
        algos = _alternating(24)
        a = KinSortingArray(v, algotypes=algos, seed=s,
                            kin_affinity=False).run(max_steps=5)
        assert a.steps == 5                  # plafond atteint exactement
        assert a.has_move() is True          # 5 pas ne suffisent pas a trier 24 elements


def test_has_move_false_at_fixed_point():
    """Au point fixe, has_move() est False (ni tri ni kin) -- c'est la condition
    d'arret de run(). Les tests existants verifier values==sorted ; celui-ci
    verifie directement le signal d'inactivite du systeme converge."""
    for s in range(5):
        vals, algos = _value_classes(6, 4, seed=s)
        a = KinSortingArray(vals, algotypes=algos, seed=s, kin_affinity=True).run()
        assert a.has_move() is False


def test_all_frozen_is_inert():
    """Un tableau entierement gele est inerte : aucune cellule ne peut agir.
    has_move()==False, step()==False (retour anticipe avant tout increment),
    run() est un no-op (0 pas), valeurs inchangees, et la sonde ne contient
    que l'instantane initial."""
    vals = [3, 1, 2, 1]
    algos = ["bubble", "insertion", "bubble", "insertion"]
    frozen = [True, True, True, True]
    a = KinSortingArray(vals, algotypes=algos, frozen=frozen, seed=0)
    assert a.has_move() is False
    assert a.step() is False                 # retour anticipe, pas de step/snapshot
    a.run()
    assert a.steps == 0
    assert a.values == vals                  # rien n'a bouge
    assert len(a.probe.values) == 1          # instantane initial seulement


def test_bidirectional_false_disables_repair():
    """Le drapeau bidirectional=False desactive la reparation par second voisin
    dans KinSortingArray lui-meme : sur l'alternance d'algotypes (impasse
    chimerique), le tri echoue au moins parfois. Mirroir direct de
    test_bidirectional_cures_chimeric_deadlock, mais isole le drapeau sur la
    classe KinSortingArray (pas seulement le constat que SelfSortingArray cale)."""
    n = 20
    failed = 0
    for s in range(20):
        v = random.Random(s).sample(range(n), n)
        algos = _alternating(n)
        a = KinSortingArray(v, algotypes=algos, seed=s,
                            bidirectional=False, kin_affinity=False).run()
        if a.values != sorted(v):
            failed += 1
    assert failed > 0                        # sans reparation, l'impasse chimerique persiste


def test_targeting_helpers_and_frozen_exclusion():
    """Contrats des fonctions de ciblage, testes directement (white-box) :
    _sort_target localise une inversion selon la direction primaire de
    l'algotype ; _kin_adjacency (static) compte les paires adjacentes de meme
    algotype ; _kin_target exclut un voisin gele meme s'il a la meme valeur."""
    # _sort_target : bubble regarde a droite, insertion a gauche.
    a = KinSortingArray([2, 1], algotypes=["bubble", "insertion"], seed=0)
    assert a._sort_target(0) == 1            # bubble, 2 > 1 -> voisin de droite
    assert a._sort_target(1) == 0            # insertion, 1 < 2 -> voisin de gauche
    # _kin_adjacency (static) compte les paires adjacentes de meme algotype.
    assert KinSortingArray._kin_adjacency(["bubble", "bubble", "insertion", "insertion"]) == 2
    assert KinSortingArray._kin_adjacency(["bubble", "insertion", "bubble"]) == 0
    # _kin_target : voisin gele exclu meme s'il a la meme valeur.
    b = KinSortingArray([1, 1, 1], algotypes=["insertion", "bubble", "insertion"],
                        frozen=[True, False, False], seed=0)
    # cellule 1 (bubble, valeur 1) : le voisin 0 est gele -> exclu ; le voisin 2
    # est sain, de valeur egale, et l'echange augmente l'agregation -> seul candidat.
    assert b._kin_target(1) == 2
