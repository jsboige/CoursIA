#!/usr/bin/env python3
"""Tests unitaires du miroir Python des definitions tricolorabilite knot_lean.

Couvre : (1) les ground-truths Lean (wf + tricolorabilite des diagrammes
nommes), (2) la reproduction du mur R2 libre, (3) la chirurgie R1 courante
(0 echec aux 2 bras), (4) le verdict des candidats R2Connected — v2 REFUTE,
v3 VALIDE.

Execution : `python scripts/lean/tests/test_knot_r2connected_validation.py`
ou pytest. Les tests lourds sont bornes (n<=1, echantillon n<=2) pour rester
rapides ; le run complet se fait via le CLI du script (--reproduce,
--r2connected).
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from knot_r2connected_validation import (  # noqa: E402
    PDCrossing,
    KnotDiagram,
    check_lemmas,
    empty_diagram,
    enumerate_wf_diagrams,
    figure_eight_diagram,
    is_tricolorable,
    r1_extension,
    r1_surgeries,
    r2_extension,
    r2_surgeries_v2,
    r2_surgeries_v3,
    trefoil_diagram,
    two_twin_crossings,
)


def test_ground_truths_wf():
    for d in (empty_diagram(), two_twin_crossings(), trefoil_diagram(),
              figure_eight_diagram()):
        assert d.wf() is True


def test_ground_truths_tricolorability():
    assert is_tricolorable(two_twin_crossings()) is True
    assert is_tricolorable(trefoil_diagram()) is True
    assert is_tricolorable(empty_diagram()) is False
    assert is_tricolorable(figure_eight_diagram()) is False


def test_free_r2_wall():
    # r2_append_only_wall : emptyDiagram --R2 libre--> twoTwinCrossings, la
    # bi-implication du maitre ne tient pas (d2 tri, d1 non tri).
    assert is_tricolorable(two_twin_crossings()) and not is_tricolorable(empty_diagram())


def test_enumeration_count():
    assert len(enumerate_wf_diagrams(2)) == 2526
    assert len(enumerate_wf_diagrams(1)) == 6


def _r1_stats(diagrams, proper_only=False):
    stats = {"total": 0, "fwd": 0, "bwd": 0}
    for d1 in diagrams:
        for d2, meta in r1_surgeries(d1):
            a = meta["a"]
            idxs = [i for i, p in _occ(d1, a)]
            if proper_only and len(set(idxs)) != 2:
                continue
            stats["total"] += 1
            r = check_lemmas(d1, d2, meta, r1_extension)
            stats["fwd"] += 0 if r["fwd_ok"] else 1
            stats["bwd"] += 0 if r["bwd_ok"] else 1
    return stats


def _occ(d1, a):
    from knot_r2connected_validation import _a_occurrences
    return _a_occurrences(d1)[a]


def test_r1_current_surgery_no_failure_n1():
    # n<=1 (6 diagrammes) : aucune torsion R1 ne casse les 2 bras.
    stats = _r1_stats(enumerate_wf_diagrams(1))
    assert stats["fwd"] == 0 and stats["bwd"] == 0


def test_r1_current_surgery_no_failure_n2_sample():
    random.seed(7)
    sample = random.sample(enumerate_wf_diagrams(2), 120)
    stats = _r1_stats(sample)
    assert stats["fwd"] == 0 and stats["bwd"] == 0


def _r2_stats(diagrams, surgery_fn):
    stats = {"total": 0, "fwd": 0, "bwd": 0, "set_bwd": 0}
    for d1 in diagrams:
        for d2, meta in surgery_fn(d1):
            stats["total"] += 1
            r = check_lemmas(d1, d2, meta, r2_extension)
            stats["fwd"] += 0 if r["fwd_ok"] else 1
            if not r["bwd_ok"]:
                stats["bwd"] += 1
                if r["set_bwd"]:
                    stats["set_bwd"] += 1
    return stats


def test_r2_v2_refuted():
    # Le candidat de la proposition #2874 (v2, kinks <a, o, u, o>) est REFUTE :
    # chaque chirurgie cree de la tricolorabilite au bras descendant.
    d1 = KnotDiagram(crossings=(PDCrossing(1, 1, 2, 2),), numEdges=2)
    any_failure = False
    for d2, meta in r2_surgeries_v2(d1):
        r = check_lemmas(d1, d2, meta, r2_extension)
        assert r["fwd_ok"]  # bras avant inconditionnel
        if not r["bwd_ok"]:
            any_failure = True
    assert any_failure


def test_r2_v3_validated_n1():
    # n<=1 : v3 (kinks <a, u, u, o>, all-equal forces) ne casse aucun bras.
    stats = _r2_stats(enumerate_wf_diagrams(1), r2_surgeries_v3)
    assert stats["fwd"] == 0 and stats["bwd"] == 0


def test_r2_v3_validated_n2_sample():
    random.seed(11)
    sample = random.sample(enumerate_wf_diagrams(2), 120)
    stats = _r2_stats(sample, r2_surgeries_v3)
    assert stats["fwd"] == 0 and stats["bwd"] == 0


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
