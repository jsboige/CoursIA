#!/usr/bin/env python3
"""Tests unitaires de la validation R3 (knot_r3connected_validation).

Couvre : (1) les ground-truths Lean (wf + tricolorabilite des diagrammes nommes),
(2) la symetrie de Fox (cle de la prediction V4), (3) le verdict V4 du scaffold
Reidemeister3Determined (borne), (4) la reproduction R1 bornee, (5) le theoreme
de reduction (764 partitions, temoin braid classique meme classe Sat + bras),
(6) un echantillon de redistributions concretes, (7) le scenario NEGATIF du
tangle ouvert 2-croisements (decouverte : pas un move d'isotopie), (8) le
triangle R3 3-croisements (exactement 2 bijections a Sat egal, correspondance
interne unique, version geometrique a identite de bord ABSENTE).

Execution : `python scripts/lean/tests/test_knot_r3connected_validation.py`
ou pytest. Les tests lourds sont bornes ; le run complet se fait via le CLI du
script (--perms, --r3search, --concrete).
"""

import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from knot_r3connected_validation import (  # noqa: E402
    P1_TRIANGLE,
    P2_TRIANGLE,
    PDCrossing,
    KnotDiagram,
    V4_PERMS,
    all_partitions_8,
    apply_perm,
    build_groups,
    cond_colors,
    empty_diagram,
    enumerate_wf_diagrams,
    figure_eight_diagram,
    is_tricolorable,
    pair_pattern,
    pattern_sat,
    pattern_sat_set,
    r1_surgeries,
    redistribute,
    sat_isomorphic,
    trefoil_diagram,
    two_twin_crossings,
    var_order,
)


def test_named_diagrams_ground_truths():
    assert empty_diagram().wf()
    assert not is_tricolorable(empty_diagram())
    assert two_twin_crossings().wf()
    assert is_tricolorable(two_twin_crossings())
    assert trefoil_diagram().wf()
    assert is_tricolorable(trefoil_diagram())
    assert figure_eight_diagram().wf()
    assert not is_tricolorable(figure_eight_diagram())


def test_fox_symmetry():
    # Fox est symetrique en ses trois arguments : c'est pourquoi la condition
    # ne depend que de la paire {slot2, slot4} et du triple {slot1..slot3}.
    for c in product(range(3), repeat=3):
        base = cond_colors(c[0], c[1], c[2], c[1])
        for p in __import__("itertools").permutations(range(3)):
            assert cond_colors(c[p[0]], c[p[1]], c[p[2]], c[p[1]]) == base


def test_v4_verdict_bounded():
    # Sur n<=1 (6 diagrammes) : V4 survit integralement (aucun echec).
    diagrams = enumerate_wf_diagrams(1)
    assert len(diagrams) == 6
    for d1 in diagrams:
        for i, c in enumerate(d1.crossings):
            for name, p in V4_PERMS.items():
                d2 = KnotDiagram(
                    tuple(apply_perm(cc, p) if k == i else cc
                          for k, cc in enumerate(d1.crossings)),
                    d1.numEdges,
                )
                assert d2.wf(), (name, d1)
                assert is_tricolorable(d1) == is_tricolorable(d2), (name, d1)
    # Sur un echantillon n<=2 : deux perms hors V4 ont des contre-exemples.
    sample = enumerate_wf_diagrams(2)[:400]
    failing = {p: False for p in ((0, 1, 3, 2), (0, 2, 1, 3))}
    for d1 in sample:
        for i, c in enumerate(d1.crossings):
            for p in failing:
                d2 = KnotDiagram(
                    tuple(apply_perm(cc, p) if k == i else cc
                          for k, cc in enumerate(d1.crossings)),
                    d1.numEdges,
                )
                if is_tricolorable(d1) != is_tricolorable(d2):
                    failing[p] = True
    assert all(failing.values()), failing


def test_r1_reproduction_bounded():
    # n<=1 exact : 6 diagrammes (C(4,2) slots), 4 torsions chacun, 0 echec.
    diagrams = enumerate_wf_diagrams(1)
    total = 0
    for d1 in diagrams:
        for d2, _meta in r1_surgeries(d1):
            total += 1
            assert is_tricolorable(d1) == is_tricolorable(d2)
    assert total == 24


def test_partitions_and_reduction():
    parts = all_partitions_8()
    assert len(parts) == 764
    # Toutes les partitions ont des blocs de taille <= 2 et couvrent 0..7.
    for blocks in parts:
        flat = [p for b in blocks for p in b]
        assert sorted(flat) == list(range(8))
        assert all(len(b) <= 2 for b in blocks)
    # var_order : tailles decroissantes puis position croissante.
    assert var_order(((0,), (1, 2), (3,), (4, 5))) == [(1, 2), (4, 5), (0,), (3,)]


def test_braid_witness_classical():
    # Fermetures sigma1*sigma2 et sigma2*sigma1 (derivation convention brin du
    # dessus en position superieure) : meme classe Sat, bras concrets OK.
    d1 = KnotDiagram((PDCrossing(2, 1, 3, 1), PDCrossing(4, 3, 4, 2)), 4)
    d2 = KnotDiagram((PDCrossing(4, 2, 3, 4), PDCrossing(3, 1, 2, 1)), 4)
    assert d1.wf() and d2.wf()
    assert is_tricolorable(d1) == is_tricolorable(d2) is False
    groups = build_groups()
    p1, p2 = pair_pattern(d1, 0, 1), pair_pattern(d2, 0, 1)
    assert pattern_sat(p1) == pattern_sat(p2)
    bucket = [v for v in groups.values() if p1 in v]
    assert len(bucket) == 1 and p2 in bucket[0]


def test_open_tangle_negative():
    # Tangle ouvert sigma1*sigma2 <-> sigma2*sigma1 (6 arcs de bord + interne
    # g, 2 croisements) : Sat NON egaux -- DECOUVERTE, ce n'est pas un move
    # d'isotopie (le R3 classique est un move a 3 croisements, cf Partie C).
    # Positions 0..7 : sigma1*sigma2 = (b,a,g,a',c,g,c',b'),
    #                 sigma2*sigma1 = (c,b,g,b',g,a,c',a').
    p1 = tuple(sorted([(1,), (3,), (0,), (7,), (4,), (6,), (2, 5)]))
    p2 = tuple(sorted([(5,), (7,), (1,), (3,), (0,), (6,), (2, 4)]))
    assert pattern_sat(p1) != pattern_sat(p2)
    # Garde anti-tautologie : un pattern voisin distinct (meme multi-ensemble
    # de tailles, couverture exacte de 0..7) doit changer Sat.
    p_other = tuple(sorted([(5,), (7,), (1,), (3,), (0,), (4,), (2, 6)]))
    assert pattern_sat(p1) != pattern_sat(p_other)
    assert pattern_sat(p2) != pattern_sat(p_other)


def test_redistribute_concrete_sample():
    # Echantillon borne de redistributions valides sur diagrammes n<=2 : bras OK.
    groups = build_groups()
    partners = {}
    for members in groups.values():
        for a in members:
            partners.setdefault(a, []).extend(b for b in members if b != a)
    checked = 0
    for d1 in enumerate_wf_diagrams(2)[:60]:
        if len(d1.crossings) < 2:
            continue
        p1 = pair_pattern(d1, 0, 1)
        for p2 in partners.get(p1, [])[:20]:
            d2 = redistribute(d1, 0, 1, p1, p2)
            assert d2.wf()
            assert is_tricolorable(d1) == is_tricolorable(d2), (d1, p2, d2)
            checked += 1
    assert checked > 0


def test_triangle_sat_isomorphic():
    # Partie C : les deux triangles ouverts sigma1*sigma2*sigma1 et
    # sigma2*sigma1*sigma2 ont des Sat egaux SOUS bijection preservant les
    # tailles -- c'est le candidat d'enonce Lean Reidemeister3Connected.
    phi = sat_isomorphic(P1_TRIANGLE, P2_TRIANGLE)
    assert phi is not None
    # Garde anti-tautologie : en ordre canonique (sans bijection) les Sat
    # different -- l'isomorphisme est la vraie information geometrique.
    assert pattern_sat_set(P1_TRIANGLE) != pattern_sat_set(P2_TRIANGLE)
    # La bijection respecte les tailles : 6 arcs de bord (singles) et 3 arcs
    # internes (paires) restent dans leurs familles.
    o1 = var_order(P1_TRIANGLE)
    o2 = var_order(P2_TRIANGLE)
    for i, b in enumerate(o1):
        assert len(b) == len(o2[phi[i]])
    # Ground truth exhaustif : EXACTEMENT 2 bijections valides (sur 4320),
    # correspondance interne unique, differant par l'echange {a1, b1}.
    from knot_r3connected_validation import sat_isomorphisms
    phis = list(sat_isomorphisms(P1_TRIANGLE, P2_TRIANGLE))
    assert len(phis) == 2
    internes = {tuple(sorted((i, phis[0][i]))) for i, b in enumerate(o1)
                if len(b) == 2}
    assert all(tuple(sorted((i, p[i]))) in internes for p in phis
               for i, b in enumerate(o1) if len(b) == 2)
    # Et la version geometrique (identite des arcs de bord) est ABSENTE.
    idx1 = {b: i for i, b in enumerate(o1)}
    idx2 = {b: j for j, b in enumerate(o2)}
    geo_border = {"a2": ((0,), (1,)), "a1": ((1,), (5,)), "a3": ((4,), (0,)),
                  "b3": ((7,), (11,)), "b2": ((10,), (10,)), "b1": ((11,), (6,))}
    preset = {idx1[b1]: idx2[b2] for b1, b2 in geo_border.values()}
    assert sat_isomorphic(P1_TRIANGLE, P2_TRIANGLE, preset=preset) is None


if __name__ == "__main__":
    for name, fn in sorted(list(globals().items())):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"PASS {name}")
    print("all tests passed")
