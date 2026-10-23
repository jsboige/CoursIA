"""Tests for scripts/notebook_tools/knot_diagram.py — issue #21908.

Le critere central est la **validite geometrique** : pour chaque PD-code de
reference, la projection reconstruite ne contient aucune intersection hors des
croisements declares (``geometric_crossings == 0``). C'est ce que la section 6.1
de KNOTS-02 exigera d'une figure presentee comme « diagramme de nœud ».
"""

import matplotlib

matplotlib.use("Agg")

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import importlib

kd = importlib.import_module("knot_diagram")

import numpy as np
import pytest

EXAMPLES = sorted(kd.EXAMPLE_PD.items())

# V - E + F = 1 + C : faces attendues par nom (mesure, spherogram 2.4.1)
EXPECTED_FACES = {"3_1": 5, "4_1": 6, "5_2": 7, "K11n34": 13}


# ---------------------------------------------------------------------------
# PD-code : occurrences et refus explicites
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_every_edge_appears_exactly_twice(name, pd):
    occ = kd.edge_occurrences(pd)
    for e, (d0, d1) in occ.items():
        assert d0[0] != d1[0], f"{name}: arete {e} en kink"
        assert sum(1 for quad in pd for x in quad if x == e) == 2


def test_edge_appearing_once_is_rejected():
    # arete 7 jamais reutilisee
    with pytest.raises(kd.PDCodeError, match="presente 1 fois"):
        kd.edge_occurrences([(5, 2, 0, 3), (3, 0, 4, 1), (1, 4, 2, 7)])


def test_kink_reidemeister_i_is_rejected():
    # arete 0 aux deux positions 0 et 2 du meme croisement : kink a une arete
    with pytest.raises(kd.PDCodeError, match="Reidemeister"):
        kd.edge_occurrences([(0, 1, 0, 1)])


def test_quad_of_wrong_arity_is_rejected():
    with pytest.raises(kd.PDCodeError, match="4 aretes"):
        kd.edge_occurrences([(1, 2, 3), (3, 0, 4, 1)])


# ---------------------------------------------------------------------------
# Faces et planarite du systeme de rotation
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_face_counts_match_euler(name, pd):
    faces, occ = kd.pd_faces(pd)
    assert len(faces) == EXPECTED_FACES[name]
    comps = kd.check_euler(pd)
    assert len(comps) == 1, f"{name}: diagramme attendu connexe"
    assert len(pd) - len(occ) + len(faces) == 2


def test_non_planar_rotation_system_is_rejected():
    # systeme incoherent : la permutation ne boucle pas sur des faces planes
    # (aretes croisees deux a deux entre 4 croisements => chi != 2)
    bad = [(7, 4, 0, 5), (3, 0, 4, 1), (1, 7, 2, 6), (5, 2, 6, 3)]
    # 4_1 avec les deux dernieres aretes de 6 echangees : plus de couplage valide
    with pytest.raises((kd.PDCodeError, ValueError)):
        kd.build_diagram(bad)


# ---------------------------------------------------------------------------
# Layout et arcs
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_positions_finite_and_distinct(name, pd):
    pos = kd.layout_crossings(pd)
    assert pos.shape == (len(pd), 2)
    assert np.all(np.isfinite(pos))
    assert len({tuple(np.round(p, 9)) for p in pos}) == len(pd)


@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_bezier_hits_both_endpoints(name, pd):
    pos = kd.layout_crossings(pd)
    _, occ = kd.pd_faces(pd)
    ctrl = kd.edge_control_points(pos, occ)
    e = sorted(occ)[0]
    pts = kd.bezier(pos[occ[e][0][0]], ctrl[e], pos[occ[e][1][0]], samples=30)
    assert np.allclose(pts[0], pos[occ[e][0][0]])
    assert np.allclose(pts[-1], pos[occ[e][1][0]])


# ---------------------------------------------------------------------------
# Validite geometrique — le critere d'acceptation de l'issue
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_projection_has_no_undeclared_crossing(name, pd):
    diagram = kd.build_diagram(pd)
    assert diagram.geometric_crossings == 0, (
        f"{name}: la figure contient {diagram.geometric_crossings} intersection(s) "
        "hors croisements declares — ce n'est pas une projection du PD-code"
    )
    assert diagram.is_valid_projection
    assert diagram.crossing_count == len(pd)


@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_crossing_info_under_over_pairs(name, pd):
    diagram = kd.build_diagram(pd)
    for ci, quad in enumerate(pd):
        info = diagram.crossings[ci]
        assert set(info.under) == {quad[0], quad[2]}, "brin sous = positions 0 et 2"
        assert set(info.over) == {quad[1], quad[3]}, "brin sur = positions 1 et 3"


# ---------------------------------------------------------------------------
# Primitives geometriques — temoin positif oblige (un test muet ne prouve rien)
# ---------------------------------------------------------------------------

def test_segments_intersect_crossing_pair_is_true():
    a0, a1 = np.array([0.0, 0.0]), np.array([1.0, 1.0])
    b0, b1 = np.array([0.0, 1.0]), np.array([1.0, 0.0])
    assert kd.segments_intersect(a0, a1, b0, b1) is True


def test_segments_intersect_disjoint_pair_is_false():
    a0, a1 = np.array([0.0, 0.0]), np.array([1.0, 0.0])
    b0, b1 = np.array([0.0, 1.0]), np.array([1.0, 1.0])
    assert kd.segments_intersect(a0, a1, b0, b1) is False


def test_segments_intersect_endpoint_touch_is_false():
    # contact d'extremite (deux arcs se rejoignant a un croisement) : pas une intersection
    a0, a1 = np.array([0.0, 0.0]), np.array([1.0, 0.0])
    b0, b1 = np.array([1.0, 0.0]), np.array([2.0, 1.0])
    assert kd.segments_intersect(a0, a1, b0, b1) is False


# ---------------------------------------------------------------------------
# Rendu matplotlib (Agg) et CLI
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("name,pd", EXAMPLES)
def test_draw_diagram_adds_base_and_over_strands(name, pd):
    import matplotlib.pyplot as plt

    diagram = kd.build_diagram(pd, samples=24)
    _, occ = kd.pd_faces(pd)
    fig, ax = plt.subplots()
    try:
        kd.draw_diagram(diagram, ax=ax)
        # E arcs de base + 2 troncons halo par croisement (le brin sur, de part et d'autre)
        assert len(ax.lines) == len(occ) + 2 * len(pd)
    finally:
        plt.close(fig)


def test_cli_check_only_returns_zero():
    assert kd.main(["--name", "3_1", "--check-only"]) == 0


def test_cli_list_pd_prints_examples(capsys):
    assert kd.main(["--list-pd"]) == 0
    out = capsys.readouterr().out
    for name in kd.EXAMPLE_PD:
        assert name in out
