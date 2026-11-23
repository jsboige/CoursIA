"""Contrôles des groupes de frise et de rosace sur des motifs asymétriques."""

import importlib.util
import math
from pathlib import Path

import pytest

PATH = (Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks" / "GenAI"
        / "Image" / "05-History" / "symmetry_art.py")
spec = importlib.util.spec_from_file_location("symmetry_art", PATH)
art = importlib.util.module_from_spec(spec)
spec.loader.exec_module(art)

MOTIF = [[(0.13, 0.21), (0.27, 0.43), (0.34, 0.19)]]


@pytest.mark.parametrize("group", list(art.FRIEZE_OPERATIONS))
def test_frieze_operations_form_a_group_modulo_translation(group):
    operations = art.FRIEZE_OPERATIONS[group]
    assert len(set(operations)) == len(operations)
    assert (1, 1, 0) in operations
    for sx, sy, dx in operations:
        for tx, ty, ex in operations:
            assert (sx * tx, sy * ty, (sx * ex + dx) % 1) in operations


def test_seven_distinct_frieze_groups_and_periodic_motif():
    signatures = {frozenset(ops) for ops in art.FRIEZE_OPERATIONS.values()}
    assert len(signatures) == 7
    for name, ops in art.FRIEZE_OPERATIONS.items():
        strokes = art.frieze(MOTIF, name, periods=2)
        assert len(strokes) == 2 * len(ops)
        for first, second in zip(strokes[:len(ops)], strokes[len(ops):]):
            for (x, y), (xx, yy) in zip(first, second):
                assert xx == pytest.approx(x + 1)
                assert yy == pytest.approx(y)


def test_each_frieze_has_its_defining_symmetries():
    operations = {name: set(ops) for name, ops in art.FRIEZE_OPERATIONS.items()}
    vertical = (-1, 1, 0)
    horizontal = (1, -1, 0)
    glide = (1, -1, 0.5)
    half_turn = (-1, -1, 0)
    assert {n for n, ops in operations.items() if vertical in ops} == {"p1m1", "p2mg", "p2mm"}
    assert {n for n, ops in operations.items() if horizontal in ops} == {"p11m", "p2mm"}
    assert {n for n, ops in operations.items() if glide in ops} == {"p11g", "p2mg"}
    assert half_turn in operations["p2"]


@pytest.mark.parametrize("order", [1, 2, 5, 8])
def test_rosettes_are_rotation_invariant_and_dihedral_adds_reflections(order):
    cyclic = art.rosette(MOTIF, order)
    dihedral = art.rosette(MOTIF, order, reflections=True)
    assert len(cyclic) == order
    assert len(dihedral) == 2 * order
    angle = 2 * math.pi / order
    for k, stroke in enumerate(cyclic):
        next_stroke = cyclic[(k + 1) % order]
        for (x, y), (xx, yy) in zip(stroke, next_stroke):
            assert xx == pytest.approx(math.cos(angle) * x - math.sin(angle) * y)
            assert yy == pytest.approx(math.sin(angle) * x + math.cos(angle) * y)
    assert dihedral[1][0] == pytest.approx((MOTIF[0][0][0], -MOTIF[0][0][1]))


@pytest.mark.parametrize("bad", [0, -1, 1.5, True])
def test_invalid_orders_and_periods_are_rejected(bad):
    with pytest.raises(ValueError):
        art.rosette(MOTIF, bad)
    with pytest.raises(ValueError):
        art.frieze(MOTIF, "p1", bad)


def test_unknown_frieze_group_is_rejected():
    with pytest.raises(ValueError):
        art.frieze(MOTIF, "p4")


def test_gallery_draws_all_groups():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = art.gallery()
    try:
        fig.canvas.draw()
        assert [ax.get_title(loc="left") for ax in fig.axes] == [
            *art.FRIEZE_OPERATIONS, "C5", "D5"
        ]
        assert all(ax.lines for ax in fig.axes)
    finally:
        plt.close(fig)
