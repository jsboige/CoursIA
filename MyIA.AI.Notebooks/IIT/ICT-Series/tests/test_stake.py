"""Tests de la batterie ENJEU (module ICT-19 ``ict.stake``).

Verifient les primitives (ancre, kick ``do(.)``, distance, courbe de
recuperation) et surtout la **gate falsifiable ENJEU-1** : un substrat
restaurateur (auto-maintien = agent) donne ``I_stake > 0`` alors qu'un pur
dissipateur (marche biaisee = controle faux-positif S5 d'ICT-18) donne
``I_stake ~= 0``. C'est la decoupe que la paire ``(I_thermo, I_stake)`` opere
et qu'``I_thermo`` seul (ICT-18) ne sait pas faire.

Numpy + pytest. Le module ne depend que de numpy.
"""

import os
import sys

import numpy as np
import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_PARENT = os.path.dirname(_HERE)
if _PARENT not in sys.path:
    sys.path.insert(0, _PARENT)

from ict import stake  # noqa: E402


def test_basin_anchor_mean():
    """L'ancre = moyenne empirique de la trajectoire libre."""
    assert stake.basin_anchor([0.0, 1.0, 2.0, 3.0]) == pytest.approx(1.5)
    assert stake.basin_anchor([-2.0, 2.0]) == pytest.approx(0.0)
    # discrete states : la moyenne marche aussi
    assert stake.basin_anchor([0, 0, 1, 0, 1]) == pytest.approx(0.4)


def test_basin_anchor_empty_raises():
    with pytest.raises(ValueError):
        stake.basin_anchor([])


def test_do_kick_basic():
    """do(x <- x + delta) : addition pure hors bornes."""
    kicked = stake.do_kick(np.array([0.0]), 5.0)
    assert float(kicked[0]) == pytest.approx(5.0)


def test_do_kick_clipped():
    """Le kick respecte l'alphabet fini (clip aux bornes)."""
    kicked = stake.do_kick(np.array([3.0]), 5.0, lo=0.0, hi=4.0)
    assert float(kicked[0]) == pytest.approx(4.0)
    kicked_lo = stake.do_kick(np.array([1.0]), -5.0, lo=0.0, hi=4.0)
    assert float(kicked_lo[0]) == pytest.approx(0.0)


def test_distance_to_anchor_monotone_shape():
    """La distance a l'ancre croit avec l'ecart."""
    traj = np.array([0.0, 1.0, 2.0, 3.0])
    d = stake.distance_to_anchor(traj, anchor=0.0)
    np.testing.assert_allclose(d, np.array([0.0, 1.0, 2.0, 3.0]))


def test_recovery_curve_length_and_start():
    """La courbe de recuperation a ``steps+1`` points et demarre a ``d0``."""
    anchor = 0.0
    kicked = stake.do_kick(np.array([0.0]), 5.0)
    curve = stake.recovery_curve(kicked, lambda s: s * 0.5, steps=10, anchor=anchor)
    assert len(curve) == 11
    # t=0 = distance immediatement apres le kick (avant relaxation)
    assert curve[0] == pytest.approx(5.0)


def test_recovery_curve_restoring_decreases():
    """Un substrat restaurateur : la distance au bassin DECROIT apres le kick."""
    rng = np.random.default_rng(0)
    anchor = 0.0
    kicked = stake.do_kick(np.array([0.0]), 5.0)
    curve = stake.recovery_curve(
        kicked, lambda s: stake.restoring_step(s, 0.5, rng), steps=40, anchor=anchor
    )
    # La distance finale doit etre nettement inferieure a la distance initiale.
    assert curve[-1] < curve[0] * 0.5


def test_recovery_curve_drift_does_not_return():
    """Un pur dissipateur (marche biaisee) : la distance ne decroit pas vers l'ancre."""
    rng = np.random.default_rng(0)
    anchor = 0.0
    kicked = stake.do_kick(np.array([0.0]), 5.0)
    curve = stake.recovery_curve(
        kicked, lambda s: stake.drift_step(s, 0.4, rng), steps=40, anchor=anchor
    )
    # Le biais +0.4 par pas pousse l'etat vers le haut : la distance au bassin
    # (ancre=0) croit, elle ne decroit pas. Pas de retour.
    assert curve[-1] >= curve[0]


def test_stake_index_restoring_positive():
    """Gate ENJEU-1 (partie agent) : restauratrice -> I_stake > 0."""
    rng = np.random.default_rng(42)
    anchor = 0.0
    i = stake.stake_index(
        kicked_state=stake.do_kick(np.array([0.0]), 5.0),
        step_fn=lambda s: stake.restoring_step(s, 0.3, rng),
        steps=50, anchor=anchor,
    )
    assert i > 0.3, f"restauratrice devrait donner I_stake > 0.3, obtenu {i}"


def test_stake_index_drift_near_zero():
    """Gate ENJEU-1 (partie controle faux-positif) : derive -> I_stake ~= 0 ou negatif."""
    rng = np.random.default_rng(7)
    anchor = 0.0
    i = stake.stake_index(
        kicked_state=stake.do_kick(np.array([0.0]), 5.0),
        step_fn=lambda s: stake.drift_step(s, 0.4, rng),
        steps=50, anchor=anchor,
    )
    # Pas de retour : la fraction regagnee est <= 0 (derive eloigne du bassin).
    assert i <= 0.05, f"derive devrait donner I_stake ~= 0 ou negatif, obtenu {i}"


def test_stake_index_discriminates():
    """Gate ENJEU-1 (decoupe) : restauratrice > derive d'une marge claire.

    C'est le coeur falsifiable de la batterie : les deux substrats dissipe, mais
    seul le restaurateur a un enjeu. Si la batterie ne separait pas les deux,
    elle serait inutile (meme porte que I_thermo seul).
    """
    i_r, i_d = stake.demo_contrast(steps=50, seed=42)
    assert i_r - i_d > 0.3, (
        f"la batterie devrait separer restauratrice et derive d'au moins 0.3, "
        f"obtenu I_stake_restoring={i_r:.3f} vs I_stake_drift={i_d:.3f}"
    )


def test_stake_index_zero_kick_returns_zero():
    """Un kick nul (etat deja a l'ancre) -> pas d'enjeu mesurable (0)."""
    i = stake.stake_index(
        kicked_state=np.array([0.0]),
        step_fn=lambda s: stake.restoring_step(s, 0.3, np.random.default_rng(0)),
        steps=10, anchor=0.0,
    )
    assert i == 0.0


def test_stake_index_in_range():
    """I_stake est borne dans [-1, 1] (clip)."""
    rng = np.random.default_rng(1)
    i = stake.stake_index(
        kicked_state=stake.do_kick(np.array([0.0]), 100.0),
        step_fn=lambda s: stake.restoring_step(s, 0.9, rng),
        steps=20, anchor=0.0,
    )
    assert -1.0 <= i <= 1.0


def test_stake_index_free_drift_subtracted():
    """Avec un controle libre fourni, la derive spontanee est soustraite.

    Un substrat dont le bassin deriverait tout seul ne doit pas faire passer
    I_stake artificiellement : la fraction regagnee par derive libre est
    retiree de la fraction regagnee apres kick.
    """
    # Restaurateur dont l'ancre est 0 ; kick a +5, libre part de 0.
    rng_k = np.random.default_rng(3)
    rng_f = np.random.default_rng(4)
    i_with_free = stake.stake_index(
        kicked_state=stake.do_kick(np.array([0.0]), 5.0),
        step_fn=lambda s: stake.restoring_step(s, 0.3, rng_k),
        steps=30, anchor=0.0,
        free_step_fn=lambda s: stake.restoring_step(s, 0.3, rng_f),
        free_init=np.array([0.0]),
    )
    # Libre part de l'ancre -> frac_free ~ 0 (reste a 0) ; i_with_free ~ i seul.
    # Just verify it's still positive and reasonable.
    assert i_with_free > 0.0
