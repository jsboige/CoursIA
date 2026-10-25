"""
Tests de real_geometry_bridge — la décision réelle Z3 et ses témoins vérifiés.

Le fil rouge est celui du carnet 02 : angle droit en A (``H``), milieu ``M`` de
l'hypoténuse, conclusion d'équidistance. L'apport testé ici est la *décision
réelle* (Z3) au côté de la décision algébrique (Gröbner) :

* les théorèmes valides le restent sur ``R`` ;
* le contre-exemple réel est **trouvé par la machine** et **vérifié
  indépendamment** — on le substitue dans les expressions sympy, et il doit
  satisfaire les hypothèses tout en violant la conclusion ;
* le discriminant d'une conique confronte la lecture symbolique (signe de
  ``b² − 4ac``) à la décision réelle vérifiée par Z3 (réels vs complexes).
"""
import sys
from pathlib import Path

import pytest
import sympy as sp

# Le module vit à l'étage parent du dossier tests/
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import real_geometry_bridge as rbg  # noqa: E402


# ---------------------------------------------------------------------------
# Les objets du fil rouge (même construction que le carnet 02)
# ---------------------------------------------------------------------------

def _symbols():
    return sp.symbols('x_A y_A x_B y_B x_C y_C')


def _H(xA, yA, xB, yB, xC, yC):
    return (xB - xA) * (xC - xA) + (yB - yA) * (yC - yA)


def _C1(xA, yA, xB, yB, xC, yC):
    Mx, My = (xB + xC) / 2, (yB + yC) / 2
    return sp.expand((Mx - xA) ** 2 + (My - yA) ** 2
                     - ((Mx - xB) ** 2 + (My - yB) ** 2))


def _Ciso(xA, yA, xB, yB, xC, yC):
    return (xB - xA) ** 2 + (yB - yA) ** 2 \
        - ((xC - xA) ** 2 + (yC - yA) ** 2)


# ---------------------------------------------------------------------------
# Décision réelle : cas valides
# ---------------------------------------------------------------------------

def test_decide_real_valid_running_example():
    xA, yA, xB, yB, xC, yC = _symbols()
    v = rbg.decide_real([_H(xA, yA, xB, yB, xC, yC)],
                        _C1(xA, yA, xB, yB, xC, yC),
                        [xA, yA, xB, yB, xC, yC])
    assert v.status == "valid"
    assert v.witness is None


def test_decide_real_valid_saturated_two_perpendiculars():
    # §6-§7 du carnet : A à l'origine, deux perpendiculaires + saturation
    # de non-dégénérescence. Le théorème d'alignement tient sur R.
    xB, yB, xC, yC, xD, yD, z = sp.symbols('x_B y_B x_C y_C x_D y_D z')
    H2a = xB * xC + yB * yC
    H2b = xB * xD + yB * yD
    g_nd = xB ** 2 + yB ** 2
    CONCL = xC * yD - xD * yC
    v = rbg.decide_real([H2a, H2b, z * g_nd - 1], CONCL,
                        [xB, yB, xC, yC, xD, yD, z])
    assert v.status == "valid"


# ---------------------------------------------------------------------------
# Décision réelle : cas invalide + TEMOIN VERIFIE
# ---------------------------------------------------------------------------

def test_decide_real_invalid_returns_verified_witness():
    xA, yA, xB, yB, xC, yC = _symbols()
    H = _H(xA, yA, xB, yB, xC, yC)
    Ciso = _Ciso(xA, yA, xB, yB, xC, yC)
    v = rbg.decide_real([H], Ciso, [xA, yA, xB, yB, xC, yC])
    assert v.status == "invalid"
    w = v.witness
    assert w is not None
    assert set(w) == {xA, yA, xB, yB, xC, yC}
    # Témoignage vérifié : le point renvoyé par Z3 satisfait H...
    assert H.subs(w) == 0
    # ...tout en violant la conclusion Ciso (ce n'est pas un faux témoin).
    assert Ciso.subs(w) != 0


def test_decide_real_invalid_non_degenerate_witness():
    # Sans non-dégénérescence, Z3 rend un témoin dégénéré (A = B). Les
    # assumptions (B != A, C != A) forcent un triangle réel non isocele.
    xA, yA, xB, yB, xC, yC = _symbols()
    H = _H(xA, yA, xB, yB, xC, yC)
    Ciso = _Ciso(xA, yA, xB, yB, xC, yC)
    nd = [(xB - xA) ** 2 + (yB - yA) ** 2, (xC - xA) ** 2 + (yC - yA) ** 2]
    v = rbg.decide_real([H], Ciso, [xA, yA, xB, yB, xC, yC], assumptions=nd)
    assert v.status == "invalid"
    w = v.witness
    # le témoin est un triangle NON degénéré (B != A et C != A)
    assert ((xB - xA) ** 2 + (yB - yA) ** 2).subs(w) != 0
    assert ((xC - xA) ** 2 + (yC - yA) ** 2).subs(w) != 0
    # ...et reste un contre-exemple honnête
    assert H.subs(w) == 0
    assert Ciso.subs(w) != 0


# ---------------------------------------------------------------------------
# Témoin positif : un point réel de la variété
# ---------------------------------------------------------------------------

def test_real_model_positive_on_variety():
    xA, yA, xB, yB, xC, yC = _symbols()
    H = _H(xA, yA, xB, yB, xC, yC)
    pt = rbg.real_model([H], [xA, yA, xB, yB, xC, yC])
    assert pt is not None
    assert H.subs(pt) == 0          # le point est bien sur H = 0


def test_real_model_inconsistent_is_none():
    x = sp.symbols('x')
    assert rbg.real_model([x - 1, x - 2], [x]) is None


# ---------------------------------------------------------------------------
# Discriminant de conique : réels vs complexes
# ---------------------------------------------------------------------------

def test_conic_hyperbolic_real_lines():
    x, y = sp.symbols('x y')
    q = x ** 2 - y ** 2              # (x - y)(x + y) : delta = 4 > 0
    d = rbg.conic_discriminant(q, x, y)
    assert d.delta == 4
    assert d.kind == "hyperbolique"
    assert d.factorise_reel is True
    assert d.has_real_point is True   # Z3 : il y a des points réels


def test_conic_elliptic_complex_only():
    x, y = sp.symbols('x y')
    q = x ** 2 + y ** 2              # delta = -4 < 0 : complexe uniquement
    d = rbg.conic_discriminant(q, x, y)
    assert d.delta == -4
    assert d.kind == "elliptique"
    assert d.factorise_reel is False
    assert d.has_real_point is False  # Z3 : hors l'origine, aucun point réel


def test_conic_parabolic_double_line():
    x, y = sp.symbols('x y')
    q = x ** 2                       # delta = 0 : droite double
    d = rbg.conic_discriminant(q, x, y)
    assert d.delta == 0
    assert d.kind == "parabolique"
    assert d.factorise_reel is True
    assert d.has_real_point is True
