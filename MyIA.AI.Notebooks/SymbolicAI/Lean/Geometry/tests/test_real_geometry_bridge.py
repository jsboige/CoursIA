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
# Le contrat « trois verdicts, never raise » tient sur les cas limites
# (review Hermes de #22551 : trois exceptions non gérées, reproduites)
# ---------------------------------------------------------------------------

def test_decide_real_free_symbol_returns_verdict_not_raises():
    # Un symbole de l'univers qu'aucune hypothèse ne contraint. `m.eval` sans
    # `model_completion` levait `TypeError: invalid input: z` ; le contrat est
    # « trois verdicts, unknown en défensif » — jamais une exception.
    x, y, z = sp.symbols('x y z')
    v = rbg.decide_real([x - 1], y - 2, [x, y, z])
    assert v.status in ("valid", "invalid", "unknown")
    assert v.status == "invalid"          # y = 2 n'implique pas x = 1
    assert set(v.witness) == {x, y, z}
    assert v.witness[x] == 1
    assert v.witness[z] == 0              # libre -> complétée à 0


def test_real_model_free_symbol_returns_point():
    # Même cause, chemin `real_model` : levait `TypeError: invalid input: y`.
    x, y, z = sp.symbols('x y z')
    pt = rbg.real_model([x - 1], [x, y, z])
    assert pt is not None
    assert set(pt) == {x, y, z}
    assert pt[x] == 1
    assert pt[z] == 0


def test_decide_real_irrational_witness_does_not_raise():
    # x² = 2 : le modèle Z3 porte un `AlgebraicNumRef` (`-1.4142135623?`).
    # `sp.Rational(str(v))` refusait le `?` ; le témoin est désormais un
    # encadrement rationnel à 30 chiffres — vérifié ici par sa distance à 2.
    x, y = sp.symbols('x y')
    v = rbg.decide_real([x ** 2 - 2], y, [x, y])
    assert v.status == "invalid"
    w = v.witness
    assert abs(sp.Abs(w[x] ** 2 - 2)) < sp.Rational(1, 10 ** 25)
    assert sp.Abs(w[x]) > 1               # |x| = sqrt(2), pas 0


def test_real_model_irrational_point_does_not_raise():
    x = sp.symbols('x')
    pt = rbg.real_model([x ** 2 - 2], [x])
    assert pt is not None
    assert abs(sp.Abs(pt[x] ** 2 - 2)) < sp.Rational(1, 10 ** 25)


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


# ---------------------------------------------------------------------------
# Coefficients non rationnels : refus explicite, jamais un verdict faux
#
# Review Hermes #23018 : `_poly_to_z3` tronquait un coefficient non rationnel
# en int() (√2 → 1, π → 3) et `decide_real` certifiait un théorème FAUX.
# Le module refuse désormais, au lieu de mentir. Défaut latent sur `main`
# jusqu'ici (aucun test n'y passait de coefficient irrationnel).
# ---------------------------------------------------------------------------

def test_non_rational_coefficient_is_refused_not_truncated():
    # x = √2 ne force pas x = 2 : le théorème est FAUX. Avant la garde, la
    # troncation √2 → 1 faisait de `x - 1` une hypothèse *autrement fausse*
    # et le système renvoyait un faux VALID, sans témoin. Le refus est
    # l'issue honnête d'un décideur QF_NIA à coefficients rationnels.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([x - sp.sqrt(2), x ** 2 - 2], x - 2, [x])


def test_non_rational_coefficient_invalid_side_also_refused():
    # Même garde, côté invalid : √2·x − 1 ne doit plus produire un témoin
    # tronqué certifié exact=True ; la conversion refuse avant le solveur.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([sp.sqrt(2) * x - 1], 2 * x ** 2 - 1, [x])
