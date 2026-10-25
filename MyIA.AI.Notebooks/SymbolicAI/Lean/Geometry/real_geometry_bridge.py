"""
real_geometry_bridge — la décision *réelle* Z3, aux côtés des bases de Gröbner.

Le carnet 02 décide l'appartenance ``g ∈ <H>`` par bases de Gröbner : c'est une
décision **algébrique** — on travaille dans la clôture algébrique, l'univers
des nombres **complexes**. La question qu'elle répond est « le théorème
``H ⟹ g`` tient-il ? », mais *sur les complexes*.

Ce module apporte la même question **sur les réels**, résolue nativement par
l'organe Z3 (théorie des corps ordonnés réels, ``QF_NIA``). Deux faces :

* :func:`decide_real` — valide-t-il sur ``R`` ? Trois verdicts :
  * ``valid``   — aucun contre-exemple réel (la réfutation est insatisfiable) ;
  * ``invalid`` — un contre-exemple réel existe, **et le témoin est renvoyé**
    (une affectation concrète et exacte de réels, produite par le modèle Z3) ;
  * ``unknown`` — le solveur ne conclut pas (défensif ; sur ces systèmes petits
    la décision est immédiate).
  C'est le contraste direct avec le §5 du carnet : là, le contre-exemple
  3-4-5 est *choisi à la main* ; ici, la machine le *trouve* elle-même.

* :func:`conic_discriminant` — le discriminant ``b² − 4ac`` d'une conique
  quadratique : son signe dit si la conique se factorise sur ``R`` (``≥ 0``)
  ou seulement sur ``C`` (``< 0``) ; la décision réelle est *vérifiée* par Z3
  (existe-t-il un point réel non nul sur la conique ?). C'est la « subtilité
  réelle vs complexe » que le carnet nomme comme l'une de ses deux limites.

Le module est l'organe natif (Z3) du raisonnement réel ; il ne réimplémente
pas le calcul algébrique — il le *décide* sur ``R`` et il *rend les témoins*.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Optional

import sympy as sp
import z3 as _z3


# ---------------------------------------------------------------------------
# Conversions sympy <-> Z3
# ---------------------------------------------------------------------------

def _poly_to_z3(expr, symbols: List, zvars: Dict) -> "_z3.ExprRef":
    """
    Convertit une expression sympy (polynomiale en ``symbols``) en expression Z3.

    Passe par ``sp.Poly`` pour reconstruire terme à terme : ``coef * x^p * y^q``.
    Les coefficients sont portés en ``fractions.Fraction`` exacts, que l'API Z3
    combine proprement avec les variables réelles (``Fraction(3,2) * x`` →
    ``3/2*x``) — la voie exacte, là où ``z3.Int`` serait un entier tronqué.
    """
    e = sp.expand(sp.together(sp.nsimplify(expr)))
    poly = sp.Poly(e, *symbols)
    total: Optional["_z3.ExprRef"] = None
    for monom, coef in poly.terms():
        coef = sp.nsimplify(coef)
        if coef.is_Rational:
            fr = Fraction(int(coef.p), int(coef.q))
        else:
            fr = Fraction(int(coef), 1)
        term: "_z3.ExprRef" = fr
        for sym, power in zip(symbols, monom):
            if power:
                term = term * (zvars[sym] ** power)
        total = term if total is None else (total + term)
    return total if total is not None else Fraction(0, 1)


def _z3num_to_sympy(v: "_z3.ExprRef"):
    """
    Renvoie la valeur d'un numéral du modèle Z3 comme ``sympy.Rational`` exact.

    L'API minimale rend un ``RatNumRef`` dont la représentation texte est la
    fraction exacte (``'1/2'``, ``'3'``) — ``sp.Rational`` la lit sans perte.
    """
    return sp.Rational(str(v))


def _make_solver(timeout_ms: Optional[int] = None) -> "_z3.Solver":
    """Un solveur ``QF_NIA`` ; le timeout n'est posé que si l'API le permet."""
    s = _z3.SolverFor("QF_NIA")
    if timeout_ms is not None:
        try:
            s.set_option("timeout", int(timeout_ms))
        except (AttributeError, Exception):
            pass  # API minimale : pas de timeout par solveur
    return s


def _fresh_vars(symbols: List) -> Dict:
    return {s: _z3.Real(str(s)) for s in symbols}


# ---------------------------------------------------------------------------
# Décision réelle
# ---------------------------------------------------------------------------

@dataclass
class RealVerdict:
    """Verdict de :func:`decide_real` sur les réels."""

    status: str                          # "valid" | "invalid" | "unknown"
    witness: Optional[Dict] = None      # {sp.Symbol: Rational} si "invalid"

    def __str__(self) -> str:
        if self.status == "valid":
            return "VALID — aucun contre-exemple reel"
        if self.status == "invalid":
            return "INVALID — temoin reel fourni"
        return "UNKNOWN — le solveur ne conclut pas"


def decide_real(hypotheses: Iterable, conclusion, symbols: List,
                timeout_ms: Optional[int] = None,
                assumptions: Optional[Iterable] = None) -> RealVerdict:
    """
    Décide, **sur les réels**, ``forall x. (∧ h = 0) -> g = 0``.

    Méthode : on réfute. On impose les hypothèses ``h = 0`` *et* ``g != 0`` ;
    si ce système est *insatisfiable* sur ``R``, le théorème est **valide**
    (aucun point réel ne le viole) ; s'il est *satisfiable*, Z3 renvoie un
    modèle — un **témoin réel** exact qui contredit la conclusion.

    Parameters
    ----------
    hypotheses : itérable d'expressions sympy (les ``H``)
    conclusion : expression sympy (le ``g``)
    symbols : liste des symboles sympy (l'univers de la décision)
    timeout_ms : bornes le calcul si l'API Z3 le permet (sinon ignoré)
    assumptions : itérable d'expressions sympy devant être **non nulles**
        (côtés de non-dégénérescence, ex. ``B != A``) — sans elles, Z3 tend à
        rendre un témoin *dégénéré* (points coïncidents, le plus « facile »).
    """
    solver = _make_solver(timeout_ms)
    zvars = _fresh_vars(symbols)
    for h in hypotheses:
        solver.add(_poly_to_z3(h, symbols, zvars) == 0)
    for a in (assumptions or []):
        solver.add(_poly_to_z3(a, symbols, zvars) != 0)
    g = _poly_to_z3(conclusion, symbols, zvars)
    solver.add(g != 0)          # réfutation : cherche un point reel avec g != 0
    r = solver.check()
    if r == _z3.unsat:
        return RealVerdict("valid")
    if r == _z3.sat:
        m = solver.model()
        witness = {s: _z3num_to_sympy(m.eval(zvars[s])) for s in symbols}
        return RealVerdict("invalid", witness)
    return RealVerdict("unknown")


def real_model(constraints: Iterable, symbols: List,
               timeout_ms: Optional[int] = None,
               assumptions: Optional[Iterable] = None) -> Optional[Dict]:
    """
    Un point **réel** (affectation exacte) satisfaisant toutes les contraintes
    ``c = 0``, ou ``None`` s'il n'en existe pas.

    C'est le **témoin positif** : « donne-moi un point réel de la variété ».

    ``assumptions`` : expressions devant être **non nulles** (non-dégénérescence)
    — sans elles, le point renvoyé tend à être dégénéré (points coïncidents).
    """
    solver = _make_solver(timeout_ms)
    zvars = _fresh_vars(symbols)
    for c in constraints:
        solver.add(_poly_to_z3(c, symbols, zvars) == 0)
    for a in (assumptions or []):
        solver.add(_poly_to_z3(a, symbols, zvars) != 0)
    if solver.check() != _z3.sat:
        return None
    m = solver.model()
    return {s: _z3num_to_sympy(m.eval(zvars[s])) for s in symbols}


# ---------------------------------------------------------------------------
# Discriminant d'une conique : réels vs complexes
# ---------------------------------------------------------------------------

@dataclass
class ConicDiscriminant:
    """Discriminant d'une conique quadratique homogène ``a x² + b x y + c y²``."""

    a: sp.Expr
    b: sp.Expr
    c: sp.Expr
    delta: sp.Expr                # b² - 4ac
    kind: str                     # hyperbolique | parabolique | elliptique | symbolique
    factorise_reel: Optional[bool]  # delta >= 0 ? (None si delta symbolique)
    has_real_point: bool           # Z3 : ∃ point réel non nul sur la conique ?


def conic_discriminant(q, x, y,
                       timeout_ms: Optional[int] = None) -> ConicDiscriminant:
    """
    Discriminant réel/complexes d'une conique quadratique ``q`` en ``x, y``.

    Le signe de ``delta = b² − 4ac`` est le classifieur symbolique :
    ``delta > 0`` → deux droites réelles (hyperbolique) ; ``delta = 0`` → une
    droite double (parabolique) ; ``delta < 0`` → deux droites complexes
    conjuguées, aucune réelle (elliptique). La décision *réelle* est ensuite
    **vérifiée par Z3** : il existe-t-il un point réel non nul ``(x, y)`` avec
    ``q(x, y) = 0`` ? Les deux lectures se confrontent dans le résultat.
    """
    poly = sp.Poly(sp.expand(q), x, y)
    a = poly.coeff_monomial(x ** 2)
    b = poly.coeff_monomial(x * y)
    c = poly.coeff_monomial(y ** 2)
    delta = sp.expand(b ** 2 - 4 * a * c)

    if delta.is_number:
        if delta > 0:
            kind, factorise_reel = "hyperbolique", True
        elif delta == 0:
            kind, factorise_reel = "parabolique", True
        else:
            kind, factorise_reel = "elliptique", False
    else:
        kind, factorise_reel = "symbolique", None

    solver = _make_solver(timeout_ms)
    zx, zy = _z3.Real(str(x)), _z3.Real(str(y))
    solver.add(_poly_to_z3(q, [x, y], {x: zx, y: zy}) == 0)
    solver.add(_z3.Or(zx != 0, zy != 0))
    has_real_point = solver.check() == _z3.sat

    return ConicDiscriminant(a, b, c, delta, kind, factorise_reel, has_real_point)
