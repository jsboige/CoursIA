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
    (une affectation concrète de réels, produite par le modèle Z3 : exacte
    quand le témoin est rationnel, encadrement rationnel à 30 chiffres quand il
    est irrationnel — cf. :func:`_z3num_to_sympy`) ;
  * ``unknown`` — le solveur ne conclut pas (défensif ; sur ces systèmes petits
    la décision est immédiate).
  C'est le contraste direct avec le §5 du carnet : là, le contre-exemple
  3-4-5 est *choisi à la main* ; ici, la machine le *trouve* elle-même.

* :func:`conic_discriminant` — le discriminant ``b² − 4ac`` d'une conique
  quadratique : son signe dit si la conique se factorise sur ``R`` (``≥ 0``)
  ou seulement sur ``C`` (``< 0``) ; la décision réelle est *vérifiée* par Z3
  (existe-t-il un point réel non nul sur la conique ?). C'est la « subtilité
  réelle vs complexe » que le carnet nomme comme l'une de ses deux limites.

* :func:`verify_witness` — le validateur **indépendant** : il rejoue le témoin
  par substitution exacte dans les expressions du problème, sans solveur. Un
  témoin n'est une preuve de réfutation que s'il satisfait les hypothèses,
  viole la conclusion et respecte les non-dégénérescences ; un témoin altéré
  est **rejeté**, et le refus dit lequel des trois contrôles est tombé.

Une dégénérescence non écartée change le verdict : sans ``B != A``, deux
perpendiculaires ne forcent plus l'alignement, et Z3 trouve le témoin dégénéré
(les hypothèses deviennent vacues en ``B = A``) ; l'exclusion réelle explicite
(``assumptions``) rend le théorème valide. Un ``unknown`` — y compris simulé à
la frontière d'adaptation (:func:`decide_real`, ``solver_factory``) — n'est
**jamais** reclassé en preuve.

Le module est l'organe natif (Z3) du raisonnement réel ; il ne réimplémente
pas le calcul algébrique — il le *décide* sur ``R``, il *rend les témoins*, et
il *valide* ceux qu'on lui présente.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Callable, Dict, Iterable, List, Optional

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


_ALGEBRAIC_DIGITS = 30
"""Précision (chiffres significatifs) de l'encadrement rationnel d'un témoin irrationnel."""


def _z3num_to_sympy(v: "_z3.ExprRef"):
    """
    Renvoie la valeur d'un numéral du modèle Z3 comme nombre ``sympy``.

    Deux classes de numéraux sortent d'un modèle ``QF_NIA`` :

    * un ``RatNumRef`` — sa représentation texte **est** la fraction exacte
      (``'1/2'``, ``'3'``) ; ``sp.Rational`` la lit sans perte, le témoin est
      exact ;
    * un ``AlgebraicNumRef`` — un irrationnel algébrique (``-1.4142135623?``
      pour ``-sqrt(2)``). Le ``?`` signale que Z3 n'affiche qu'une décimale
      **tronquée** : ``sp.Rational`` la refuse, et la relire telle quelle
      donnerait un nombre faux au-delà du dixième. On demande donc à Z3 un
      encadrement rationnel à :data:`_ALGEBRAIC_DIGITS` chiffres
      (``v.approx``), qui est exact *comme rationnel* — c'est un rationnel
      précis à 30 chiffres, pas la valeur algébrique elle-même.

    Un témoin irrationnel est donc rendu comme un **encadrement rationnel** :
    suffisant pour vérifier une identité à la tolérance près et pour lire la
    valeur, mais ce n'est pas une affectation algébrique exacte. La définition
    algébrique exacte reste accessible par ``v.sexpr()``
    (``(root-obj (+ (^ x 2) (- 2)) 1)``).
    """
    text = str(v)
    if text.endswith("?"):
        # Irrationnel algébrique : Z3 n'affiche qu'une décimale tronquée.
        # `v.approx(n)` rend la fraction sous forme de chaîne « num/den » ;
        # `sp.Rational` refuse cette chaîne quand les entiers sont longs, on
        # la découpe donc explicitement (aucun flottant n'entre dans le calcul).
        num, _, den = str(v.approx(_ALGEBRAIC_DIGITS)).partition("/")
        return sp.Rational(int(num), int(den or 1))
    return sp.Rational(text)


def _z3num_is_exact(v: "_z3.ExprRef") -> bool:
    """
    Le numéral du modèle est-il une valeur **exacte** (rationnel) ?

    ``True`` pour un ``RatNumRef`` — le témoin est alors un nombre rationnel
    exact, certifiable par substitution. ``False`` pour un
    ``AlgebraicNumRef`` : la valeur rendue est un *encadrement* rationnel à
    :data:`_ALGEBRAIC_DIGITS` chiffres (cf. :func:`_z3num_to_sympy`), pas la
    valeur algébrique elle-même — une approximation ne certifie pas un témoin
    algébrique (critère 3 de l'issue #22379).
    """
    return not str(v).endswith("?")


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
    exact: bool = True                  # témoin exact ? (False = encadrement)

    def __str__(self) -> str:
        if self.status == "valid":
            return "VALID — aucun contre-exemple reel"
        if self.status == "invalid":
            kind = "temoin reel exact" if self.exact else \
                "temoin reel en encadrement (non certifiable par substitution)"
            return f"INVALID — {kind}"
        return "UNKNOWN — le solveur ne conclut pas"


def decide_real(hypotheses: Iterable, conclusion, symbols: List,
                timeout_ms: Optional[int] = None,
                assumptions: Optional[Iterable] = None,
                solver_factory: Optional[Callable[[Optional[int]], Any]] = None,
                ) -> RealVerdict:
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
    solver_factory : fabrique de solveur (``f(timeout_ms) -> objet`` ayant
        ``add`` et ``check``). Sert à **simuler** la frontière ``unknown`` de
        façon déterministe, sans dépendre d'un timeout propre à une machine
        (critère 6 de #22379) : un solveur qui rend ``unknown`` produit le
        statut ``unknown``, jamais ``valid``.
    """
    make = solver_factory or _make_solver
    solver = make(timeout_ms)
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
        # model_completion : une variable de l'univers absente du modèle vaut 0
        # au lieu de faire lever `m.eval` (TypeError: invalid input) — un
        # symbole que les hypothèses ne contraignent pas est parfaitement
        # légitime dans un contre-exemple.
        vals = {s: m.eval(zvars[s], model_completion=True) for s in symbols}
        witness = {s: _z3num_to_sympy(v) for s, v in vals.items()}
        exact = all(_z3num_is_exact(v) for v in vals.values())
        return RealVerdict("invalid", witness, exact=exact)
    return RealVerdict("unknown")


def real_model(constraints: Iterable, symbols: List,
               timeout_ms: Optional[int] = None,
               assumptions: Optional[Iterable] = None,
               solver_factory: Optional[Callable[[Optional[int]], Any]] = None,
               ) -> Optional[Dict]:
    """
    Un point **réel** satisfaisant toutes les contraintes ``c = 0``, ou ``None``
    s'il n'en existe pas.

    C'est le **témoin positif** : « donne-moi un point réel de la variété ».
    L'affectation est exacte quand le modèle Z3 est rationnel ; pour un point
    irrationnel (ex. ``x² = 2``) la coordonnée est un encadrement rationnel à
    30 chiffres, cf. :func:`_z3num_to_sympy`.

    ``assumptions`` : expressions devant être **non nulles** (non-dégénérescence)
    — sans elles, le point renvoyé tend à être dégénéré (points coïncidents).

    ``solver_factory`` : cf. :func:`decide_real` — un solveur qui ne conclut pas
    (``unknown``) rend ``None``, il ne fabrique jamais un point.
    """
    make = solver_factory or _make_solver
    solver = make(timeout_ms)
    zvars = _fresh_vars(symbols)
    for c in constraints:
        solver.add(_poly_to_z3(c, symbols, zvars) == 0)
    for a in (assumptions or []):
        solver.add(_poly_to_z3(a, symbols, zvars) != 0)
    if solver.check() != _z3.sat:
        return None
    m = solver.model()
    return {s: _z3num_to_sympy(m.eval(zvars[s], model_completion=True))
            for s in symbols}


# ---------------------------------------------------------------------------
# Validateur indépendant d'un témoin (aucun solveur dans la boucle)
# ---------------------------------------------------------------------------

@dataclass
class WitnessCheck:
    """
    Verdict du validateur **indépendant** d'un témoin, par substitution exacte.

    Les trois conditions d'un contre-exemple honnête :

    * ``holds_hypotheses`` — chaque hypothèse s'annule au témoin ;
    * ``violates_conclusion`` — la conclusion, elle, n'est **pas** nulle ;
    * ``non_degenerate`` — chaque non-dégénérescence demandée est non nulle.

    Les résidus sont conservés pour que le refus soit **lisible** : un témoin
    rejeté dit *pourquoi* il l'est, il ne rend pas un simple ``False``.
    """

    residuals: List[sp.Expr] = field(default_factory=list)
    conclusion_residual: Optional[sp.Expr] = None
    assumption_residuals: List[sp.Expr] = field(default_factory=list)

    @property
    def holds_hypotheses(self) -> bool:
        return all(r == 0 for r in self.residuals)

    @property
    def violates_conclusion(self) -> bool:
        return self.conclusion_residual is not None \
            and self.conclusion_residual != 0

    @property
    def non_degenerate(self) -> bool:
        return all(r != 0 for r in self.assumption_residuals)

    @property
    def ok(self) -> bool:
        return self.holds_hypotheses and self.violates_conclusion \
            and self.non_degenerate

    def __str__(self) -> str:
        verdict = "TEMOIN VALIDE" if self.ok else "TEMOIN REJETE"
        parts = [f"hypotheses={'ok' if self.holds_hypotheses else 'violees'}",
                 f"conclusion={'violee' if self.violates_conclusion else 'tenue'}",
                 f"non-degenerescence={'ok' if self.non_degenerate else 'degeneree'}"]
        return f"{verdict} — {', '.join(parts)}"


def verify_witness(hypotheses: Iterable, conclusion, symbols: List,
                   witness: Dict, assumptions: Optional[Iterable] = None,
                   ) -> WitnessCheck:
    """
    Valide un témoin **sans appeler le solveur** : substitution exacte.

    C'est le contrôle indépendant exigé par le critère 6 de l'issue — un
    témoin produit par Z3 n'est une preuve de réfutation que si sa
    substitution dans les expressions mêmes du problème satisfait les
    hypothèses et viole la conclusion. Un témoin **altéré** doit être
    **rejeté** ; c'est exactement ce que ce validateur teste.

    ``witness`` doit couvrir tous les ``symbols`` (``ValueError`` sinon) : un
    témoin partiel ne se valide pas silencieusement.

    Limite honnête : la substitution est **exacte** sur les rationnels. Un
    témoin irrationnel est un encadrement à 30 chiffres — ses résidus ne
    s'annulent pas exactement, et le validateur le **rejette** : une
    approximation ne certifie pas un témoin algébrique (voir
    ``RealVerdict.exact``, qui distingue les deux classes à la source).
    """
    missing = [s for s in symbols if s not in witness]
    if missing:
        raise ValueError(f"temoin incomplet, symboles absents : {missing}")
    subs = {s: witness[s] for s in symbols}
    check = WitnessCheck()
    for h in hypotheses:
        check.residuals.append(sp.simplify(sp.expand(h).subs(subs)))
    check.conclusion_residual = sp.simplify(sp.expand(conclusion).subs(subs))
    for a in (assumptions or []):
        check.assumption_residuals.append(sp.simplify(sp.expand(a).subs(subs)))
    return check


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
