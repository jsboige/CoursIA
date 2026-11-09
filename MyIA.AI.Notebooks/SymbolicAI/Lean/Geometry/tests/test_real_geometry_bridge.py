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
    # l'issue honnête d'un décideur QF_NRA à coefficients rationnels.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([x - sp.sqrt(2), x ** 2 - 2], x - 2, [x])


def test_non_rational_coefficient_invalid_side_also_refused():
    # Même garde, côté invalid : √2·x − 1 ne doit plus produire un témoin
    # tronqué certifié exact=True ; la conversion refuse avant le solveur.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([sp.sqrt(2) * x - 1], 2 * x ** 2 - 1, [x])


# ---------------------------------------------------------------------------
# Critere 5 -- degenerescences : deux perpendiculaires sans / avec exclusion
#
# A l'origine, B, C, D tels que AB _|_ AC et AB _|_ AD. Sans exclusion, les
# hypotheses deviennent VACUES en B = A : C et D sont alors libres, et la
# conclusion (C, D, A alignes) tombe. L'exclusion reelle explicite B != A
# rend le theoreme valide. Le contraste doit etre mesure, pas raconte.
# ---------------------------------------------------------------------------

def _two_perpendiculars():
    xB, yB, xC, yC, xD, yD = sp.symbols('x_B y_B x_C y_C x_D y_D')
    H2a = xB * xC + yB * yC          # AB _|_ AC
    H2b = xB * xD + yB * yD          # AB _|_ AD
    CONCL = xC * yD - xD * yC        # C, D, A(=origine) alignes
    return [xB, yB, xC, yC, xD, yD], H2a, H2b, CONCL


def test_two_perpendiculars_without_exclusion_is_degenerate():
    symbols, H2a, H2b, CONCL = _two_perpendiculars()
    v = rbg.decide_real([H2a, H2b], CONCL, symbols)
    assert v.status == "invalid"
    assert v.exact is True
    xB, yB = symbols[0], symbols[1]
    # Le temoin trouve par Z3 est DEGENERE : B = A = (0,0). Ce n'est pas un
    # detail du modele mais une necessite : si (xB, yB) != 0, C et D sont tous
    # deux orthogonaux a B, donc colineaires dans le plan reel, et la
    # conclusion tiendrait.
    assert v.witness[xB] ** 2 + v.witness[yB] ** 2 == 0
    # Contre-exemple honnete, verifie independamment (sans solveur).
    check = rbg.verify_witness([H2a, H2b], CONCL, symbols, v.witness)
    assert check.ok
    assert str(check).startswith("TEMOIN VALIDE")


def test_two_perpendiculars_with_real_exclusion_is_valid():
    symbols, H2a, H2b, CONCL = _two_perpendiculars()
    xB, yB = symbols[0], symbols[1]
    v = rbg.decide_real([H2a, H2b], CONCL, symbols,
                        assumptions=[xB ** 2 + yB ** 2])
    assert v.status == "valid"
    assert v.witness is None


def test_bounded_search_absence_is_never_reported_as_valid():
    # Critere 5 : l'absence de temoin dans une recherche bornee n'est PAS un
    # `unsat`. Ici la frontiere est simulee : le solveur ne conclut pas, le
    # statut est `unknown` -- jamais `valid`.
    x, y = sp.symbols('x y')
    v = rbg.decide_real([x ** 2 + y ** 2 - 1], x - 2, [x, y],
                        solver_factory=lambda _t: _UnknownSolver())
    assert v.status == "unknown"
    assert v.witness is None


# ---------------------------------------------------------------------------
# Critere 6 -- controles negatifs
# ---------------------------------------------------------------------------

class _UnknownSolver:
    """Solveur simule qui ne conclut jamais (frontiere d'adaptation)."""

    def __init__(self):
        self.constraints = []

    def add(self, *args):
        self.constraints.extend(args)

    def check(self):
        import z3
        return z3.unknown


def test_changed_hypothesis_yields_verified_witness():
    # Meme pipeline, UNE hypothese changee : l'angle droit est declare en B
    # au lieu de A. La conclusion (M equidistant de A et B) devient fausse ;
    # le temoin rendu doit satisfaire la nouvelle hypothese ET violer la
    # conclusion, les deux verifies independamment.
    xA, yA, xB, yB, xC, yC = _symbols()
    H_B = (xA - xB) * (xC - xB) + (yA - yB) * (yC - yB)
    C1 = _C1(xA, yA, xB, yB, xC, yC)
    syms = [xA, yA, xB, yB, xC, yC]
    v = rbg.decide_real([H_B], C1, syms)
    assert v.status == "invalid"
    check = rbg.verify_witness([H_B], C1, syms, v.witness)
    assert check.ok
    assert check.holds_hypotheses and check.violates_conclusion


def test_tampered_witness_is_rejected():
    # Un temoin honnete est valide ; une coordonnee alteree doit etre rejetee.
    #
    # Pourquoi un enonce arithmetique ici : sur un modele geometrique, Z3 peut
    # laisser une coordonnee LIBRE (dans la mutation ci-dessus x_A == x_B, donc
    # x_C n'entre dans aucune contrainte) ; l'alterer par +1 produit alors un
    # AUTRE contre-exemple parfaitement honnete -- le test mesurerait le
    # hasard du modele, pas le validateur. Ici le modele est ponctuel et
    # entierement contraint, l'alteration tombe donc surement.
    x, y = sp.symbols('x y')
    syms = [x, y]
    v = rbg.decide_real([x - 1, y - 2], x - 3, syms)
    assert v.status == "invalid"
    assert rbg.verify_witness([x - 1, y - 2], x - 3, syms, v.witness).ok

    tampered = dict(v.witness)
    tampered[x] = tampered[x] + 1                   # x = 2 : hypothese cassee
    check = rbg.verify_witness([x - 1, y - 2], x - 3, syms, tampered)
    assert not check.ok
    assert not check.holds_hypotheses
    assert str(check).startswith("TEMOIN REJETE")


def test_witness_that_does_not_violate_conclusion_is_rejected():
    # Deuxieme motif de rejet : un temoin qui satisfait les hypotheses mais
    # dont la conclusion TIENT n'est pas un contre-exemple -- il confirme le
    # theoreme, il ne le refute pas. Cas geometrique non degenere : B = (1,0),
    # C = (0,1), D = (0,3) -> les deux perpendiculaires tiennent et C, D, A
    # sont alignes (tous sur l'axe des ordonnees).
    symbols, H2a, H2b, CONCL = _two_perpendiculars()
    xB, yB, xC, yC, xD, yD = symbols
    w = {xB: sp.Integer(1), yB: sp.Integer(0),
         xC: sp.Integer(0), yC: sp.Integer(1),
         xD: sp.Integer(0), yD: sp.Integer(3)}
    check = rbg.verify_witness([H2a, H2b], CONCL, symbols, w)
    assert check.holds_hypotheses
    assert not check.violates_conclusion
    assert not check.ok
    assert "conclusion=tenue" in str(check)


def test_witness_violating_nondegeneracy_is_rejected():
    # Troisieme motif de rejet : un temoin qui satisfait H et viole la
    # conclusion mais DEGENERE sur une non-degenerescence demandee.
    symbols, H2a, H2b, CONCL = _two_perpendiculars()
    xB, yB, xC, yC, xD, yD = symbols
    w = {s: sp.Integer(0) for s in symbols}
    w[xC], w[yD] = sp.Integer(1), sp.Integer(1)     # conclusion violee
    check = rbg.verify_witness([H2a, H2b], CONCL, symbols, w,
                               assumptions=[xB ** 2 + yB ** 2])
    assert check.holds_hypotheses
    assert check.violates_conclusion
    assert not check.non_degenerate
    assert not check.ok
    assert "non-degenerescence=degeneree" in str(check)


def test_incomplete_witness_is_refused_not_silently_validated():
    x, y = sp.symbols('x y')
    with pytest.raises(ValueError):
        rbg.verify_witness([x - 1], y, [x, y], {x: sp.Integer(1)})


def test_simulated_unknown_alias_is_not_a_proof():
    x, y = sp.symbols('x y')
    v = rbg.decide_real([x - 1], y, [x, y],
                        solver_factory=lambda _t: _UnknownSolver())
    assert v.status == "unknown"
    assert v.witness is None
    assert rbg.real_model([x - 1], [x, y],
                          solver_factory=lambda _t: _UnknownSolver()) is None


def test_exact_flag_distinguishes_rational_from_enclosure():
    # Rationnel : temoin exact, certifiable par substitution.
    x, y = sp.symbols('x y')
    v_rat = rbg.decide_real([x ** 2 - 4], y, [x, y])
    assert v_rat.status == "invalid" and v_rat.exact is True
    assert rbg.verify_witness([x ** 2 - 4], y, [x, y], v_rat.witness).ok

    # Irrationnel (x^2 = 2) : le temoin est un ENCADREMENT a 30 chiffres.
    # Le drapeau le dit, et le validateur refuse de le certifier -- une
    # approximation decimale ne certifie pas un temoin algebrique.
    v_irr = rbg.decide_real([x ** 2 - 2], y, [x, y])
    assert v_irr.status == "invalid" and v_irr.exact is False
    assert not rbg.verify_witness([x ** 2 - 2], y, [x, y], v_irr.witness).ok
    assert "encadrement" in str(v_irr)


# ---------------------------------------------------------------------------
# Coefficients non rationnels : refus explicite, jamais un verdict faux
#
# Review Hermes #23018 : `_poly_to_z3` tronquait un coefficient non rationnel
# en int() (√2 → 1, π → 3) et `decide_real` certifiable un théorème FAUX.
# Le module refuse désormais, au lieu de mentir.
# ---------------------------------------------------------------------------

def test_non_rational_coefficient_is_refused_not_truncated():
    # x = √2 ne force pas x = 2 : le théorème est FAUX. Avant la garde, la
    # troncation √2 → 1 faisait de `x - 1` une hypothèse *autrement fausse*
    # et le système renvoyait un faux VALID, sans témoin. Le refus est
    # l'issue honnête d'un décideur QF_NRA à coefficients rationnels.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([x - sp.sqrt(2), x ** 2 - 2], x - 2, [x])


def test_non_rational_coefficient_invalid_side_also_refused():
    # Même garde, côté invalid : √2·x − 1 ne doit plus produire un témoin
    # tronqué certifié exact=True ; la conversion refuse avant le solveur.
    x = sp.symbols('x')
    with pytest.raises(ValueError, match="non rationnel"):
        rbg.decide_real([sp.sqrt(2) * x - 1], 2 * x ** 2 - 1, [x])


# ---------------------------------------------------------------------------
# Validateur : un résidu symbolique n'est pas une réfutation
#
# Review Hermes #23018 : les trois propriétés testaient != 0 / == 0 sans
# exiger un NOMBRE, si bien qu'un résidu gardant un symbole libre passait
# pour un contre-exemple (fail-open). La garde is_number ferme le trou.
# ---------------------------------------------------------------------------

def test_symbolic_conclusion_residual_is_not_a_refutation():
    # Une conclusion portant un symbole hors de `symbols` laisse un résidu
    # SYMBOLIQUE (z + 1) : sans la garde, `!= 0` le passait pour une
    # violation. Le validateur le rejette — une famille d'affectations non
    # évaluée ne certifie rien.
    x, z = sp.symbols('x z')
    check = rbg.verify_witness([x - 1], x + z, [x], {x: sp.Integer(1)})
    assert not check.violates_conclusion
    assert not check.ok
    assert str(check).startswith("TEMOIN REJETE")


def test_symbolic_assumption_residual_is_not_non_degenerate():
    # Même garde pour une non-dégénérescence : un résidu `z` libre ne compte
    # pas comme « non nul ».
    x, z = sp.symbols('x z')
    check = rbg.verify_witness([x - 1], x - 2, [x], {x: sp.Integer(1)},
                               assumptions=[z])
    assert not check.non_degenerate


# ---------------------------------------------------------------------------
# Critère 1 de #22379 : la logique interrogée est celle des réels
# ---------------------------------------------------------------------------

def test_solver_is_built_for_non_linear_real_arithmetic(monkeypatch):
    # Les variables du module sont des z3.Real : la logique demandée doit être
    # QF_NRA (arithmétique non linéaire sur les réels), pas QF_NIA — qui nomme
    # la même théorie sur les ENTIERS, un domaine étranger à celui que le
    # module décide. Le test épingle ce que le module DEMANDE à Z3, et non un
    # détail d'implantation : les contraintes restent réelles, seul le
    # tactique choisi change.
    demandes = []
    vrai_solver_for = rbg._z3.SolverFor

    def espion(logique, *args, **kwargs):
        demandes.append(logique)
        return vrai_solver_for(logique, *args, **kwargs)

    monkeypatch.setattr(rbg._z3, "SolverFor", espion)
    rbg._make_solver()
    assert demandes == ["QF_NRA"]

    # Contrôle positif : ce solveur décide bien une contrainte qui n'a de
    # témoin que dans le domaine des réels. x*x == 2 est satisfiable sur R
    # (√2) mais insatisfiable sur Z : c'est cette asymétrie que le domaine
    # réel apporte, et le test ne surpromet rien au-delà — sous une autre
    # étiquette de logique avec les mêmes sorts Real, la sonde resterait
    # sat ; seule l'espion ci-dessus distingue les étiquettes.
    s = rbg._make_solver()
    x = rbg._z3.Real('sonde_sqrt2')
    s.add(x * x == 2)
    assert s.check() == rbg._z3.sat
