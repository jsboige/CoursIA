"""Tests du module basin_asym (Pont #1-bis chantier 2/3, Epic #9531).

Le chantier 1/3 (:mod:`ict.basin_family`, tests :mod:`tests.test_basin_family`,
PR #9540) a tranche **CONFIRMED-NEGATIVE** sur des double-puits **symetriques**
``V = a x^4 - b x^2`` ou les deux bassins sont interchangeables. Ce module (2/3)
teste la robustesse du verdict dans un regime ou les deux bassins ne sont PLUS
interchangeables : le double-puits **asymetrique** ``V = a x^4 - b x^2 + c x^3``
brise la symetrie ``x <-> -x`` (terme cubique), donnant deux minima de
profondeurs, courbures, largeurs et barrieres **differentes**.

Deux differences cruciales avec le chantier 1/3, validees par ces tests :

1. **Decouplage structurellement impossible.** En regime symetrique, ``sigma``
   et ``width`` etaient decouples *par construction* (cadrans separes). En
   regime asymetrique, ils sont couples *intra-puits* (le minimum profond est a
   la fois plus raide ET plus large ; ``rho ~ 0.75`` brut). La stratification 2D
   reduit ce couplage (test ``test_stratification_reduces_coupling``) mais ne
   l'elimine pas -- le seuil ``< 0.2`` calibre pour le symetrique n'est pas
   atteignable. C'est pourquoi le test decisif est la **correlation partielle a
   2 covariables (FWL)**, qui isole ``sigma`` meme sous couplage residuel.

2. **Col robuste en ``x = 0`` meme a ``c != 0``.** ``V'(0) = 0`` et
   ``V''(0) = -2 b < 0`` quel que soit ``c`` : le test d'appartenance a un bassin
   (``sign(x_final) == sign(xstar)``) reste geometriquement exact. Les minima
   sont en forme fermee ``x_pm = (-3 c +/- sqrt(9 c^2 + 32 a b)) / (8 a)``.

Les tests valident :

1. **Geometrie** (potentiel, force, courbure, equilibria forme fermee, profil a
   6 quantites, limite ``c -> 0`` recouvre le symetrique).
2. **Mesure NON triviale** : recuperation stochastique (Langevin) a variance
   reelle dependant de la geometrie.
3. **Stratification** : elle reduit le couplage ``sigma``-``width`` (raw > strat).
4. **GATE decisive** : ``partial_rho_given_width_barrier`` ~ 0 et sous le null ->
   verdict CONFIRMED-NEGATIVE (generalisation du chantier 1/3).
5. **Robustesse cross-seed** : le verdict n'est pas un point-artefact.
6. **Controle nul** (limite symetrique ``c = 0``) : reproduit le motif fronce
   (couplage eleve, partielle ~ 0) -> le protocole detecte le couplage canonique.

Numpy + pytest. Stats reutilisees depuis :mod:`ict.basin_family`.
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import basin_asym as ba  # noqa: E402


# --------------------------------------------------------------------------- #
#  Geometrie : potentiel, force, courbure, equilibria (forme fermee)           #
# --------------------------------------------------------------------------- #


def test_asym_potential_shape():
    # V(x) = a x^4 - b x^2 + c x^3 : V(0) = 0. Le terme cubique brise V(-x)=V(x).
    a, b, c = 1.0, 2.0, 0.5
    xs = np.array([-1.0, 0.0, 1.0])
    V = ba.asym_potential(xs, a, b, c)
    assert V[1] == pytest.approx(0.0)               # V(0) = 0
    assert V[0] != pytest.approx(V[2], rel=1e-9)    # asymetrie : V(-1) != V(1)


def test_asym_force_is_zero_at_equilibria():
    # -V'(x) = 2bx - 3cx^2 - 4ax^3 : nul au col (0) et aux minima (forme fermee).
    a, b, c = 1.5, 3.0, 0.4
    eqs = ba.asym_equilibria(a, b, c)
    assert len(eqs) == 3
    for x, _st in eqs:
        assert ba.asym_force(x, a, b, c) == pytest.approx(0.0, abs=1e-9)


def test_asym_curvature_col_is_unstable_regardless_of_c():
    # LE FAIT CLE : V''(0) = -2b < 0 quel que soit c -> col en 0 robuste.
    # C'est ce qui rend le test de bassin sign(x) geometriquement exact.
    a, b = 1.0, 2.0
    for c in (-0.8, -0.3, 0.0, 0.4, 0.9):
        assert ba.asym_curvature(0.0, a, b, c) == pytest.approx(-2.0 * b, rel=1e-9)
        assert ba.asym_curvature(0.0, a, b, c) < 0.0


def test_asym_curvature_minima_are_stable():
    a, b, c = 1.0, 2.0, 0.5
    eqs = ba.asym_equilibria(a, b, c)
    for x, stable in eqs:
        curv = ba.asym_curvature(x, a, b, c)
        if stable:
            assert curv > 0.0          # minimum stable
        else:
            assert curv < 0.0          # col instable


def test_asym_equilibria_closed_form_matches_quadratic_factor():
    # V'(x) = x (4a x^2 + 3c x - 2b) : les minima sont racines du facteur quadratique.
    a, b, c = 1.0, 2.0, 0.5
    eqs = ba.asym_equilibria(a, b, c)
    x_minus, x_col, x_plus = [x for x, _ in eqs]
    assert x_col == pytest.approx(0.0, abs=1e-9)
    disc = 9.0 * c * c + 32.0 * a * b
    assert x_minus == pytest.approx((-3.0 * c - np.sqrt(disc)) / (8.0 * a), rel=1e-9)
    assert x_plus == pytest.approx((-3.0 * c + np.sqrt(disc)) / (8.0 * a), rel=1e-9)
    assert x_minus < 0.0 < x_plus                     # col entre les deux minima


def test_asym_equilibria_c_zero_recovers_symmetric():
    # Limite c -> 0 : retrouve le symetrique x_pm = +/- sqrt(b/(2a)), col en 0.
    a, b = 1.0, 2.0
    eqs = ba.asym_equilibria(a, b, 0.0)
    xstar = float(np.sqrt(b / (2.0 * a)))
    assert eqs[0] == pytest.approx((-xstar, True), abs=1e-9)
    assert eqs[1] == pytest.approx((0.0, False), abs=1e-9)
    assert eqs[2] == pytest.approx((xstar, True), abs=1e-9)


def test_asym_equilibria_undefined():
    # a <= 0 ou b <= 0 : pas de double-puits -> [].
    assert ba.asym_equilibria(-1.0, 2.0, 0.5) == []
    assert ba.asym_equilibria(1.0, -2.0, 0.5) == []
    assert ba.asym_equilibria(0.0, 2.0, 0.5) == []


# --------------------------------------------------------------------------- #
#  Profil geometrique (6 quantites, les DEUX minima) + asymetrie               #
# --------------------------------------------------------------------------- #


def test_asym_basin_profile_six_quantities_two_minima():
    a, b, c = 1.0, 2.0, 0.6
    prof = ba.asym_basin_profile(a, b, c)
    assert len(prof) == 2                              # 2 minima stables
    for (xstar, sigma, width, col, barrier, depth) in prof:
        assert col == pytest.approx(0.0, abs=1e-9)     # col commun en 0
        assert width == pytest.approx(abs(xstar), rel=1e-9)
        assert barrier == pytest.approx(-depth, rel=1e-9)   # V(0)=0
        assert sigma > 0.0                              # minimum stable
        assert depth < 0.0                              # sous le col


def test_asym_basin_profile_minima_have_different_geometry():
    # LE POINT DU CHANTIER 2/3 : des que c != 0, les deux minima differentent en
    # profondeur, courbure, largeur, barriere (non interchangeables).
    a, b, c = 1.0, 2.0, 0.8
    prof = ba.asym_basin_profile(a, b, c)
    deep = min(prof, key=lambda p: p[5])
    shallow = max(prof, key=lambda p: p[5])
    assert deep[5] < shallow[5]                         # profondeurs differentes
    assert deep[4] > shallow[4]                         # barriere differente
    # asymetrie > 0 : ecart de profondeur quantifiable
    asym = shallow[5] - deep[5]
    assert asym > 0.0


def test_asym_basin_profile_c_zero_is_symmetric():
    # c = 0 : les deux minima sont miroir (meme profondeur, sigma, largeur, barriere).
    a, b = 1.0, 2.0
    prof = ba.asym_basin_profile(a, b, 0.0)
    assert len(prof) == 2
    p_neg, p_pos = prof
    assert p_neg[1] == pytest.approx(p_pos[1], rel=1e-9)    # meme sigma
    assert p_neg[4] == pytest.approx(p_pos[4], rel=1e-9)    # meme barrier


def test_asym_basin_profile_undefined_empty():
    assert ba.asym_basin_profile(-1.0, 2.0, 0.5) == []
    assert ba.asym_basin_profile(1.0, 0.0, 0.5) == []


# --------------------------------------------------------------------------- #
#  Recuperation NON triviale : stochastique (Langevin) a variance reelle        #
# --------------------------------------------------------------------------- #


def test_recover_fraction_asym_in_unit_interval():
    rng = np.random.default_rng(0)
    prof = ba.asym_basin_profile(1.0, 2.0, 0.5)
    xstar = prof[0][0]
    frac = ba.recover_fraction_asym_stochastic(xstar, 1.0, 2.0, 0.5, rng,
                                               n_trials=20, T=500)
    assert 0.0 <= frac <= 1.0


def test_recover_fraction_asym_has_genuine_variance():
    # La mesure a une variance REELLE qui depend de la geometrie (barriere,
    # sigma, largeur) -> le test est falsifiable, non degenere.
    rng = np.random.default_rng(0)
    fracs = []
    for a in (0.5, 1.0, 2.0):
        for b in (1.0, 2.0, 3.5):
            for c in (-0.6, 0.0, 0.6):
                prof = ba.asym_basin_profile(a, b, c)
                for (xstar, _s, _w, _col, _bar, _d) in prof:
                    fracs.append(ba.recover_fraction_asym_stochastic(
                        xstar, a, b, c, rng, noise=0.35, n_trials=30, T=1500))
    fracs = np.array(fracs)
    assert fracs.std() > 0.05                           # NON constante


def test_recover_fraction_asym_barrier_matters():
    # SANITY physique : barriere plus haute -> recuperation plus haute
    # (escape d'Arrhenius ~ exp(-barrier/D)). On isole via (a,b,c) contrastes.
    rng = np.random.default_rng(42)
    prof_lo = ba.asym_basin_profile(0.6, 0.5, 0.3)      # barrier faible
    prof_hi = ba.asym_basin_profile(2.5, 3.5, 0.3)      # barrier grande
    xs_lo, _s, _w, _c, bar_lo, _d = max(prof_lo, key=lambda p: p[4])
    xs_hi, _s, _w, _c, bar_hi, _d = max(prof_hi, key=lambda p: p[4])
    assert bar_lo < bar_hi
    frac_lo = ba.recover_fraction_asym_stochastic(xs_lo, 0.6, 0.5, 0.3, rng,
                                                  noise=0.35, n_trials=80, T=2000)
    frac_hi = ba.recover_fraction_asym_stochastic(xs_hi, 2.5, 3.5, 0.3, rng,
                                                  noise=0.35, n_trials=80, T=2000)
    assert frac_hi > frac_lo


# --------------------------------------------------------------------------- #
#  Stratification : reduit le couplage sigma-width (disclosure honnete)        #
# --------------------------------------------------------------------------- #


def test_stratification_reduces_coupling():
    """Le couplage intra-puits est structurel (raw ~ 0.75). La stratification 2D
    le reduit (post-stratif < raw) meme si elle ne l'elimine pas sous le seuil
    < 0.2 (calibre pour le regime symetrique). On documente les deux."""
    v = ba.asym_verdict(seed=0, n_shuffle=50, n_trials=60, T=2000)
    assert v["rho_sigma_width"] < v["rho_sigma_width_raw"]   # stratification reduit
    # Disclosure honnete : le couplage residuel persiste (regime asymetrique).
    # Le test decisif est la partielle a 2 covariables (FWL), pas ce diagnostic.
    assert v["rho_sigma_width"] < 0.6                        # reduit sous 0.6


# --------------------------------------------------------------------------- #
#  GATE decisive : verdict CONFIRMED-NEGATIVE (generalisation chantier 1/3)    #
# --------------------------------------------------------------------------- #


@pytest.fixture(scope="module")
def verdict():
    # seed 0, n_shuffle reduit pour la vitesse du CI (200 en notebook complet).
    return ba.asym_verdict(seed=0, n_shuffle=100)


def test_verdict_is_confirmed_negative(verdict):
    """LE VERDICT DECISIF : en regime asymetrique (bassins non interchangeables),
    ``sigma`` n'a toujours aucun pouvoir predictif propre apres controle de la
    largeur ET de la barriere -> CONFIRMED-NEGATIVE. Le verdict du chantier 1/3
    (symetrique) se generalise : le Pont #1 est un vrai negatif GENERAL."""
    assert verdict["verdict"] == "CONFIRMED-NEGATIVE"


def test_two_covariate_partial_is_near_zero(verdict):
    """La correlation partielle a 2 covariables (largeur ET barriere, FWL) isole
    ``sigma`` meme sous le couplage residuel intra-puits. Elle est ~ 0."""
    assert abs(verdict["partial_rho_given_width_barrier"]) < 0.25


def test_two_covariate_partial_under_null(verdict):
    """La partielle a 2 covariables est sous le null p95 (non significatif) -> le
    peu de signal residuel n'est pas distingue du hasard."""
    assert abs(verdict["partial_rho_given_width_barrier"]) < verdict["partial_2cov_null_p95"]


def test_width_or_barrier_dominate_sigma(verdict):
    """SANITY : la largeur OU la barriere predit mieux la recuperation que sigma
    seul (brut) -- sigma n'est qu'un proxy geometrique."""
    assert (verdict["rho_width_recovery"] > verdict["rho_sigma_recovery"]
            or verdict["rho_barrier_recovery"] > verdict["rho_sigma_recovery"])


def test_verdict_robust_across_seeds():
    """Le verdict n'est pas un point-artefact : la recuperation est stochastique,
    donc le seed traverse le calcul (mesure de robustesse reelle)."""
    verdicts = [ba.asym_verdict(seed=s, n_shuffle=50, n_trials=60, T=2000)["verdict"]
                for s in (0, 1, 7, 42)]
    assert all(v == "CONFIRMED-NEGATIVE" for v in verdicts)


# --------------------------------------------------------------------------- #
#  Controle nul (limite symetrique c=0) : reproduit le motif fronce            #
# --------------------------------------------------------------------------- #


def test_recoupled_null_reproduces_fronce_pattern():
    """LE CONTROLE NUL (discipline #9531) : dans la limite symetrique ``c = 0``
    ou ``sigma`` et ``width`` sont re-couples canoniquement (a fixe, b varie),
    le protocole doit reproduire le motif du Pont #1 sur la fronce -- couplage
    eleve ET partielle a 1 covariable ~ 0. Si ce controle echoue, le protocole
    est suspect."""
    n = ba.asym_recoupled_null(seed=0, n_shuffle=100)
    assert n["reproduces_fronce_pattern"] is True
    assert n["rho_sigma_width"] > 0.6                      # re-couple par construction
    assert abs(n["partial_rho_given_width"]) < 0.3         # sigma n'ajoute rien


def test_recoupled_null_more_coupled_than_asymmetric_family():
    """CONTRASTE : le null re-couple (c=0, a fixe) est nettement plus couple que
    la famille asymetrique principale (ou la stratification reduit le couplage)."""
    n = ba.asym_recoupled_null(seed=0, n_shuffle=50)
    v = ba.asym_verdict(seed=0, n_shuffle=50, n_trials=60, T=2000)
    assert n["rho_sigma_width"] > v["rho_sigma_width"] + 0.3
