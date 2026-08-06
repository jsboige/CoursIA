"""Tests du module basin_family (Pont #1-bis, Epic #9531 / #8077).

Le Pont #1 (:mod:`ict.bridge_testing`, PR #8944) falsifiait « sigma stabilite ->
recuperabilite » sur la fronce de Thom : la courbure locale ``sigma`` n'a aucun
pouvoir predictif propre (correlation partielle ~ 0) une fois la largeur de bassin
controlee, et c'est la largeur (position du col) qui gouverne la portee de
recuperation. Mais sur la fronce, ``sigma`` et la largeur sont **couplees par
construction** (rho ~ 0.93) : la generalite du verdict est indecidable.

Ce module construit une famille parametrique de double-puits ou ``sigma`` et la
largeur varient **independamment par construction** (cadrans separes), puis rejoue
le protocole avec une rigueur statistique accrue (correlation partielle a 2
covariables : largeur ET barriere, la barriere co-variant avec le produit des
deux cadrans et devant etre purgee).

Les tests valident :

1. **Geometrie** du double-puits (potentiel, force, courbure, equilibria, profil a
   5 quantites) et le decouplage constructif (``realize_decoupled``).
2. **Statistique** : rangs moyennes tolerants aux ex-aequo (correctif du bug
   ``argsort(argsort())`` qui fabrique de fausses correlations sur vecteur
   constant), correlation partielle a N covariables (FWL).
3. **Mesure NON triviale** : recuperation stochastique (Langevin) -- la version
   deterministe est degeneree (purement geometrique), le bruit rend les trois
   quantites (barriere, sigma, largeur) mesurablement effectives.
4. **GATE decisive** : ``partial_rho_given_width_barrier`` ~ 0 et sous le null ->
   verdict CONFIRMED-NEGATIVE (le Pont #1 est un vrai negatif general).
5. **Robustesse cross-seed** : le verdict n'est pas un point-artefact (c.1014-L).
6. **Controle nul re-couple** : une sous-famille ou sigma/width derivent ensemble
   (a fixe, b varie) doit reproduire le motif fronce (couplage grand, partielle ~ 0).

Numpy + pytest. Le module depend de ``catastrophe`` (+ numpy du package).
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import basin_family as bf  # noqa: E402


# --------------------------------------------------------------------------- #
#  Geometrie du double-puits : potentiel, force, courbure, equilibria          #
# --------------------------------------------------------------------------- #


def test_double_well_potential_shape():
    # V(x) = a x^4 - b x^2 : V(0) = 0, minima negatifs, symetrie paire.
    a, b = 1.0, 2.0
    xs = np.array([-2.0, -1.0, 0.0, 1.0, 2.0])
    V = bf.double_well_potential(xs, a, b)
    assert V[2] == pytest.approx(0.0)              # V(0) = 0
    assert V[3] < 0.0                               # minimum droit < 0
    assert V[1] == pytest.approx(V[3], rel=1e-9)   # symetrie paire V(-x)=V(x)
    assert V[4] > V[3]                              # remontee loin du minimum


def test_double_well_force_is_zero_at_equilibria():
    # -V'(x) = 2bx - 4ax^3 : nul aux minima (+/-sqrt(b/2a)) et au col (0).
    a, b = 1.5, 3.0
    xstar = float(np.sqrt(b / (2.0 * a)))
    for x in (-xstar, 0.0, xstar):
        assert bf.double_well_force(x, a, b) == pytest.approx(0.0, abs=1e-9)


def test_double_well_curvature_signs_at_minima_and_col():
    # V''(x*) = 4b > 0 (minimum stable), V''(0) = -2b < 0 (col instable).
    a, b = 1.0, 2.0
    xstar = float(np.sqrt(b / (2.0 * a)))
    assert bf.double_well_curvature(xstar, a, b) == pytest.approx(4.0 * b, rel=1e-9)
    assert bf.double_well_curvature(xstar, a, b) > 0.0
    assert bf.double_well_curvature(0.0, a, b) == pytest.approx(-2.0 * b, rel=1e-9)
    assert bf.double_well_curvature(0.0, a, b) < 0.0


def test_double_well_curvature_independent_of_a_at_minimum():
    # LE FAIT CLE : V''(x*) = 4b ne depend PAS de a. Varying a (largeur) garde sigma.
    b = 2.0
    xstar = lambda a: float(np.sqrt(b / (2.0 * a)))
    curvs = [bf.double_well_curvature(xstar(a), a, b) for a in (0.5, 1.0, 2.0, 5.0)]
    assert all(c == pytest.approx(4.0 * b, rel=1e-8) for c in curvs)


def test_double_well_equilibria_structure():
    eqs = bf.double_well_equilibria(1.0, 2.0)
    assert len(eqs) == 3                            # 2 minima + 1 col
    xstar = float(np.sqrt(2.0 / 2.0))               # = 1.0
    assert eqs[0] == pytest.approx((-xstar, True), abs=1e-9)
    assert eqs[1] == pytest.approx((0.0, False), abs=1e-9)
    assert eqs[2] == pytest.approx((xstar, True), abs=1e-9)


def test_double_well_equilibria_undefined():
    # a <= 0 ou b <= 0 : pas de double-puits -> [].
    assert bf.double_well_equilibria(-1.0, 2.0) == []
    assert bf.double_well_equilibria(1.0, -2.0) == []
    assert bf.double_well_equilibria(0.0, 2.0) == []


# --------------------------------------------------------------------------- #
#  Profil geometrique (5 quantites) et decouplage (realize_decoupled)          #
# --------------------------------------------------------------------------- #


def test_basin_profile_five_quantities():
    a, b = 1.0, 2.0
    prof = bf.basin_profile(a, b)
    assert len(prof) == 2                           # 2 minima stables
    xstar_r = prof[1]                               # minimum droit
    xstar, sigma, width, col, barrier = xstar_r
    assert xstar > 0.0
    assert sigma == pytest.approx(4.0 * b, rel=1e-9)            # V''(x*) = 4b
    assert width == pytest.approx(float(np.sqrt(b / (2.0 * a))), rel=1e-9)
    assert col == pytest.approx(0.0, abs=1e-9)                  # col au centre
    assert barrier == pytest.approx(b ** 2 / (4.0 * a), rel=1e-9)  # b^2/(4a)


def test_basin_profile_undefined_empty():
    assert bf.basin_profile(-1.0, 2.0) == []
    assert bf.basin_profile(1.0, 0.0) == []


def test_realize_decoupled_recovers_target_sigma_and_width():
    # LE FAIT CLE du decouplage : (sigma, width) cible -> (a,b) realise exactement.
    for sigma_target in (2.0, 5.0, 12.0):
        for width_target in (0.5, 1.0, 2.0):
            a, b = bf.realize_decoupled(sigma_target, width_target)
            prof = bf.basin_profile(a, b)
            _, sigma, width, _, _ = prof[1]
            assert sigma == pytest.approx(sigma_target, rel=1e-6)
            assert width == pytest.approx(width_target, rel=1e-6)


def test_realize_decoupled_barrier_covaries_with_product():
    # LE PIEGE : barrier = sigma * width^2 / 8 co-varie avec le produit des cadrans.
    # C'est pourquoi la partielle a 2 covariables (largeur ET barriere) est decisive.
    for sigma, width in [(4.0, 1.0), (4.0, 2.0), (8.0, 1.0), (8.0, 2.0)]:
        a, b = bf.realize_decoupled(sigma, width)
        prof = bf.basin_profile(a, b)
        _, _, _, _, barrier = prof[1]
        assert barrier == pytest.approx(sigma * width ** 2 / 8.0, rel=1e-6)


def test_realize_decoupled_rejects_nonpositive():
    with pytest.raises(ValueError):
        bf.realize_decoupled(0.0, 1.0)
    with pytest.raises(ValueError):
        bf.realize_decoupled(4.0, -1.0)


# --------------------------------------------------------------------------- #
#  Statistique : rangs tolerants ex-aequo (correctif du bug argsort-argsort)   #
# --------------------------------------------------------------------------- #


def test_rank_constant_is_constant():
    # LE BUG CORRIGE : argsort(argsort(constant)) rend une rampe [0,1,...] ->
    # fausses correlations. Les rangs moyennes rendent constant -> constant.
    const = np.array([3.0, 3.0, 3.0, 3.0, 3.0])
    r = bf._rank(const)
    assert np.all(r == r[0])                        # tous egaux -> variance nulle
    assert bf._pearson(r, np.arange(5)) == 0.0      # variance nulle -> Pearson 0


def test_rank_ties_are_averaged():
    # Ex-aequo : rang moyenne (comme scipy.stats.rankdata). [1,1,4] -> [1.5,1.5,3].
    r = bf._rank(np.array([1.0, 1.0, 4.0]))
    assert r == pytest.approx(np.array([1.5, 1.5, 3.0]))


def test_rank_strictly_increasing_identity():
    # Sans ex-aequo : rangs = [1, 2, ..., n].
    r = bf._rank(np.array([0.5, 1.5, 2.5, 10.0]))
    assert r == pytest.approx(np.array([1.0, 2.0, 3.0, 4.0]))


def test_partial_spearman_zero_covariate_is_spearman():
    # Sans covariable : partial_spearman = Spearman (Pearson des rangs).
    x = np.array([1.0, 2.0, 3.0, 4.0, 5.0])
    y = np.array([2.0, 4.0, 6.0, 8.0, 10.0])        # monotone croissante
    assert bf.partial_spearman(x, y, []) == pytest.approx(1.0, abs=1e-9)


def test_partial_spearman_purges_covariate():
    # y = 2x (bruit 0), controle de x -> partielle ~ 0 (y explique par x).
    rng = np.random.default_rng(0)
    x = rng.uniform(0, 10, 200)
    y = 2.0 * x
    partial = bf.partial_spearman(x, y, [x])
    assert abs(partial) < 0.1                        # x purge -> plus rien


def test_partial_spearman_two_covariates_generalizes():
    # 2 covariables : doit rendre ~0 quand y est combinaison lineaire des 2.
    rng = np.random.default_rng(1)
    x1 = rng.uniform(0, 1, 200)
    x2 = rng.uniform(0, 1, 200)
    y = 3.0 * x1 + 2.0 * x2                          # y explique par (x1, x2)
    # x1 donne-t-il un pouvoir predictif propre apres (x1, x2) ? Non.
    partial = bf.partial_spearman(x1, y, [x1, x2])
    assert abs(partial) < 0.15


# --------------------------------------------------------------------------- #
#  Recuperation NON triviale : stochastique (Langevin) a variance reelle        #
# --------------------------------------------------------------------------- #


def test_recover_fraction_stochastic_in_unit_interval():
    rng = np.random.default_rng(0)
    a, b = bf.realize_decoupled(4.0, 1.0)
    prof = bf.basin_profile(a, b)
    xstar = prof[1][0]
    frac = bf.recover_fraction_stochastic(xstar, a, b, rng, n_trials=20, T=500)
    assert 0.0 <= frac <= 1.0


def test_recover_fraction_stochastic_has_genuine_variance():
    # LE POINT NON TRIVIAL : la mesure deterministe est degeneree (constante apres
    # mise a l'echelle). La mesure stochastique a une variance REELLE qui depend
    # de la geometrie (barriere, sigma, largeur) -> le test est falsifiable.
    rng = np.random.default_rng(0)
    fracs = []
    for sigma in (2.0, 4.0, 8.0, 12.0):
        for width in (0.5, 1.0, 1.5):
            a, b = bf.realize_decoupled(sigma, width)
            prof = bf.basin_profile(a, b)
            xstar = prof[1][0]
            fracs.append(bf.recover_fraction_stochastic(
                xstar, a, b, rng, noise=0.35, n_trials=40, T=1500))
    fracs = np.array(fracs)
    assert fracs.std() > 0.05                        # NON constante (variance reelle)


def test_recover_fraction_stochastic_barrier_matters():
    # SANITY physique : a bruit fixe, barriere plus haute -> recuperation plus haute
    # (escape d'Arrhenius ~ exp(-barrier/D)). On isole la barriere en gardant sigma
    # et largeur proches et en faisant varier la barriere via (sigma,width).
    rng = np.random.default_rng(42)
    # barrier = sigma * width^2 / 8 : barrier faible vs eleve.
    a_lo, b_lo = bf.realize_decoupled(2.0, 0.5)      # barrier petit
    a_hi, b_hi = bf.realize_decoupled(12.0, 2.0)     # barrier grand
    prof_lo = bf.basin_profile(a_lo, b_lo)[1]
    prof_hi = bf.basin_profile(a_hi, b_hi)[1]
    assert prof_lo[4] < prof_hi[4]                   # barrier: lo < hi
    frac_lo = bf.recover_fraction_stochastic(prof_lo[0], a_lo, b_lo, rng,
                                             noise=0.35, n_trials=80, T=2000)
    frac_hi = bf.recover_fraction_stochastic(prof_hi[0], a_hi, b_hi, rng,
                                             noise=0.35, n_trials=80, T=2000)
    assert frac_hi > frac_lo                         # barrier grand => recupere mieux


# --------------------------------------------------------------------------- #
#  GATE decisive : verdict CONFIRMED-NEGATIVE (Pont #1 vrai negatif general)   #
# --------------------------------------------------------------------------- #


@pytest.fixture(scope="module")
def verdict():
    # seed 0, n_shuffle reduit pour la vitesse du CI (200 en notebook complet).
    return bf.pont1bis_verdict(seed=0, n_shuffle=100)


def test_decoupling_holds_by_construction(verdict):
    """LE PRE-REQUIS : sigma et largeur sont decouplees par construction
    (``rho_sigma_width`` ~ 0 sur le produit cartesien des cadrans). Sans cela, le
    verdict de generalite n'est pas decidable."""
    assert verdict["decoupling_ok"] is True
    assert abs(verdict["rho_sigma_width"]) < 0.2


def test_verdict_is_confirmed_negative(verdict):
    """LE VERDICT DECISIF : ``sigma`` n'a aucun pouvoir predictif propre apres
    controle de la largeur ET de la barriere -> CONFIRMED-NEGATIVE. Le Pont #1
    falsifie sur la fronce est un vrai negatif GENERAL, pas un artefact de
    couplage."""
    assert verdict["verdict"] == "CONFIRMED-NEGATIVE"


def test_two_covariate_partial_is_near_zero(verdict):
    """LA RIGUEUR #9531 : la correlation partielle a 2 covariables (largeur ET
    barriere) est ~ 0 -- c'est la barriere qui co-variait avec le produit des
    cadrans et qu'il fallait purger. La controler ne revele aucun pouvoir propre
    de sigma."""
    assert abs(verdict["partial_rho_given_width_barrier"]) < 0.25


def test_two_covariate_partial_under_null(verdict):
    """La partielle a 2 covariables est sous le null p95 (non significatif) -> le
    peu de signal residuel n'est pas distingue du hasard."""
    assert abs(verdict["partial_rho_given_width_barrier"]) < verdict["partial_2cov_null_p95"]


def test_width_or_barrier_dominate_sigma(verdict):
    """SANITY : la largeur OU la barriere predit mieux la recuperation que sigma
    seul (brut) -- sigma n'est qu'un proxy."""
    assert (verdict["rho_width_recovery"] > verdict["rho_sigma_recovery"]
            or verdict["rho_barrier_recovery"] > verdict["rho_sigma_recovery"])


def test_verdict_robust_across_seeds():
    """Le verdict n'est pas un point-artefact (c.1014-L) : la recuperation est
    stochastique, donc le seed traverse le calcul (mesure de robustesse reelle)."""
    verdicts = [bf.pont1bis_verdict(seed=s, n_shuffle=50)["verdict"]
                for s in (0, 1, 7, 42)]
    assert all(v == "CONFIRMED-NEGATIVE" for v in verdicts)


# --------------------------------------------------------------------------- #
#  Controle nul re-couple : doit reproduire le motif fronce                    #
# --------------------------------------------------------------------------- #


def test_recoupled_null_reproduces_fronce_pattern():
    """LE CONTROLE NUL (discipline #9531) : une sous-famille ou sigma et largeur
    derivent ensemble (a fixe, b varie) doit reproduire le motif du Pont #1 sur
    la fronce -- couplage eleve (rho_sigma_width grand) ET partielle a 1 covariable
    ~ 0. Si ce controle echoue, le protocole lui-meme est suspect."""
    n = bf.recoupled_null(seed=0, n_shuffle=100)
    assert n["reproduces_fronce_pattern"] is True
    assert n["rho_sigma_width"] > 0.6                 # re-couple par construction
    assert abs(n["partial_rho_given_width"]) < 0.3    # sigma n'ajoute rien


def test_recoupled_null_more_coupled_than_decoupled_family():
    """CONTRASTE : le null re-couple est nettement plus couple que la famille
    decouplee principale (ou rho_sigma_width ~ 0 par construction)."""
    n = bf.recoupled_null(seed=0, n_shuffle=50)
    v = bf.pont1bis_verdict(seed=0, n_shuffle=50)
    assert n["rho_sigma_width"] > v["rho_sigma_width"] + 0.5
