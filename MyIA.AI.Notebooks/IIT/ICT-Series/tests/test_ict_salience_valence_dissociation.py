"""Tests du module : dissociation saillance / pregnance (case ``s perp pi``).

Couvrent les verdicts falsifiables de la 1ʳᵉ case de la matrice inversee
(Epic #9533, prediction pre-enregistree PR #9546) :

1. **Decorrelation par construction** -- ``s`` (conspicuite) et ``lam`` (vraie
   recompense) sont tirees independamment -> ``corr(s, lam) ~ 0`` (pre-requis).
2. **Fidelite de l'apprentissage** -- la valence apprise ``V`` converge vers
   ``lam`` (Rescorla-Wagner), independamment de ``s`` (qui n'entre pas dans
   l'apprentissage).
3. **Verdict honnete a deux niveaux** (le coeur falsifiable) :
   * **Engagement TOTAL FALSIFIE** : ``s`` gate la detection, donc ``s`` predit
     l'engagement total meme pour l'animat a valence (``|partial_s|pi| > 0.5``).
     La prediction stricte pre-enregistree est REJETEE -- resultat honnete.
   * **DECISION sachant detection CONFIRMEE** : ``pi`` gouverne (``|partial_pi|s|
     > 0.5``), ``s`` est inerte (``|partial_s|pi| < 0.2``) -> ``DISSOCIATED`` au
     niveau decision (pattern « saillant sans importance »).
4. **Null adversarial** -- l'animat reactif (``pi == s``) **inverse** le motif :
   ``s`` predit la decision, ``pi`` ne predit plus.
5. **Non-trivialite (SOTA Prong B)** -- la mesure comportementale est NON
   deterministe (Bernoulli, detection gatee) -> le verdict n'est pas garanti par
   construction ; a faible puissance l'effet propre de ``s`` a la decision est
   noye dans le bruit (``NOT-DISSOCIATED`` par manque de n, pas de concept).
6. **Robustesse multi-seed** -- le verdict decision tient sur >=3/4 seeds a
   puissance adequate (``n_stimuli >= 120``).

Plus les proprietes mecaniques (bornes, sigmoid, rangs moyennes, FWL). numpy +
pytest, CPU uniquement.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.salience_valence_dissociation import (
    _pearson,
    _rank,
    _sigmoid,
    approach_probability_reactive,
    approach_probability_valence,
    case_verdict,
    learn_valences,
    measure_decision_given_detected,
    measure_engagement,
    partial_spearman,
    stimulus_battery,
    verdict_robust_across_seeds,
)


# --------------------------------------------------------------------------- #
#  1. Decorrelation par construction + bornes                                  #
# --------------------------------------------------------------------------- #


def test_stimulus_battery_shapes_and_ranges():
    """s dans [0.1, 1.0], lam dans [-1, +1], memes tailles."""
    rng = np.random.default_rng(0)
    s, lam = stimulus_battery(n_stimuli=50, rng=rng)
    assert s.shape == lam.shape == (50,)
    assert 0.1 <= s.min() and s.max() <= 1.0
    assert -1.0 <= lam.min() and lam.max() <= 1.0


def test_stimulus_battery_decorrelation_pre_requisite():
    """Pre-requis de la dissociation : s et lam decorreles par construction.

    Sur n=400 (grande batterie), |corr(s, lam)| doit etre petit (< 0.2). Sur une
    petite batterie (n=40) le bruit d'echantillonnage (SE ~ 1/sqrt(n)) peut
    produire des correlations spurieuses -- on teste donc a grande echelle.
    """
    rng = np.random.default_rng(0)
    s, lam = stimulus_battery(n_stimuli=400, rng=rng)
    rho = _pearson(_rank(s), _rank(lam))
    assert abs(rho) < 0.2, f"decorrelation violatee : rho={rho:.3f}"


# --------------------------------------------------------------------------- #
#  2. Fidelite Rescorla-Wagner : V -> lam, independant de s                   #
# --------------------------------------------------------------------------- #


def test_learn_valences_converges_to_lambda():
    """V apprise converge vers lam (fidelite), independamment de s."""
    rng = np.random.default_rng(0)
    _, lam = stimulus_battery(n_stimuli=40, rng=rng)
    V = learn_valences(lam, n_epochs=400, alpha=0.2, rng=rng)
    # Convergence : V proche de lam en moyenne quadratique.
    rmse = float(np.sqrt(np.mean((V - lam) ** 2)))
    assert rmse < 0.15, f"V n'a pas converge vers lam : RMSE={rmse:.3f}"


def test_learn_valence_of_a_single_extreme_stimulus():
    """Un stimulus fortement positif -> V positive ; fortement negatif -> negative."""
    rng = np.random.default_rng(0)
    lam = np.array([1.0, -1.0, 0.0])
    V = learn_valences(lam, n_epochs=300, alpha=0.2, rng=rng)
    assert V[0] > 0.5
    assert V[1] < -0.5
    assert abs(V[2]) < 0.2


# --------------------------------------------------------------------------- #
#  3. Proprietes mecaniques : sigmoid, engagement, decision                    #
# --------------------------------------------------------------------------- #


def test_sigmoid_range_and_monotone():
    # Valeurs moderees (la sigmoid numeriquement stable sature a 0/1 pour |x|>>1)
    x = np.array([-6.0, -1.0, 0.0, 1.0, 6.0])
    p = _sigmoid(x)
    assert np.all((p > 0.0) & (p < 1.0))   # strictement dans ]0, 1[
    assert np.all(np.diff(p) > 0.0)        # strictement croissante
    assert abs(p[2] - 0.5) < 1e-9          # sigma(0) = 0.5
    assert np.isfinite(p).all()            # pas de NaN/inf (stabilite numerique)


def test_approach_probability_valence_follows_V_not_s():
    """Pour l'animat a valence, P(approach) = sigma(gain*V) : ne depend que de V."""
    rng = np.random.default_rng(0)
    s, lam = stimulus_battery(n_stimuli=40, rng=rng)
    V = learn_valences(lam, rng=rng)
    p = approach_probability_valence(V, gain=3.0)
    assert p.shape == V.shape
    # V eleve -> P elevee ; V faible -> P faible (monotone en V)
    assert np.all(np.diff(p[np.argsort(V)]) > -1e-12)
    # Deux V identiques -> P identiques (independance envers s)
    V2 = V.copy()
    p2 = approach_probability_valence(V2, gain=3.0)
    assert np.allclose(p, p2)


def test_approach_probability_reactive_follows_s():
    """Pour le reactif, P(approach) = sigma(gain*s) : ne depend que de s."""
    s = np.array([0.1, 0.5, 0.9])
    p = approach_probability_reactive(s, gain=3.0)
    assert np.all(np.diff(p) > 0.0)  # croissante en s


def test_engagement_bounds_and_s_gating():
    """L'engagement total est dans [0,1] et gate par s : E[eng] <= s."""
    rng = np.random.default_rng(0)
    s, _ = stimulus_battery(n_stimuli=40, rng=rng)
    p = np.full(40, 0.8)  # decision constante elevee
    eng = measure_engagement(s, p, n_trials=400, rng=rng)
    assert np.all(eng >= 0.0) and np.all(eng <= 1.0)
    # E[eng_i] = s_i * p -> eng approximativement <= s_i (au bruit pres)
    assert np.all(eng <= s + 0.15)


def test_decision_given_detected_isolated_from_gating():
    """P(approach|detecte) isole la decision : pour p constant, dec ~ p (pas ~ s)."""
    rng = np.random.default_rng(0)
    s, _ = stimulus_battery(n_stimuli=60, rng=rng)
    p_const = np.full(60, 0.7)
    dec = measure_decision_given_detected(s, p_const, n_trials=600, rng=rng)
    # Pour chaque stimulus detecte au moins une fois, dec ~ 0.7 independamment de s
    mask = s > 0.3  # stimuli suffisamment detectes pour un estimateur stable
    assert np.all(np.abs(dec[mask] - 0.7) < 0.12), f"dec={dec[mask]}"


# --------------------------------------------------------------------------- #
#  4. Statistique : rangs moyennes, Pearson, correlation partielle (FWL)      #
# --------------------------------------------------------------------------- #


def test_rank_average_ties():
    """Les rangs moyennes tolerent les ex-aequo (miroir scipy.rankdata)."""
    xs = np.array([1.0, 1.0, 3.0, 2.0, 1.0])
    r = _rank(xs)
    # Les trois '1.0' partagent les rangs 1,2,3 -> moyenne 2.0
    assert r[0] == r[1] == r[4] == 2.0


def test_rank_constant_array_is_constant():
    """Vecteur constant -> rangs constants (evite les fausses correlations)."""
    r = _rank(np.full(5, 3.14))
    assert np.all(r == r[0])


def test_partial_spearman_zero_on_decorrelated():
    """partial_spearman ~ 0 quand y est independant de x (controlant un covarie)."""
    rng = np.random.default_rng(0)
    x = rng.uniform(size=400)
    cov = rng.uniform(size=400)
    y = rng.uniform(size=400)  # independant de x
    assert abs(partial_spearman(x, y, [cov])) < 0.2


def test_partial_spearman_positive_on_correlated():
    """partial_spearman > 0 quand y croit avec x (covarie constante)."""
    rng = np.random.default_rng(0)
    x = rng.uniform(size=400)
    cov = rng.uniform(size=400)
    y = x + 0.05 * rng.standard_normal(400)  # y ~ x
    assert partial_spearman(x, y, [cov]) > 0.5


def test_partial_spearman_controls_covariate():
    """Si x et y ne se correlent QUE par l'intermediaire de cov (x = cov+noise,
    y = cov+noise, independents sachant cov), le controle partiel annule la
    correlation naive -> |rho_partial| << |rho_naive|."""
    rng = np.random.default_rng(0)
    cov = rng.uniform(size=400)
    x = cov + 0.2 * rng.standard_normal(400)   # x ~ cov (SNR eleve)
    y = cov + 0.2 * rng.standard_normal(400)   # y ~ cov, mais x _|_ y | cov
    rho_naive = _pearson(_rank(x), _rank(y))
    rho_partial = partial_spearman(x, y, [cov])
    # Naive > 0.4 (via cov partage) ; partial effondre vers 0
    assert rho_naive > 0.4, f"naive devrait etre >0.4 via cov : {rho_naive:.3f}"
    assert abs(rho_partial) < 0.2, f"partial devrait etre ~0 : {rho_partial:.3f}"


# --------------------------------------------------------------------------- #
#  5. Le coeur falsifiable : verdict honnete a deux niveaux                  #
# --------------------------------------------------------------------------- #


@pytest.fixture(scope="module")
def default_verdict():
    """Verdict par defaut (n=120, trials=300) -- seed 0, detailed."""
    return case_verdict(seed=0)


def test_total_engagement_is_NOT_dissociated_s_gates_detection(default_verdict):
    """Niveau engagement TOTAL : la prediction stricte est FALSIFIEE.

    s gate la detection -> s predit l'engagement total (|partial_s|pi| > 0.5),
    meme pour l'animat a valence. Ce n'est pas un defaut, c'est la mecanique
    perceptuelle. Resultat honnete, pas un echec.
    """
    v = default_verdict
    assert v["total_dissociated"] is False
    assert abs(v["total_partial_s_given_pi_valence"]) > 0.5, (
        "s doit predire l'engagement total (gating de detection) : "
        f"partial_s|pi={v['total_partial_s_given_pi_valence']:.3f}")


def test_decision_level_IS_dissociated_pi_governs(default_verdict):
    """Niveau DECISION sachant detection : pi gouverne (|partial_pi|s| > 0.5)."""
    v = default_verdict
    assert v["decision_dissociated"] is True
    assert abs(v["decision_partial_pi_given_s_valence"]) > 0.5


def test_decision_level_s_is_inert(default_verdict):
    """Niveau DECISION : s est inerte (|partial_s|pi| < 0.2) -- la vraie dissociation."""
    v = default_verdict
    assert abs(v["decision_partial_s_given_pi_valence"]) < 0.2


def test_verdict_is_dissociated_at_decision(default_verdict):
    """Le verdict combine est DISSOCIATED-AT-DECISION (total falsifie, decision tient)."""
    assert default_verdict["verdict"] == "DISSOCIATED-AT-DECISION"


# --------------------------------------------------------------------------- #
#  6. Null adversarial : le reactif inverse le motif                          #
# --------------------------------------------------------------------------- #


def test_null_reactive_inverts_motif(default_verdict):
    """L'animat reactif (pi == s) inverse le motif : s predit, pi ne predit plus."""
    v = default_verdict
    assert v["null_inverts"] is True
    assert abs(v["null_decision_partial_s_given_pi_reactive"]) > 0.5  # s predit
    assert abs(v["null_decision_partial_pi_given_s_reactive"]) < 0.3  # pi ne predit plus


# --------------------------------------------------------------------------- #
#  7. Non-trivialite (Prong B) : non-determinisme + sensibility a la puissance #
# --------------------------------------------------------------------------- #


def test_measurement_is_stochastic_two_runs_differ():
    """La mesure comportementale est NON deterministe : 2 runs (seeds differentes)
    donnent des engagements legerement differents -> le test n'est pas trivial."""
    rng1 = np.random.default_rng(1)
    rng2 = np.random.default_rng(2)
    s = np.full(40, 0.7)
    p = np.full(40, 0.6)
    e1 = measure_engagement(s, p, n_trials=80, rng=rng1)
    e2 = measure_engagement(s, p, n_trials=80, rng=rng2)
    assert not np.allclose(e1, e2), "mesure deterministe -> test trivial (Prong B)"


def test_low_power_can_fail_decision_dissociation():
    """A FAIBLE puissance (n=40, trials=80), l'effet propre (proche de zero) de s
    a la decision est noye dans le bruit d'echantillonnage : sur 4 seeds au moins
    une tombe NOT-DISSOCIATED. Ce n'est pas un defaut conceptuel, c'est un manque
    de n -- la sensibility a la puissance est elle-meme la preuve de non-trivialite."""
    verdicts = [case_verdict(seed=sd, n_stimuli=40, n_trials=80)["verdict"]
                for sd in (0, 1, 7, 42)]
    # Au moins un NOT-DISSOCIATED a faible puissance (bruit d'echantillonnage)
    assert any(v == "NOT-DISSOCIATED" for v in verdicts), (
        f"a faible puissance on s'attend a >=1 NOT-DISSOCIATED : {verdicts}")


# --------------------------------------------------------------------------- #
#  8. Robustesse multi-seed a puissance adequate                              #
# --------------------------------------------------------------------------- #


def test_dissociation_robust_across_seeds_at_adequate_power():
    """A puissance adequate (n=120, trials=300), >=3/4 seeds sont dissociees."""
    r = verdict_robust_across_seeds(seeds=(0, 1, 7, 42))
    assert r["robust"] is True, f"non robuste : {r}"
    assert r["frac_dissociated"] >= 0.75


def test_dissociation_full_null_inversion_at_higher_power():
    """A n=160/trials=400, TOUTES les seeds (0,1,7,42,99) sont DISSOCIATED-AT-DECISION
    (null inversé inclus) -- la robustesse s'etend au null adversarial."""
    r = verdict_robust_across_seeds(seeds=(0, 1, 7, 42, 99),
                                    n_stimuli=160, n_trials=400)
    assert all(vv == "DISSOCIATED-AT-DECISION" for vv in r["verdicts"]), (
        f"attendu DISSOCIATED-AT-DECISION sur 5/5 : {r['verdicts']}")
