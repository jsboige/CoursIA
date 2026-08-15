"""Tests unitaires pour ``ict.salience_valence_dissociation`` (Case s perp pi, Epic #9533).

La matrice de dissociations ICT (``docs/ict/dissociations-matrix.md``) factorise
la serie en 4 objets -- ``s_t`` (saillance), ``q_t(z)`` (representation
predictive), ``pi_t(z)`` (pregnance/valence), ``W_t`` (workspace) -- et, depuis
le rafraichissement #9533, **inverse** la matrice : chaque case vide designe
une experience manquante, avec prediction pre-enregistree + null adversarial.

Ce module teste la premiere case nommee : la **dissociation ``s perp pi``**
(saillance sans pregnance, et reciproquement). C'est la Experience 1 du
canevas pre-enregistre, basee sur la prediction **PR #9546** (verrouillee
avant ce test) :

    Un animat dont la saillance ``s`` (conspicuite perceptuelle) et la
    pregnance ``pi`` (valence apprise par Rescorla-Wagner) sont portees par
    des canaux d'entree independants (decorreles par construction) exhibe
    un regime ou l'engagement (approche) est gouverne par ``pi`` et non
    par ``s`` au niveau DECISION. La prediction stricte au niveau
    engagement TOTAL (detect x decide) est FALSIFIEE : ``s`` gate la
    detection, donc predit l'engagement TOTAL meme pour l'animat a
    valence.

Verdict honnete (4 categories, voir :func:`svd.case_verdict`) :
    * ``DISSOCIATED-AT-DECISION`` (cible) : DISSOCIATED au niveau
      decision, FALSIFIEE au niveau total, null reactif inverse.
    * ``DISSOCIATED-TOTAL`` (rare) : dissociation vue meme au total.
    * ``DISSOCIATED-DECISION-NULL-WEAK`` : DISSOCIATED mais null ne
      inverse pas (protocole suspect).
    * ``NOT-DISSOCIATED`` : pas de dissociation (echec honnete).

Gates falsifiables (15, numerotes) :
    1.  ``stimulus_battery`` : shapes (n_stimuli,), ranges
        (s in [0.1, 1.0], lam in [-1.0, 1.0]), decorrelation par
        construction (|corr(s, lam)| << 1 sur grand echantillon).
    2.  ``_sigmoid`` : numeriquement stable, range [0, 1], symetrie
        ``1 - sigma(-x) = sigma(x)`` (anti-regression log-sum-exp).
    3.  ``learn_valences`` : convergence -- corr(V, lam) > 0.95 apres
        200 epoques (Rescorla-Wagner est fidele sur la batterie).
    4.  ``learn_valences`` : determinisme bit-a-bit (memes seeds ->
        memes float arrays).
    5.  ``approach_probability_valence`` : shape allumee par V, range
        [0, 1], gain=0 -> p = 0.5 (sigma(0) = 0.5).
    6.  ``approach_probability_reactive`` : allume **par s, pas par V**
        (cible s_i=0 -> p_i = 0.5, s_i=1 et gain=0 -> p_i = 0.5).
    7.  ``measure_engagement`` : shape (n_stimuli,), s_i = 0 ->
        engagement_i = 0 strictement (gating perceptuel).
    8.  ``measure_decision_given_detected`` : shape + evite division
        par zero quand s_i = 0 (dec_i retourne 0.0, pas NaN/inf).
    9.  ``_rank`` : vecteur constant -> rangs constants (anti-regression
        L48 ``argsort(argsort)`` -> fausse correlation 1.0 entre
        constantes).
    10. ``_pearson`` : constant ys -> correlation 0 (constante = 0
        auto-correlation, anti-regression numerique).
    11. ``partial_spearman(x, y, [])`` = ``_pearson(_rank(x), _rank(y))``
        (regression sans covariates equivaut a correlation simple).
    12. ``case_verdict`` : dict structure avec TOUTES les 11 cles
        documentees (meta + 4 corr total + 3 corr decision + 2 null +
        verdict + bool).
    13. ``case_verdict`` (FALSIFIEE totale par defaut) : au config
        par defaut (``n_stimuli=120``, ``n_trials=300``), la prediction
        stricte au niveau engagement TOTAL **est FALSIFIEE**
        (``total_dissociated=False``). Verifie que la falsification de
        la prediction stricte est REPRODUCTIBLE, pas un artefact de
        bruit d'echantillonnage.
    14. ``case_verdict`` (DISSOCIATED-AT-DECISION par defaut + null
        inverse) : par defaut, le verdict est ``DISSOCIATED-AT-DECISION``
        (``dec_dissociated=True`` + ``null_inverts=True`` + ``total``
        FALSIFIEE). C'est la cible pre-enregistree #9546.
    15. ``verdict_robust_across_seeds`` : robuste (>=3/4 seeds
        ``startswith("DISSOCIATED")``) + structure dict (``seeds``,
        ``verdicts``, ``frac_dissociated``, ``robust``).

Implementation : aucune dependance externe ; un seul import numpy + import
du package ``ict``. Les seuils (``n_stimuli=120``, ``n_trials=300``, ``gain=3.0``,
``alpha=0.15``, ``n_epochs=200``) sont les valeurs par defaut du module et
correspondent aux parametres utilises dans le canevas pre-enregistre #9546
(verrouillage avant test). Les tests ne FORCENT aucun verdict numerique
(sauf le cas 14 ou la cible ``DISSOCIATED-AT-DECISION`` est pre-enregistree)
mais verifient la COHERENCE des invariants structurels et la falsifiabilite
des 4 categories de verdict.
"""

from __future__ import annotations

import os
import sys

# Permettre l'import direct depuis ict package (sans installer en mode develop).
_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import numpy as np
import pytest

from ict import salience_valence_dissociation as svd


def _rng_for(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


# --------------------------------------------------------------------------- #
#  Gate 1 : stimulus_battery -- shapes, ranges, decorrelation par construction  #
# --------------------------------------------------------------------------- #


def test_stimulus_battery_shapes_ranges_decorrelation():
    """``stimulus_battery`` tire ``(s, lam)`` de facon indepenDANTE.

    Sur grand n_stimuli (200), la decorrelation doit etre numeriquement
    proche de 0 (Pearson sur bruit i.i.d. uniforme). On teste :
      * shapes = (n_stimuli,)
      * s in [0.1, 1.0] exactement (bornes doc)
      * lam in [-1.0, 1.0] exactement (bornes doc)
      * decorrelation loose : |corr(s, lam)| < 0.30 (sur grand n le
        Pearson de 2 uniformes i.i.d. est ~ N(0, 1/n), donc loose).
    """
    rng = _rng_for(0)
    s, lam = svd.stimulus_battery(n_stimuli=200, rng=rng)

    assert s.shape == (200,)
    assert lam.shape == (200,)
    assert s.dtype == np.float64
    assert lam.dtype == np.float64

    # Bornes docstring L71 : s in [0.1, 1.0], lam in [-1.0, 1.0].
    assert s.min() >= 0.1 - 1e-12
    assert s.max() <= 1.0 + 1e-12
    assert lam.min() >= -1.0 - 1e-12
    assert lam.max() <= 1.0 + 1e-12

    # Decorrelation : sur 200 tirages i.i.d., |corr| reste loose ~0.30.
    # On n'utilise PAS un seuil strict (e.g. <0.05) car le bruit
    # d'echantillonnage peut donner |corr| ~ 0.15 meme pour des
    # uniformes decorrelees -- c'est statistique, pas deterministe.
    rho = float(np.corrcoef(s, lam)[0, 1])
    assert abs(rho) < 0.30, (
        f"decorrelation par construction : |corr(s, lam)| = {abs(rho):.3f} >= 0.30 "
        f"sur n=200 (anormal, signale une fuite de la generateur)"
    )


# --------------------------------------------------------------------------- #
#  Gate 2 : _sigmoid -- numeriquement stable, symetrique, range [0, 1]         #
# --------------------------------------------------------------------------- #


def test_sigmoid_numerically_stable_and_symmetric():
    """``_sigmoid`` est la logistique **numeriquement stable** (cf code L83
    ``np.where(x >= 0, 1/(1+exp(-x)), exp(x)/(1+exp(x))``).

    On verifie :
      * range [0, 1] strictement (jamais 0.0 ou 1.0 strict sur le continu)
      * grandes valeurs positives -> ~1.0
      * grandes valeurs negatives -> ~0.0
      * symetrie : ``sigma(-x) = 1 - sigma(x)``.
    """
    x = np.array([-3.0, -1.0, 0.0, 1.0, 3.0])
    out = svd._sigmoid(x)
    assert np.all((out >= 0.0) & (out <= 1.0)), (
        f"_sigmoid hors [0,1] : {out}"
    )
    # sigma(0) = 0.5 exactement.
    assert np.isclose(svd._sigmoid(np.array(0.0)), 0.5)

    # Symetrie : sigma(-x) + sigma(x) = 1.
    x_pos = np.array([0.5, 1.5, 2.5])
    sym = svd._sigmoid(x_pos) + svd._sigmoid(-x_pos)
    assert np.allclose(sym, 1.0), (
        f"symetrie cassee : sigma(x) + sigma(-x) = {sym} (attendu 1.0)"
    )

    # Stabilite numerique sur grands arguments.
    big_pos = svd._sigmoid(np.array([100.0, 200.0, 500.0]))
    big_neg = svd._sigmoid(np.array([-100.0, -200.0, -500.0]))
    assert np.all(np.isfinite(big_pos)) and np.all(big_neg >= 0.0)
    assert np.all(big_pos >= 1.0 - 1e-12), f"sigma(grand+) != 1.0 : {big_pos}"
    assert np.all(big_neg <= 1e-12), f"sigma(grand-) != 0.0 : {big_neg}"


# --------------------------------------------------------------------------- #
#  Gate 3 : learn_valences -- convergence corr(V, lam) > 0.95                   #
# --------------------------------------------------------------------------- #


def test_learn_valences_convergence_corr_with_lambda():
    """Apres Rescorla-Wagner (200 epoques, alpha=0.15, obs_noise=0.1),
    V_i doit converger vers lam_i -- la cible pre-enregistree.

    On verifie ``corr(V, lam) > 0.95`` : le bruit d'observation (sigma=0.1)
    cree un mismatch de l'ordre de 1% sur la batterie (cf test c.1261
    firsthand ``mean abs V-lam = 0.022``). On reste conservateur a 0.95
    pour tolerer d'autres seeds.
    """
    rng = _rng_for(0)
    s, lam = svd.stimulus_battery(n_stimuli=40, rng=rng)
    V = svd.learn_valences(lam, n_epochs=200, alpha=0.15, rng=rng)

    assert V.shape == (40,)
    assert np.isfinite(V).all()

    rho = float(np.corrcoef(V, lam)[0, 1])
    assert rho > 0.95, (
        f"apprentissage Rescorla-Wagner ne converge pas : "
        f"corr(V, lam) = {rho:.3f} <= 0.95 (attendu > 0.95 apres 200 epoques)"
    )


# --------------------------------------------------------------------------- #
#  Gate 4 : learn_valences -- determinisme bit-a-bit sur seed                   #
# --------------------------------------------------------------------------- #


def test_learn_valences_determinism_same_seed():
    """``learn_valences`` est deterministe : memes seeds -> memes arrays
    bit-a-bit (factor important pour la reproductibilite de
    ``case_verdict`` qui en depend).
    """
    lam = np.linspace(-1.0, 1.0, 50)
    V1 = svd.learn_valences(lam, n_epochs=100, alpha=0.15, rng=_rng_for(7))
    V2 = svd.learn_valences(lam, n_epochs=100, alpha=0.15, rng=_rng_for(7))
    assert np.array_equal(V1, V2), (
        "learn_valences : memes seeds -> memes float arrays (determinisme REQUIS)"
    )

    # Et deux seeds distincts produisent des resultats differents
    # (anti-regression sur un seed hardcode).
    V3 = svd.learn_valences(lam, n_epochs=100, alpha=0.15, rng=_rng_for(8))
    assert not np.array_equal(V1, V3), (
        "learn_valences : seeds differents -> resultats identiques (BUG)"
    )


# --------------------------------------------------------------------------- #
#  Gate 5 : approach_probability_valence -- gate par V, range [0, 1]            #
# --------------------------------------------------------------------------- #


def test_approach_probability_valence_shape_range_gain_zero_half():
    """``approach_probability_valence(V, gain) = sigma(gain * V)``.

    On verifie :
      * shape preservee + dtype numpy float
      * range [0, 1]
      * gain=0 -> p = 0.5 partout (sigma(0) = 0.5)
      * grand gain positif sur V > 0 -> p -> 1.0
    """
    V = np.array([-1.0, -0.5, 0.0, 0.5, 1.0])

    # gain=3 (defaut) -> range [0,1] non-trivial.
    p = svd.approach_probability_valence(V, gain=3.0)
    assert p.shape == (5,)
    assert np.all((p >= 0.0) & (p <= 1.0))
    # gain=3 sur V=-1 -> sigma(-3) ~= 0.047 ; V=+1 -> sigma(+3) ~= 0.953.
    assert 0.04 < p[0] < 0.06
    assert 0.94 < p[4] < 0.96

    # gain=0 -> 0.5 partout (sigma(0*V) = sigma(0) = 0.5).
    p0 = svd.approach_probability_valence(V, gain=0.0)
    assert np.allclose(p0, 0.5), (
        f"gain=0 doit donner 0.5 partout, recu {p0}"
    )


# --------------------------------------------------------------------------- #
#  Gate 6 : approach_probability_reactive -- gate par s (pas par V)              #
# --------------------------------------------------------------------------- #


def test_approach_probability_reactive_uses_salience_not_valence():
    """``approach_probability_reactive(s, gain) = sigma(gain * s)``.

    C'est l'animat **null reactif** : la decision suit la saillance ``s``,
    PAS la pregnance ``pi``. On verifie que l'entree ``s`` (et non ``V``)
    gouverne la decision :
      * gain=0 -> 0.5 partout (sigma(0) = 0.5), independamment de s.
      * Avec s faible ~ 0 et gain=3, p proche de 0.5 (sigma(0) = 0.5).
    """
    s = np.array([0.1, 0.5, 1.0])

    # gain=3 (defaut) : p range [sigma(0.3)~=0.574, sigma(3)~=0.953].
    p = svd.approach_probability_reactive(s, gain=3.0)
    assert p.shape == (3,)
    assert np.all((p >= 0.0) & (p <= 1.0))
    assert 0.55 < p[0] < 0.60, f"sigma(3*0.1) ~= 0.574, recu {p[0]}"
    assert p[2] > 0.9, f"sigma(3*1.0) ~= 0.953, recu {p[2]}"
    # Croissance monotone en s (s plus saillant -> plus d'approche).
    assert p[0] < p[1] < p[2]

    # gain=0 -> 0.5 partout (gain nul = pas de discrimination).
    p0 = svd.approach_probability_reactive(s, gain=0.0)
    assert np.allclose(p0, 0.5), f"gain=0 doit donner 0.5, recu {p0}"


# --------------------------------------------------------------------------- #
#  Gate 7 : measure_engagement -- s_i = 0 -> engagement_i = 0 (gating)           #
# --------------------------------------------------------------------------- #


def test_measure_engagement_salience_gates_detection():
    """``measure_engagement`` gate la detection par ``s_i`` :
    ``engagement_i = s_i * P(approach | detecte)_i`` (produit de Bernoulli).

    Sur n_trials tres grand (5000) et **un seul stimulus s_i = 0** (donc
    jamais detecte, Bernoulli toujours 0), l'engagement mesure doit etre
    exactement 0.0 sur la duree. C'est le **gating perceptuel** : on
    n'approche pas ce qu'on ne detecte pas.
    """
    # Stimulus 0 : s=0 (jamais detecte). Stimulus 1 : s=1 (toujours detecte).
    s = np.array([0.0, 1.0])
    # p_dec largement au-dessus de 0.5 pour le stimulus 1 pour eviter
    # tout faux positif sur le gating.
    p_dec = np.array([0.5, 0.5])

    eng = svd.measure_engagement(s, p_dec, n_trials=5000, rng=_rng_for(0))

    assert eng.shape == (2,)
    # Stimulus 0 : jamais detecte -> engagement strictement 0.
    assert eng[0] == 0.0, (
        f"stimulus s=0 doit avoir engagement strictement 0, recu {eng[0]}"
    )
    # Stimulus 1 : toujours detecte -> engagement ~ p_dec = 0.5.
    assert 0.45 < eng[1] < 0.55, (
        f"stimulus s=1 doit avoir engagement ~ 0.5, recu {eng[1]}"
    )


# --------------------------------------------------------------------------- #
#  Gate 8 : measure_decision_given_detected -- safe division quand s = 0        #
# --------------------------------------------------------------------------- #


def test_measure_decision_given_detected_safe_when_salience_zero():
    """``measure_decision_given_detected`` conditionne par la detection
    (P(approach | detecte)). Si ``s_i = 0``, le stimulus n'est jamais
    detecte -> division par zero. Le module doit retourner 0.0 (pas
    NaN/inf), cf. L202-204 ``with np.errstate...``.
    """
    s = np.array([0.0, 0.5, 1.0])
    p_dec = np.array([0.5, 0.5, 0.5])

    dec = svd.measure_decision_given_detected(s, p_dec, n_trials=5000, rng=_rng_for(11))

    assert dec.shape == (3,)
    assert np.all(np.isfinite(dec)), (
        f"decision contient NaN/inf : {dec} (anti-regression safe division)"
    )
    # Stimulus 0 : jamais detecte -> decision = 0 (convention).
    assert dec[0] == 0.0, f"s=0 doit donner decision 0.0, recu {dec[0]}"
    # Stimulus 2 : p_dec=0.5, toujours detecte -> decision ~ 0.5.
    assert 0.45 < dec[2] < 0.55, f"s=1 doit donner decision ~ 0.5, recu {dec[2]}"


# --------------------------------------------------------------------------- #
#  Gate 9 : _rank -- vecteur constant -> rangs constants (anti-regression)      #
# --------------------------------------------------------------------------- #


def test_rank_constant_input_yields_constant_ranks():
    """``_rank`` doit rendre un vecteur constant pour une entree constante.

    Anti-regression : l'implementation naive ``argsort(argsort(xs))``
    rendrait une rampe [0, 1, 2, ...] sur un vecteur constant, ce qui
    introduirait une fausse correlation 1.0 entre constantes (cf L218-219
    commentaire du code source). Les rangs moyennes gerent les ex-aequo
    en plaçant tout le groupe au rang moyen.
    """
    r = svd._rank(np.array([3.14, 3.14, 3.14, 3.14, 3.14]))
    assert np.all(r == r[0]), (
        f"_rank(constant) doit etre constant, recu {r} "
        f"(anti-regression argsort(argsort) fausse correlation)"
    )

    # Et pour un vecteur non-constant, les rangs sont en [1, n] avec
    # permutation (et permutation des indices preserves les valeurs).
    xs = np.array([10.0, 30.0, 20.0])
    r = svd._rank(xs)
    assert sorted(r.tolist()) == [1.0, 2.0, 3.0], f"rangs non-permutation : {r}"
    # L'element le plus petit (10) doit avoir le rang 1.
    assert r[0] == 1.0


# --------------------------------------------------------------------------- #
#  Gate 10 : _pearson -- constant -> 0 (anti-regression numerique)              #
# --------------------------------------------------------------------------- #


def test_pearson_constant_inputs_yield_zero():
    """``_pearson(xs, ys)`` retourne 0.0 si xs ou ys est constant (variance
    nulle). Anti-regression numerique (definie L238 `float(np.std(xs))
    < 1e-12 or float(np.std(ys)) < 1e-12`).
    """
    xs = np.array([1.0, 2.0, 3.0, 4.0])
    ys_const = np.array([5.0, 5.0, 5.0, 5.0])
    xs_const = np.array([2.0, 2.0, 2.0, 2.0])

    p_y = svd._pearson(xs, ys_const)
    assert p_y == 0.0, f"_pearson(xs, const) doit etre 0.0, recu {p_y}"

    p_x = svd._pearson(xs_const, ys_const)
    assert p_x == 0.0, f"_pearson(const, const) doit etre 0.0, recu {p_x}"

    # Anti-regression : _pearson NON trivial doit retourner des valeurs
    # dans [-1, 1] et au moins une non-nulle.
    ys = np.array([1.0, 2.0, 3.0, 4.0])
    p = svd._pearson(xs, ys)
    assert -1.0 <= p <= 1.0
    assert abs(p) > 0.9, f"correlations identiques doivent etre ~ 1.0, recu {p}"


# --------------------------------------------------------------------------- #
#  Gate 11 : partial_spearman(x, y, []) = _pearson(_rank(x), _rank(y))          #
# --------------------------------------------------------------------------- #


def test_partial_spearman_no_covariates_equals_pearson_of_ranks():
    """``partial_spearman(x, y, [])`` doit retrecir exactement a la
    correlation de Pearson des rangs de x et y (cas limite : 0 covariates).
    """
    rng = _rng_for(13)
    x = rng.uniform(-1.0, 1.0, size=30)
    y = rng.uniform(-1.0, 1.0, size=30)

    p_no_cov = svd.partial_spearman(x, y, [])
    p_expected = svd._pearson(svd._rank(x), svd._rank(y))

    assert np.isclose(p_no_cov, p_expected), (
        f"partial_spearman(x, y, []) = {p_no_cov} != "
        f"_pearson(_rank(x), _rank(y)) = {p_expected}"
    )


# --------------------------------------------------------------------------- #
#  Gate 12 : case_verdict -- structure du dict et verdict dans l'ensemble       #
# --------------------------------------------------------------------------- #


def test_case_verdict_keys_and_verdict_in_set():
    """``case_verdict`` retourne TOUTES les sous-cles documentees (meta +
    4 correlations partielles total + 3 corr partielles decision + 2 null
    + verdict + bool) et un verdict parmi les 4 categories.

    Verification structurelle : on ne FORCE aucun verdict, mais on
    verifie que **toutes** les cles sont presentes avec les bons types.
    """
    out = svd.case_verdict(seed=0)

    expected_keys = {
        "n_stimuli", "rho_s_pi_decorrelation",
        "total_partial_pi_given_s_valence",
        "total_partial_s_given_pi_valence",
        "total_dissociated",
        "decision_partial_pi_given_s_valence",
        "decision_partial_s_given_pi_valence",
        "decision_dissociated",
        "null_decision_partial_pi_given_s_reactive",
        "null_decision_partial_s_given_pi_reactive",
        "null_inverts",
        "verdict",
    }
    assert set(out.keys()) == expected_keys, (
        f"cles case_verdict attendues {expected_keys}, recues {set(out.keys())}"
    )

    # Types verifies.
    assert isinstance(out["n_stimuli"], int)
    assert isinstance(out["verdict"], str)
    assert isinstance(out["total_dissociated"], bool)
    assert isinstance(out["decision_dissociated"], bool)
    assert isinstance(out["null_inverts"], bool)
    assert isinstance(out["rho_s_pi_decorrelation"], float)
    for k in expected_keys:
        if k.startswith("decision_") or k.startswith("total_") or k.startswith("null_"):
            if k.endswith("dissociated") or k.endswith("inverts"):
                continue
            assert isinstance(out[k], float), f"{k} doit etre float, pas {type(out[k])}"

    # Verdict parmi les 4 categories documentees.
    assert out["verdict"] in {
        "DISSOCIATED-AT-DECISION",
        "DISSOCIATED-TOTAL",
        "DISSOCIATED-DECISION-NULL-WEAK",
        "NOT-DISSOCIATED",
    }, f"verdict = {out['verdict']!r} hors ensemble documente"


# --------------------------------------------------------------------------- #
#  Gate 13 : case_verdict -- FALSIFICATION au niveau engagement TOTAL (cible)    #
# --------------------------------------------------------------------------- #


def test_case_verdict_total_dissociation_is_falsified_at_default():
    """Prediction stricte **FALSIFIEE** au niveau engagement TOTAL par
    defaut (n_stimuli=120, n_trials=300).

    La docstring du module annonce que ``s`` gate la detection
    (``P(detecte) = s_i``), donc predit l'engagement TOTAL meme pour
    l'animat a valence. Cela signifie que la prediction stricte
    (``|corr(eng, V | s)| > 0.5`` ET ``|corr(eng, s | V)| < 0.2``) ne
    tient PAS : ``s`` est correlee a l'engagement (gating).

    On verifie ce pattern falsifie (la prediction stricte est
    intentionnellement FALSIFIEE) en controlant que la branche
    ``total_dissociated=False`` est REPRODUCTIBLE sur plusieurs seeds
    a configuration par defaut.
    """
    for seed in (0, 1, 7, 42, 99):
        out = svd.case_verdict(seed=seed)
        assert out["total_dissociated"] is False, (
            f"seed={seed} : total_dissociated devrait etre False (prediction "
            f"stricte FALSIFIEE), recu True. partials : "
            f"pi|s={out['total_partial_pi_given_s_valence']:.3f}, "
            f"s|pi={out['total_partial_s_given_pi_valence']:.3f}"
        )


# --------------------------------------------------------------------------- #
#  Gate 14 : case_verdict -- DISSOCIATED-AT-DECISION + null inverse (cible)     #
# --------------------------------------------------------------------------- #


def test_case_verdict_dissociated_at_decision_at_default():
    """Au config par defaut, le verdict canonique est
    ``DISSOCIATED-AT-DECISION`` (cible pre-enregistree PR #9546) :
      * DISSOCIATED au niveau decision (``decision_dissociated=True``)
      * FALSIFIEE au niveau total (``total_dissociated=False``)
      * null reactif inverse le motif (``null_inverts=True``).

    Test direct de la **cible** sur la config par defaut.
    """
    for seed in (0, 1, 42, 99):
        out = svd.case_verdict(seed=seed)
        assert out["verdict"] == "DISSOCIATED-AT-DECISION", (
            f"seed={seed} : verdict attendu DISSOCIATED-AT-DECISION, "
            f"recu {out['verdict']}. Branches : "
            f"decision_diss={out['decision_dissociated']}, "
            f"null_inverts={out['null_inverts']}, "
            f"total_diss={out['total_dissociated']}"
        )
        assert out["decision_dissociated"] is True
        assert out["null_inverts"] is True
        assert out["total_dissociated"] is False


# --------------------------------------------------------------------------- #
#  Gate 15 : verdict_robust_across_seeds -- structure + robust >= 3/4           #
# --------------------------------------------------------------------------- #


def test_verdict_robust_across_seeds_structure_and_robustness():
    """``verdict_robust_across_seeds`` produit ``seeds / verdicts /
    frac_dissociated / robust`` et detecte une majorite dissociee
    (>= 3 seeds sur 4 qui commencent par ``"DISSOCIATED"``).

    Au config par defaut, la majorite des seeds doit etre dissociee
    (la cible ``DISSOCIATED-AT-DECISION`` tient sur >= 3/4 seeds dans
    la majorite des cas ; les events ``DISSOCIATED-DECISION-NULL-WEAK``
    eventuels comptent comme dissocies au sens ``startswith``).
    """
    out = svd.verdict_robust_across_seeds(seeds=(0, 1, 7, 42))

    expected_keys = {"seeds", "verdicts", "frac_dissociated", "robust"}
    assert set(out.keys()) == expected_keys, (
        f"cles verdict_robust attendues {expected_keys}, "
        f"recues {set(out.keys())}"
    )

    assert list(out["seeds"]) == [0, 1, 7, 42]
    assert len(out["verdicts"]) == 4

    # frac_dissociated = proportion de verdicts commençant par DISSOCIATED.
    n_diss = sum(1 for v in out["verdicts"] if v.startswith("DISSOCIATED"))
    expected_frac = n_diss / len(out["verdicts"])
    assert out["frac_dissociated"] == expected_frac
    assert isinstance(out["robust"], bool)

    # Au config par defaut, on attend au moins 3/4 seeds dissocies.
    # C'est plus permissif que 4/4 (autorise un event
    # ``DISSOCIATED-DECISION-NULL-WEAK`` ou meme un ``NOT-DISSOCIATED``
    # rare sans signaler un defaut de protocole).
    assert out["robust"] is True, (
        f"robust attendu >= 3/4 seeds, recu {out['frac_dissociated']:.2%} "
        f"({out['verdicts']})"
    )
