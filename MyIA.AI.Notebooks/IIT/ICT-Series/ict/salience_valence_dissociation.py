"""Dissociation saillance / pregnance (Case s perp pi, Epic #9533 / #8077).

La matrice de dissociations ICT (``docs/ict/dissociations-matrix.md``) factorise
la serie en 4 objets -- ``s_t`` (saillance), ``q_t(z)`` (representation
predictive), ``pi_t(z)`` (pregnance/valence), ``W_t`` (workspace) -- et, depuis
#9533, **inverse** la matrice : chaque case vide designe une experience
manquante, avec prediction pre-enregistree + null adversarial. Ce module teste
la premiere case nommee : la dissociation ``s perp pi`` (saillance sans
pregnance, et reciproquement).

Prediction pre-enregistree (PR #9546, verrouillee avant ce test) :
    Un animat dont la saillance ``s`` (conspicuite perceptuelle) et la pregnance
    ``pi`` (valence apprise par Rescorla-Wagner) sont portees par des canaux
    d'entree independants (decorreles par construction) exhibe un regime ou
    l'engagement (approche) est gouverne par ``pi`` et non par ``s`` :

        |corr(engagement, pi | s)| > 0.5   (pi : pouvoir predictif propre)
        |corr(engagement, s | pi)| < 0.2   (s : pas de pouvoir predictif propre)

Null adversarial : un animat reactif pur (pi == s, pas d'apprentissage de
valence -- l'engagement suit la conspicuite) inverse le motif -- ``s`` predit,
``pi`` ne predit plus. Si le null ne s'inverse pas, le protocole est suspect.

Verdict du test (honnete, multi-seed >= 4) :
    La prediction stricte ci-dessus (sur l'engagement TOTAL = detect x decide)
    est **FALSIFIEE** : ``s`` gate la detection (``P(detecte)=s_i``), donc ``s``
    predit l'engagement total meme pour l'animat a valence -- on n'approche pas
    ce qu'on ne detecte pas (``|corr(eng, s | V)| ~ 0.8``). Ce n'est pas un defaut
    de protocole mais la mecanique perceptuelle elle-meme. La dissociation tient
    en revanche au niveau **DECISION sachant detection** (``P(approach|detecte)``)
    ou ``s`` est inerte (``|corr| < 0.2``) et ``pi`` gouverne (``|corr| > 0.9``),
    et le null reactif y inverse le motif. Resultat nuance : **la saillance compte
    pour VOIR, la pregnance pour AGIR**. Verdict : ``DISSOCIATED-AT-DECISION``.

Substrat
--------
Numpy uniquement, CPU-only. La saillance ``s_i`` d'un stimulus est sa
conspicuite perceptuelle (contraste, amplitude) dans [0, 1] ; la pregnance
``pi_i`` est sa vraie valeur de recompense ``lambda_i`` dans [-1, +1], apprise
par Rescorla-Wagner (``V_i <- V_i + alpha (lambda_i - V_i)``). Les deux sont
tirees independamment sur la batterie de stimuli (decorrelees par construction).

L'animat a **valence** apprend ``V_i`` puis decide l'approche selon ``sigma(V_i)``
(engagement gouverne par la pregnance apprise, ignore ``s`` pour la decision).
L'animat **reactif** (null) decide l'approche selon ``sigma(s_i)`` (engagement
gouverne par la saillance, pas d'apprentissage). Les deux percoivent ``s_i`` ;
seul le valence ignore ``s`` a la decision d'approche -- c'est la dissociation
mesuree.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Batterie de stimuli : s (conspicuite) et pi (vraie recompense) decorreles    #
# --------------------------------------------------------------------------- #


def stimulus_battery(
    n_stimuli: int = 40,
    rng: Optional[np.random.Generator] = None,
) -> Tuple[np.ndarray, np.ndarray]:
    """Tire une batterie de ``n_stimuli`` stimuli aux attributs **independants**.

    Renvoie ``(s, lam)`` ou ``s`` est la conspicuite (saillance perceptuelle,
    uniforme [0.1, 1.0]) et ``lam`` la vraie recompense (pregnance cible,
    uniforme [-1.0, +1.0]). Les deux sont tirees **independamment** ->
    ``corr(s, lam) ~ 0`` par construction (pre-requis de la dissociation).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    s = rng.uniform(0.1, 1.0, size=int(n_stimuli))
    lam = rng.uniform(-1.0, 1.0, size=int(n_stimuli))
    return s, lam


def _sigmoid(x: np.ndarray) -> np.ndarray:
    """Logistique numeriquement stable."""
    return np.where(x >= 0, 1.0 / (1.0 + np.exp(-x)), np.exp(x) / (1.0 + np.exp(x)))


# --------------------------------------------------------------------------- #
#  Apprentissage Rescorla-Wagner de la valence                                 #
# --------------------------------------------------------------------------- #


def learn_valences(
    lam: np.ndarray,
    n_epochs: int = 200,
    alpha: float = 0.15,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """Apprend la valence ``V_i`` de chaque stimulus par Rescorla-Wagner.

    A chaque epoque, un stimulus ``i`` est tire (uniforme), expose a sa vraie
    recompense bruitee ``lambda_i + noise``, et ``V_i`` est mis a jour :
    ``V_i <- V_i + alpha (lambda_obs - V_i)``. Renvoie ``V`` converge vers
    ``lam`` (l'apprentissage est fidele sur la batterie), independamment de la
    conspicuite ``s`` (qui n'entre PAS dans l'apprentissage).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    lam = np.asarray(lam, dtype=float)
    n = lam.size
    V = np.zeros(n, dtype=float)
    obs_noise = 0.1
    for _ in range(int(n_epochs)):
        order = rng.integers(0, n, size=n)          # n exposes par epoque
        for i in order:
            obs = float(lam[i]) + float(obs_noise) * float(rng.standard_normal())
            V[i] = V[i] + float(alpha) * (obs - V[i])
    return V


# --------------------------------------------------------------------------- #
#  Engagement : approche par l'animat a valence vs l'animat reactif (null)     #
# --------------------------------------------------------------------------- #


def approach_probability_valence(V: np.ndarray, gain: float = 3.0) -> np.ndarray:
    """Probabilite d'approche a la **decision** (animat a valence) :
    ``P(approach | detecte) = sigma(gain * V)``.

    La decision d'approche est gouvernee par la pregnance apprise ``V`` ; la
    saillance ``s`` n'entre PAS dans la decision (uniquement dans la detection,
    cf ``measure_engagement``). C'est la dissociation cible.
    """
    return _sigmoid(float(gain) * np.asarray(V, dtype=float))


def approach_probability_reactive(s: np.ndarray, gain: float = 3.0) -> np.ndarray:
    """Probabilite d'approche a la decision (animat **reactif**, null) :
    ``P(approach | detecte) = sigma(gain * s)``.

    La decision suit la saillance ``s`` ; pas d'apprentissage de valence
    (``pi == s``). C'est le null adversarial : si le protocole est sain, cet
    animat inverse le motif (``s`` predit, ``pi`` ne predit plus).
    """
    return _sigmoid(float(gain) * np.asarray(s, dtype=float))


def measure_engagement(
    s: np.ndarray,
    p_approach_given_detected: np.ndarray,
    n_trials: int = 80,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """Engagement **TOTAL** mesure comportementalement (non deterministe) :
    fraction d'essais ou l'animat approche le stimulus ``i``, sur ``n_trials``.

    Rend le test NON trivial (SOTA Prong B) : la detection est **gatee par la
    saillance** (``P(detecte) = s_i``), et la decision est bruitee (Bernoulli).
    L'engagement total combine les deux canaux : ``E[eng_i] = s_i *
    p_approach_given_detected_i``. La saillance ``s`` a donc un effet (gating de
    detection) meme pour l'animat a valence -- la dissociation n'est PAS
    garantie par construction a ce niveau (elle est falsifiee : cf verdict).
    """
    if rng is None:
        rng = np.random.default_rng(0)
    s = np.asarray(s, dtype=float)
    p_dec = np.asarray(p_approach_given_detected, dtype=float)
    n = s.size
    counts = np.zeros(n, dtype=float)
    for _ in range(int(n_trials)):
        detected = rng.random(n) < s
        counts += (rng.random(n) < p_dec) & detected
    return counts / float(n_trials)


def measure_decision_given_detected(
    s: np.ndarray,
    p_approach_given_detected: np.ndarray,
    n_trials: int = 80,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """Decision ** Sachant detection** : fraction d'essais ou l'animat approche
    parmi les essais ou il a detecte le stimulus.

    C'est la mesure conceptuellement correcte de l'« approche » dans le sens de
    la dissociation « saillant sans importance » (leurre) : un stimulus salient
    est detecte (s eleve) mais, s'il est neutre (V ~ 0), n'est **pas** approche.
    En conditionnant par la detection, on isole la DECISION (gouvernee par V pour
    l'animat a valence, par s pour le reactif) du gating perceptuel. Mesure
    bruitee (Bernoulli) -> correlations non triviales.
    """
    if rng is None:
        rng = np.random.default_rng(0)
    s = np.asarray(s, dtype=float)
    p_dec = np.asarray(p_approach_given_detected, dtype=float)
    n = s.size
    approach_counts = np.zeros(n, dtype=float)
    detect_counts = np.zeros(n, dtype=float)
    for _ in range(int(n_trials)):
        detected = rng.random(n) < s
        approach = (rng.random(n) < p_dec) & detected
        detect_counts += detected
        approach_counts += approach
    # P(approach | detected) ; evite la division par zero (stimuli jamais detectes)
    with np.errstate(invalid="ignore", divide="ignore"):
        dec = np.where(detect_counts > 0, approach_counts / detect_counts, 0.0)
    return dec



# --------------------------------------------------------------------------- #
#  Statistique : correlation partielle a 1 covariable (rangs moyennes, FWL)    #
# --------------------------------------------------------------------------- #


def _rank(xs: np.ndarray) -> np.ndarray:
    """Rangs **moyennes** (ex-aequo tolerants), miroir ``scipy.stats.rankdata``.

    Crucial : ``argsort(argsort(xs))`` rend une rampe ``[0,1,...]`` sur un
    vecteur constant -> fausses correlations. Les rangs moyennes rendent
    constant -> constant -> ``_pearson`` garde a 0. (cf basin_family._rank.)"""
    xs = np.asarray(xs, dtype=float)
    n = xs.size
    order = np.argsort(xs, kind="mergesort")
    ranks = np.empty(n, dtype=float)
    sorted_vals = xs[order]
    i = 0
    while i < n:
        j = i
        while j + 1 < n and sorted_vals[j + 1] == sorted_vals[i]:
            j += 1
        avg = 0.5 * (i + j) + 1.0
        ranks[order[i:j + 1]] = avg
        i = j + 1
    return ranks


def _pearson(xs: np.ndarray, ys: np.ndarray) -> float:
    """Correlation de Pearson (rendement 0 si variance nulle)."""
    if xs.size < 2 or float(np.std(xs)) < 1e-12 or float(np.std(ys)) < 1e-12:
        return 0.0
    xs = xs - xs.mean()
    ys = ys - ys.mean()
    denom = float(np.sqrt((xs * xs).sum() * (ys * ys).sum()))
    return float((xs * ys).sum() / denom) if denom > 0 else 0.0


def _residuals_against(y: np.ndarray, covariates: np.ndarray) -> np.ndarray:
    """Residus de la regression de ``y`` sur les ``covariates`` (+ intercept)."""
    n = y.size
    Z = np.column_stack([np.ones(n), covariates])
    coef, *_ = np.linalg.lstsq(Z, y, rcond=None)
    return y - Z @ coef


def partial_spearman(x: np.ndarray, y: np.ndarray,
                     covariates: Sequence[np.ndarray]) -> float:
    """Correlation partielle de Spearman de ``x`` avec ``y`` controlant les
    ``covariates`` (FWL sur les rangs). Generalise a N covariables."""
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    if x.size < 3:
        return 0.0
    rx = _rank(x)
    ry = _rank(y)
    if not covariates:
        return _pearson(rx, ry)
    C = np.column_stack([_rank(np.asarray(c, dtype=float)) for c in covariates])
    ex = _residuals_against(rx, C)
    ey = _residuals_against(ry, C)
    return _pearson(ex, ey)


# --------------------------------------------------------------------------- #
#  Verdict : la 1ʳᵉ case s perp pi (prediction pre-enregistree #9546)          #
# --------------------------------------------------------------------------- #


def case_verdict(
    n_stimuli: int = 120,
    n_epochs: int = 200,
    alpha: float = 0.15,
    gain: float = 3.0,
    n_trials: int = 300,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Verdict de la case ``s perp pi`` : l'engagement est-il gouverne par la
    pregnance apprise ``pi`` (valence) et non par la saillance ``s`` ?

    Deux niveaux de mesure (sur la batterie aux attributs decorreles), chacun
    NON deterministe (Bernoulli sur ``n_trials`` essais, detection gatee par
    ``s``) -> test non trivial (SOTA Prong B) :

    * **Engagement TOTAL** ``E[eng_i] = s_i * p(approach|detecte)_i`` (detect x
      decide). Prediction stricte pre-enregistree (PR #9546) :
      ``|corr(eng, V | s)| > 0.5`` ET ``|corr(eng, s | V)| < 0.2``. **FALSIFIEE** :
      ``s`` gate la detection, donc ``s`` predit l'engagement total meme pour
      l'animat a valence (on n'approche pas ce qu'on ne detecte pas). Robuste.
    * **DECISION sachant detection** ``P(approach | detecte)`` (isole la decision
      du gating perceptuel). C'est la « vraie » dissociation (leurre : un stimulus
      saillant est detecte mais, s'il est neutre ``V ~ 0``, n'est PAS approche) :
      ``|corr(dec, V | s)| > 0.5`` ET ``|corr(dec, s | V)| < 0.2``. Tient a
      puissance adequate (``n_stimuli >= 120``, ``n_trials >= 300``) : a faible n
      l'effet propre (proche de zero) de ``s`` a la decision est noye dans le
      bruit d'echantillonnage -> ``NOT-DISSOCIATED`` par manque de puissance, pas
      par defaut conceptuel.

    Verdict honnete (jamais "promising") :

    * ``DISSOCIATED-AT-DECISION`` : prediction stricte (engagement total)
      FALSIFIEE, dissociation CONFIRMEE au niveau decision, **et** le null reactif
      inverse le motif (``s`` predit, ``V`` ne predit plus). Resultat scientifique
      nuance : la saillance compte pour VOIR, la pregnance pour AGIR.
    * ``DISSOCIATED-TOTAL`` : dissociation vue meme au niveau engagement total
      (rare -- requiert que le gating soit negligeable) + null inverse.
    * ``DISSOCIATED-DECISION-NULL-WEAK`` : dissociation au niveau decision mais le
      null n'inverse pas -> protocole suspect (artefact de mesure possible).
    * ``NOT-DISSOCIATED`` : la saillance parasite la decision, ou la pregnance ne
      predit pas, ou puissance insuffisante (resultat honnete, pas un echec).
    """
    rng = np.random.default_rng(seed)
    s, lam = stimulus_battery(n_stimuli=n_stimuli, rng=rng)
    V = learn_valences(lam, n_epochs=n_epochs, alpha=alpha, rng=rng)

    p_v = approach_probability_valence(V, gain=gain)
    p_r = approach_probability_reactive(s, gain=gain)

    # Niveau 1 : engagement TOTAL (detect x decide) -- la prediction stricte
    # pre-enregistree y est FALSIFIEE : s gate la detection, donc predit l'engagement.
    eng_v = measure_engagement(s, p_v, n_trials=n_trials, rng=rng)
    eng_r = measure_engagement(s, p_r, n_trials=n_trials, rng=rng)
    total_partial_pi = partial_spearman(V, eng_v, [s])
    total_partial_s = partial_spearman(s, eng_v, [V])
    total_dissociated = bool(abs(total_partial_pi) > 0.5 and abs(total_partial_s) < 0.2)

    # Niveau 2 : DECISION sachant detection (la « vraie » dissociation leurre) :
    # la saillance ne predit plus l'approche une fois la detection controlee.
    dec_v = measure_decision_given_detected(s, p_v, n_trials=n_trials, rng=rng)
    dec_r = measure_decision_given_detected(s, p_r, n_trials=n_trials, rng=rng)
    dec_partial_pi = partial_spearman(V, dec_v, [s])
    dec_partial_s = partial_spearman(s, dec_v, [V])
    dec_dissociated = bool(abs(dec_partial_pi) > 0.5 and abs(dec_partial_s) < 0.2)
    # null reactif au niveau decision : s predit, V ne predit plus
    null_dec_partial_pi = partial_spearman(V, dec_r, [s])
    null_dec_partial_s = partial_spearman(s, dec_r, [V])
    null_inverts = bool(abs(null_dec_partial_s) > 0.5 and abs(null_dec_partial_pi) < 0.2)

    # corr(s, V) doit etre ~0 (decorrele par construction) -- diagnostic
    rho_s_pi = _pearson(_rank(s), _rank(V))

    # Verdict honnete : la prediction stricte (engagement total) est FALSIFIEE ;
    # la dissociation tient au niveau decision (la ou elle est conceptuellement
    # attendue -- leurre : salient-detected mais non-approche si neutre).
    if (not total_dissociated) and dec_dissociated and null_inverts:
        verdict = "DISSOCIATED-AT-DECISION"
    elif total_dissociated and null_inverts:
        verdict = "DISSOCIATED-TOTAL"
    elif dec_dissociated and not null_inverts:
        verdict = "DISSOCIATED-DECISION-NULL-WEAK"
    else:
        verdict = "NOT-DISSOCIATED"

    return {
        "n_stimuli": int(s.size),
        "rho_s_pi_decorrelation": float(rho_s_pi),
        # niveau engagement total (prediction stricte -> falsifiee)
        "total_partial_pi_given_s_valence": float(total_partial_pi),
        "total_partial_s_given_pi_valence": float(total_partial_s),
        "total_dissociated": total_dissociated,
        # niveau decision-sachant-detection (la vraie dissociation)
        "decision_partial_pi_given_s_valence": float(dec_partial_pi),
        "decision_partial_s_given_pi_valence": float(dec_partial_s),
        "decision_dissociated": dec_dissociated,
        "null_decision_partial_pi_given_s_reactive": float(null_dec_partial_pi),
        "null_decision_partial_s_given_pi_reactive": float(null_dec_partial_s),
        "null_inverts": null_inverts,
        "verdict": verdict,
    }


def verdict_robust_across_seeds(seeds: Sequence[int] = (0, 1, 7, 42),
                                **kw) -> Dict[str, object]:
    """Robustesse multi-seed de la case ``s perp pi`` (la valence est aprende ->
    le seed traverse l'apprentissage, mesure de robustesse reelle)."""
    verdicts = [case_verdict(seed=int(s), **kw)["verdict"] for s in seeds]
    n_diss = sum(1 for v in verdicts if v.startswith("DISSOCIATED"))
    return {
        "seeds": list(seeds),
        "verdicts": verdicts,
        "frac_dissociated": float(n_diss / len(verdicts)),
        "robust": bool(n_diss >= max(2, len(verdicts) - 1)),  # >=3/4 seeds
    }
