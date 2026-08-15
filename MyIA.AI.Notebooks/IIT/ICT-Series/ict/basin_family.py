"""Famille de substrats a decouplage construit (Pont #1-bis, Epic #8077 / #9531).

Le Pont #1 de :mod:`ict.bridge_testing` (``sigma`` stabilite -> recuperabilite,
PR #8944) a ete **FALSIFIE** sur la fronce de Thom : la correlation partielle de
``sigma`` (controle de la largeur de bassin) tombe a ~0, et c'est la largeur de
bassin (position du col) qui gouverne la portee de recuperation (``rho`` ~ 0.996).

Mais sur la fronce, ``sigma`` (courbure locale ``V''(x*)``) et la largeur de
bassin sont **couples par construction** (``rho_sigma_width`` ~ 0.93). Le verdict
de falsification est donc acquis *sur ce substrat* ; sa **generalite est
indecidable** sans un substrat ou les deux quantites varient independamment.

Ce module (issue #9531, mandat user 2026-08-06, chantier 1/3) construit une
**famille parametrique de substrats ou ``sigma`` et la largeur de bassin varient
independamment par construction** (deux cadrans independants), rejoue le
protocole du Pont #1, et tranche entre trois verdicts :

* ``CONFIRMED-NEGATIVE`` : ``sigma`` n'a de pouvoir predictif nulle part dans la
  famille -> le Pont #1 est un vrai negatif general (la geometrie du bassin
  gouverne partout).
* ``SUBSTRATE-ARTIFACT`` : ``sigma`` regagne un pouvoir predictif propre dans un
  coin de la famille -> le verdict fronce etait un artefact de couplage.
* ``INCONCLUSIVE`` : decouplage insuffisant ou signal sous le bruit multi-seed.

Le substrat : le double-puits symetrique
----------------------------------------
``V(x) = a x^4 - b x^2``  (``a > 0``, ``b > 0``). Ses trois quantites
geometriques se separent algebriquement (prototype ICT-8 section 8, eleve ici au
rang de module reutilisable) :

* **courbure au minimum** ``sigma = V''(x*) = 4 b``  -> depend de ``b`` **seul** ;
* **largeur de demi-bassin** (vers le col en ``x = 0``) ``width = sqrt(b / (2 a))``
  -> depend de ``a`` **et** ``b`` ;
* **hauteur de barriere** ``barrier = V(0) - V(x*) = b^2 / (4 a)`` -> depend de
  ``a`` **et** ``b``.

L'independance (cadrans) : on echantillonne ``sigma`` et ``width`` sur deux
grilles separees. Chaque couple cible ``(sigma, width)`` se realise par
``b = sigma / 4`` puis ``a = b / (2 width^2)``. Sur le produit cartesien des deux
grilles, ``corr(sigma, width) ~ 0`` par construction.

Le piege (rendant le verdict NON trivial, contrairement a un decouplage naif) :
la **barriere** ``= sigma * width^2 / 8`` **co-varie** avec le produit des deux.
Controler la largeur seule (comme le Pont #1) laisse donc fuir la barriere. Le
verdict decisif de ce module controlera **la largeur ET la barriere** (correlation
partielle a deux covariables, methode des residus de Frisch-Waugh-Lovell). C'est
la rigueur statistique qui manquait au Pont #1 et que la famille rend enfin
applicable.

Conventions
-----------
Numpy uniquement (pas de scipy / pingouin / statsmodels), conformement a
:mod:`ict.bridge_testing`. Les correlations partielles a ``N`` covariables se
calculent par regression des residus (FWL), ce qui generalise la forme analytique
a 1 covariable de ``bridge_testing._partial_spearman``.

Le module se nomme ``basin_family`` (et non ``basin_geometry`` comme suggere dans
#9531) pour eviter la collision de nom avec la **fonction** existante
``bridge_testing.basin_geometry(a, b)`` -- la famille est aussi une generalisation
(profil a 5 quantites : ``x*, sigma, width, col, barrier``) de la geometrie
a 4 quantites du Pont #1.
"""

from __future__ import annotations

from typing import Dict, List, Sequence, Tuple

import numpy as np

from . import catastrophe as cat


# --------------------------------------------------------------------------- #
#  Substrat : double-puits symetrique V(x) = a x^4 - b x^2                       #
# --------------------------------------------------------------------------- #


def double_well_potential(x, a: float, b: float):
    """Potentiel double-puits symetrique ``V(x) = a x^4 - b x^2``.

    Deux minima stables en ``x = +/- sqrt(b / (2 a))``, un col (equilibre
    instable) en ``x = 0``. ``a > 0``, ``b > 0``.
    """
    x = np.asarray(x, dtype=float)
    return float(a) * x ** 4 - float(b) * x ** 2


def double_well_force(x, a: float, b: float):
    """Force ``-V'(x) = -(4 a x^3 - 2 b x) = 2 b x - 4 a x^3`` (descente)."""
    x = np.asarray(x, dtype=float)
    return 2.0 * float(b) * x - 4.0 * float(a) * x ** 3


def double_well_curvature(x, a: float, b: float):
    """Courbure ``V''(x) = 12 a x^2 - 2 b``. Aux minima ``x*^2 = b/(2a)`` ->
    ``V''(x*) = 12 a (b/2a) - 2 b = 4 b`` (independant de ``a`` au minimum).

    Au col ``x = 0`` : ``V''(0) = -2 b < 0`` (equilibre instable, attendu).
    """
    x = np.asarray(x, dtype=float)
    return 12.0 * float(a) * x ** 2 - 2.0 * float(b)


def double_well_equilibria(a: float, b: float) -> List[Tuple[float, bool]]:
    """Equilibres du double-puits : col en ``0`` (instable), minima en
    ``+/- sqrt(b/(2a))`` (stables). Retourne ``[(x, stable), ...]`` trie."""
    a = float(a)
    b = float(b)
    if a <= 0.0 or b <= 0.0:
        return []
    half_width = float(np.sqrt(b / (2.0 * a)))
    return [(-half_width, True), (0.0, False), (half_width, True)]


def relax_double_well(x0: float, a: float, b: float,
                      dt: float = 0.01, steps: int = 5000) -> float:
    """Descente de gradient ``dx/dt = -V'(x)`` depuis ``x0`` sur le double-puits.

    Converge vers le minimum du **bassin** contenant ``x0`` (Euler explicite),
    mirroring :func:`ict.catastrophe.relax_to_equilibrium`. Le signe de ``x0``
    decide du bassin (``x0 > 0`` -> minimum droit, ``x0 < 0`` -> gauche).
    """
    x = float(x0)
    for _ in range(int(steps)):
        x = x + dt * float(double_well_force(x, a, b))
    return x


# --------------------------------------------------------------------------- #
#  Profil geometrique (5 quantites) et decouplage (sigma, width)                #
# --------------------------------------------------------------------------- #


def basin_profile(a: float, b: float) -> List[Tuple[float, float, float, float, float]]:
    """Profil geometrique des bassins du double-puits en ``(a, b)``.

    Generalise :func:`ict.bridge_testing.basin_geometry` (4 quantites) en
    ajoutant la **hauteur de barriere**. Renvoie, pour chaque minimum stable
    ``x*``, le tuple ``(x*, sigma, width, col, barrier)`` ou :

    * ``sigma``   = courbure ``V''(x*) = 4 b`` (raideur locale) ;
    * ``col``     = equilibre instable le plus proche (``x = 0`` ici) ;
    * ``width``   = ``|x* - col| = sqrt(b / (2 a))`` (demi-largeur vers le col) ;
    * ``barrier`` = ``V(col) - V(x*) = b^2 / (4 a)`` (hauteur du col).

    Renvoie ``[]`` si le double-puits n'est pas defini (``a <= 0`` ou ``b <= 0``).
    """
    eqs = double_well_equilibria(a, b)
    stables = [x for x, st in eqs if st]
    unstables = [x for x, st in eqs if not st]
    if not stables or not unstables:
        return []
    a_f = float(a)
    b_f = float(b)
    barrier = float(b_f ** 2 / (4.0 * a_f))
    out: List[Tuple[float, float, float, float, float]] = []
    for xstar in stables:
        col = min(unstables, key=lambda c: abs(c - xstar))
        sigma = 4.0 * b_f                       # V''(x*) = 4b
        width = float(abs(xstar - col))          # sqrt(b/(2a))
        out.append((float(xstar), float(sigma), width, float(col), barrier))
    return out


def realize_decoupled(sigma: float, width: float) -> Tuple[float, float]:
    """Donne les parametres ``(a, b)`` du double-puits realisant le couple
    cible ``(sigma, width)``. ``b = sigma / 4`` puis ``a = b / (2 width^2)``.

    La barriere resultante vaut ``sigma * width^2 / 8`` (co-varie avec le
    produit des deux cadrans -> devra etre controllee au verdict).
    """
    if sigma <= 0.0 or width <= 0.0:
        raise ValueError(f"sigma et width doivent etre > 0 (recu {sigma}, {width})")
    b = float(sigma) / 4.0
    a = b / (2.0 * float(width) ** 2)
    return a, b


# --------------------------------------------------------------------------- #
#  Recuperation NON tautologique (relaxation a convergence)                     #
# --------------------------------------------------------------------------- #


def recover_fraction(xstar: float, col: float, a: float, b: float,
                     delta_grid: np.ndarray, dt: float = 0.01,
                     full_steps: int = 4000, eps: float = 0.05) -> float:
    """Fraction d'un balayage de perturbations (vers le col) dont la relaxation
    **convergente** revient dans le bassin de ``x*`` (mesure deterministe,
    geometric). Mode **diagnostique** seulement : a convergence, la recuperation
    est purement geometrique (franchissement du col), la barriere n'a aucun
    effet -> le test de la barriere comme covariable n'est PAS exerce. Utilisez
    :func:`recover_fraction_stochastic` pour le verdict non trivial.
    """
    direction = 1.0 if col > xstar else -1.0
    n_back = 0
    for d in delta_grid:
        x = relax_double_well(xstar + direction * float(d), a, b,
                              dt=dt, steps=full_steps)
        if abs(x - xstar) < eps:
            n_back += 1
    return float(n_back) / float(delta_grid.size)


def recover_fraction_stochastic(xstar: float, a: float, b: float,
                                rng: np.random.Generator,
                                noise: float = 0.35,
                                n_trials: int = 60,
                                T: int = 3000,
                                dt: float = 0.02,
                                perturb_frac: float = 0.75) -> float:
    r"""Recuperation **stochastique** (Langevin) -- la mesure NON triviale.

    Chaque essai demarre en ``xstar * perturb_frac`` (perturbation relative,
    comparable d'un bassin a l'autre) puis evolue sous la dynamique
    overdamped bruitee ``dx = -V'(x) dt + sqrt(2 D dt) xi`` ou ``D = noise``.
    La **fraction d'essais** terminant dans le bassin de depart (``x > 0`` pour
    le minimum droit) apres ``T`` pas est la recuperation.

    Sous bruit, les TROIS quantites geometriques ont un effet mesurable :

    * **barriere** : proba d'escape d'Arrhenius ``~ exp(-barrier / D)`` ->
      barriere grande => recuperation plus haute ;
    * **courbure sigma** : taux de rappel lineaire vers ``x*`` (``exp(-sigma t)``)
      qui compete avec le bruit -> sigma grand => rappel plus rapide ;
    * **largeur** : geometrie (marge avant le col).

    C'est ce qui rend la correlation partielle a 2 covariables (largeur ET
    barriere) **decisive** : si ``sigma`` garde un pouvoir predictif propre
    apres controle des deux, le Pont #1 etait un artefact de couplage ;
    sinon, c'est un vrai negatif general. Prototype : ICT-8 section 8
    ``recov_dw`` (commit ``71ee7cf2b``), eleve ici au rang de module.

    Le bruit (``D``) est un parametre **physique**, pas un workaround : sans
    bruit la recuperation deterministe est degeneree (purement geometrique,
    constante apres mise a l'echelle), ce qui rendrait le test trivial et le
    verdict non falsifiable -- l'inverse du mandat SOTA (#3801 Prong B).
    """
    x0 = float(xstar) * float(perturb_frac)
    sdt = float(np.sqrt(2.0 * float(noise) * float(dt)))
    n_back = 0
    for _ in range(int(n_trials)):
        x = x0
        for _ in range(int(T)):
            x = x + float(double_well_force(x, a, b)) * float(dt) + sdt * rng.standard_normal()
        if x > 0.0:                       # bassin droit (xstar > 0)
            n_back += 1
    return float(n_back) / float(n_trials)


# --------------------------------------------------------------------------- #
#  Statistique : correlation partielle a N covariables (FWL, numpy)             #
# --------------------------------------------------------------------------- #


def _rank(xs: np.ndarray) -> np.ndarray:
    """Rangs **moyennes** (ex-aequo tolerants), comme ``scipy.stats.rankdata``.

    Crucial : ``np.argsort(np.argsort(xs))`` rend une rampe ``[0,1,...]`` sur un
    tableau constant (ordre arbitraire du tri stable), ce qui fabrique de fausses
    correlations. Les rangs moyennes rendent un vecteur constant -> constant
    (variance nulle -> ``_pearson`` garde a 0)."""
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
        avg = 0.5 * (i + j) + 1.0          # rangs 1-indexes, moyenne du bloc
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
    """Residus de la regression de ``y`` sur les ``covariates`` (+ intercept),
    methode des moindres carres (``np.linalg.lstsq``). Numpy-only (FWL)."""
    n = y.size
    Z = np.column_stack([np.ones(n), covariates])
    coef, *_ = np.linalg.lstsq(Z, y, rcond=None)
    return y - Z @ coef


def partial_spearman(x: np.ndarray, y: np.ndarray,
                     covariates: Sequence[np.ndarray]) -> float:
    """Correlation partielle de Spearman de ``x`` avec ``y`` en controlant les
    ``covariates`` (nombre quelconque), methode des residus de Frisch-Waugh-
    Lovell sur les **rangs**. Generalise ``bridge_testing._partial_spearman``
    (1 covariable, forme analytique) a ``N`` covariables.

    Renvoie 0.0 si moins de 2 points ou variance nulle. Pour 0 covariable,
    rend la correlation de Spearman simple (``_pearman`` des rangs).
    """
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    if x.size < 2:
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
#  Verdict Pont #1-bis : sigma | (width, barrier) -> recuperabilite             #
# --------------------------------------------------------------------------- #


def _gather_family(sigma_grid: np.ndarray, width_grid: np.ndarray,
                   noise: float, n_trials: int, T: int, dt: float,
                   perturb_frac: float, seed: int) -> Dict[str, np.ndarray]:
    """Echantillonne la famille decouplee et mesure ``sigma, width, barrier,
    recovery`` (stochastique) pour chaque minimum stable droit de chaque couple
    ``(sigma, width)``. On ne garde que le minimum droit (``x* > 0``) : la
    recuperation stochastique est definie relativement au bassin de depart, et
    les deux minima symetriques sont statistiquement interchangeables."""
    rng = np.random.default_rng(seed)
    sigmas: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    recoveries: List[float] = []
    for sg in sigma_grid:
        for wd in width_grid:
            a, b = realize_decoupled(float(sg), float(wd))
            for xstar, sigma, width, col, barrier in basin_profile(a, b):
                if xstar <= 0.0:
                    continue                  # minimum symetrique gauche: skip
                frac = recover_fraction_stochastic(
                    xstar, a, b, rng,
                    noise=noise, n_trials=n_trials, T=T, dt=dt,
                    perturb_frac=perturb_frac)
                sigmas.append(sigma)
                widths.append(width)
                barriers.append(barrier)
                recoveries.append(frac)
    return {
        "sigma": np.asarray(sigmas, dtype=float),
        "width": np.asarray(widths, dtype=float),
        "barrier": np.asarray(barriers, dtype=float),
        "recovery": np.asarray(recoveries, dtype=float),
    }


def pont1bis_verdict(
    sigma_grid: np.ndarray = None,
    width_grid: np.ndarray = None,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Pont #1-bis : verdict ternaire sur la famille decouplee (#9531).

    Rejoue le protocole du Pont #1 (:func:`ict.bridge_testing.bridge_stability_to_recoverability`)
    sur une famille de double-puits ou ``sigma`` (courbure) et la largeur de
    bassin varient **independamment par construction``. Le verdict decisif est
    la **correlation partielle de ``sigma`` avec ``recovery`` en controlant la
    largeur ET la barriere** (2 covariables, FWL) -- la barriere ``= sigma *
    width^2 / 8`` co-varie avec le produit des cadrans et doit etre purgee pour
    que le test de pouvoir predictif propre de ``sigma`` soit honnete.

    Verdict ternaire (jamais "promising") :

    * ``CONFIRMED-NEGATIVE`` : ``partial`` ~ 0 (``|partial| < 0.2``) et non
      significatif vs null par brouillage -> ``sigma`` n'a aucun pouvoir
      predictif propre dans la famille ; le Pont #1 est un vrai negatif
      general.
    * ``SUBSTRATE-ARTIFACT`` : ``partial > 0.2`` et au-dela du null p95 ->
      ``sigma`` regagne un pouvoir predictif propre ; le verdict fronce etait
      un artefact de couplage.
    * ``INCONCLUSIVE`` : ``partial < -0.2`` (effet inverse marque) ou signal
      incoherent -> documente honnetement, ni confirme ni falsifie.

    Renvoie un dict avec les correlations de Spearman brutes, le diagnostic de
    decouplage ``rho_sigma_width``, la partielle a 2 covariables, son null p95
    et le verdict.
    """
    rng = np.random.default_rng(seed)
    if sigma_grid is None:
        # courbures cible : b in (0.5, 4) -> sigma = 4b in (2, 16)
        sigma_grid = np.array([2.0, 3.0, 4.0, 6.0, 9.0, 13.0])
    if width_grid is None:
        # demi-largeurs cible : sqrt(b/(2a)) -- on balaye un ordre de grandeur
        width_grid = np.array([0.4, 0.6, 0.9, 1.3, 1.9])

    fam = _gather_family(sigma_grid, width_grid, noise, n_trials, T, dt,
                         perturb_frac, seed)
    sig, wid, bar, rec = fam["sigma"], fam["width"], fam["barrier"], fam["recovery"]

    rho_sigma_recovery = _pearson(_rank(sig), _rank(rec))
    rho_width_recovery = _pearson(_rank(wid), _rank(rec))
    rho_barrier_recovery = _pearson(_rank(bar), _rank(rec))
    rho_sigma_width = _pearson(_rank(sig), _rank(wid))     # diagnostic decouplage
    rho_sigma_barrier = _pearson(_rank(sig), _rank(bar))    # fuite de barriere

    # Tests decideurs : partielle a 1 covariable (comme Pont #1, pour comparaison)
    # puis a 2 covariables (largeur ET barriere, la rigueur #9531).
    partial_1cov = partial_spearman(sig, rec, [wid])
    partial_2cov = partial_spearman(sig, rec, [wid, bar])

    # null du test a 2 covariables : brouiller sigma, recompute la partielle.
    null_partial = np.array([
        partial_spearman(rng.permutation(sig), rec, [wid, bar])
        for _ in range(int(n_shuffle))
    ])
    p95_partial_null = float(np.percentile(np.abs(null_partial), 95))

    if partial_2cov > p95_partial_null and partial_2cov > 0.2:
        verdict = "SUBSTRATE-ARTIFACT"
    elif partial_2cov < -0.2:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "CONFIRMED-NEGATIVE"

    return {
        "n_samples": int(sig.size),
        "rho_sigma_recovery": float(rho_sigma_recovery),
        "rho_width_recovery": float(rho_width_recovery),
        "rho_barrier_recovery": float(rho_barrier_recovery),
        "rho_sigma_width": float(rho_sigma_width),
        "rho_sigma_barrier": float(rho_sigma_barrier),
        "partial_rho_given_width": float(partial_1cov),
        "partial_rho_given_width_barrier": float(partial_2cov),
        "partial_2cov_null_p95": p95_partial_null,
        "decoupling_ok": bool(abs(rho_sigma_width) < 0.2),
        "verdict": verdict,
    }


def recoupled_null(
    b_grid: np.ndarray = None,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Controle nul re-couple : sous-famille ou ``sigma`` et ``width`` sont
    **re-couples par construction`` (``a`` fixe, ``b`` varie -> les deux derivent
    ensemble). Doit reproduire le motif du Pont #1 sur la fronce : couplage
    eleve (``rho_sigma_width`` grand) et partielle a 1 covariable ~ 0.

    Si ce controle ne reproduit PAS le motif fronce, le protocole lui-meme est
    suspect (le decouplage de la famille principale pourrait etre un artefact
    de mesure). C'est la discipline du null model exigee par #9531.
    """
    rng = np.random.default_rng(seed)
    if b_grid is None:
        b_grid = np.array([0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5])
    a_fixed = 1.0  # a fixe : sigma=4b et width=sqrt(b/2) derivent ensemble

    sigmas: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    recoveries: List[float] = []
    for b in b_grid:
        a = a_fixed
        for xstar, sigma, width, col, barrier in basin_profile(a, float(b)):
            if xstar <= 0.0:
                continue
            frac = recover_fraction_stochastic(
                xstar, a, float(b), rng,
                noise=noise, n_trials=n_trials, T=T, dt=dt,
                perturb_frac=perturb_frac)
            sigmas.append(sigma)
            widths.append(width)
            barriers.append(barrier)
            recoveries.append(frac)

    sig = np.asarray(sigmas, dtype=float)
    wid = np.asarray(widths, dtype=float)
    bar = np.asarray(barriers, dtype=float)
    rec = np.asarray(recoveries, dtype=float)

    rho_sigma_width = _pearson(_rank(sig), _rank(wid))
    partial_1cov = partial_spearman(sig, rec, [wid])
    null_partial = np.array([
        partial_spearman(rng.permutation(sig), rec, [wid])
        for _ in range(int(n_shuffle))
    ])
    p95_partial_null = float(np.percentile(np.abs(null_partial), 95))

    return {
        "n_samples": int(sig.size),
        "rho_sigma_width": float(rho_sigma_width),
        "rho_width_recovery": float(_pearson(_rank(wid), _rank(rec))),
        "partial_rho_given_width": float(partial_1cov),
        "partial_null_p95": p95_partial_null,
        # le null re-couple doit reproduire la fronce : couplage grand ET
        # partielle ~ 0 (sigma n'ajoute rien par-dessus width).
        "reproduces_fronce_pattern": bool(
            rho_sigma_width > 0.6 and abs(partial_1cov) < 0.3
        ),
    }
