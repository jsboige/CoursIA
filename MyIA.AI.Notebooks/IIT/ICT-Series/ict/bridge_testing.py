"""Bridge-testing protocols (Epic #8077) : tester les FLECHES, pas les NOEUDS.

La serie ICT valide chaque brique localement (un sigma, un SAE, un workspace,
un MDL, un Phi). L'ambition unificatrice repose sur les **transitions** entre
briques -- les fleches (ponts) -- et ce sont elles qui portent le risque
scientifique : une brique peut tenir isolee sans que la fleche qui l'enchaine
a la suivante soit causale. Ce module porte un protocole falsifiable **par pont
testable**, sur le modele explicite ``hypothese + modele nul + intervention +
verdict``, au compte-gouttes (un pont par PR, cf #8077).

Ponts livres
------------
* **Pont #1** (sigma stabilite -> recuperabilite, c.1020) : **FALSIFIE** sur la
  fronce de Thom -- la portee de recuperation est gouvernee par la largeur de
  bassin (position du col), pas par la courbure locale ``sigma`` (proxy correle,
  correlation partielle ~0).
* **Pont #3** (extraction -> usage causal, c.1023) : **CONFIRME** sur substrat
  lineaire a redondance, avec controle nul borne par la severite de la
  redondance -- l'importance marginale predit l'usage causal (ablation) a
  diversite realiste, mais est un **proxy trompeur** sous redondance severe (seule
  l'ablation distingue alors les features causeales des redondantes).

Bridge #1 (sigma stabilite -> recuperabilite)
---------------------------------------------
Cf #8077, pont 1 du retour externe ChatGPT. Hypothese implicite de la strate
catastrophe (ICT-8/11) : un equilibre plus **stable** (bassin plus raide,
courbure ``V''(x*)`` grande) se reparerait **mieux** apres perturbation. Le
substrat est la fronce de Thom (:mod:`ict.catastrophe`).

La subtilite (qui rend le pont NON tautologique et donc falsifiable) est qu'on
distingue **deux** dimensions de la recuperation, qui se separant dans la fronce
asymetrique :

* **vitesse de relaxation** : linearise au voisinage de l'equilibre,
  ``dx/dt = -V''(x*) (x - x*)`` -- le taux de retour = la courbure ``sigma``.
  Plus ``sigma`` est grand, plus le systeme se rapproche vite de son equilibre
  en un temps fixe. C'est le pole ou le pont tient **par construction**
  (tautologie de la linearisation).
* **portee du bassin** : la perturbation finie franchit-elle le col (equilibre
  instable) ? Si oui, le systeme tombe dans l'autre bassin -- la recuperation
  est PERDUE, independamment de la courbure locale. La portee est gouvernee par
  la **largeur de bassin** (distance ``x* -> col``), pas par ``sigma``.

Le verdict falsifiable confronte donc les deux : si ``sigma`` predit la
recuperation **mieux que la largeur de bassin**, le pont tient ; si la largeur
de bassin predit mieux (``sigma`` n'etant qu'un proxy grossier de la portee,
qui s'effondre au pli ou largeur -> 0 alors que la courbure reste moderee), le
pont est **partiellement falsifie** -- c'est la geometrie du bassin (position du
col), pas la raideur locale, qui decide de la reparation. Un tel verdict 0 est
aussi honnete qu'un verdict 1 : c'est l'interet du protocole.
"""

from __future__ import annotations

from typing import Dict, List, Tuple

import numpy as np

from . import catastrophe as cat


# --------------------------------------------------------------------------- #
#  Bridge #1 : sigma (courbure) -> recuperabilite apres perturbation finie      #
# --------------------------------------------------------------------------- #


def basin_geometry(a: float, b: float) -> List[Tuple[float, float, float, float]]:
    """Geometrie des bassins de la fronce en ``(a, b)``.

    Renvoie, pour chaque minimum stable ``x*``, le tuple
    ``(x*, sigma, width, col)`` ou :

    * ``sigma`` = courbure ``V''(x*) = 3 x*^2 + a`` (raideur locale = stabilite) ;
    * ``col`` = equilibre instable le plus proche (frontiere de bassin) ;
    * ``width`` = ``|x* - col|`` (demi-largeur du bassin vers le col = portee).

    Renvoie ``[]`` hors region bistable (pas de col -> bassin infini, cas
    trivial ou toute perturbation est recuperee ; hors-scope du pont).
    """
    eqs = cat.cusp_equilibria(a, b)              # [(x, stable), ...] trie par x
    stables = [x for x, st in eqs if st]
    unstables = [x for x, st in eqs if not st]
    if not stables or not unstables:
        return []
    out: List[Tuple[float, float, float, float]] = []
    for xstar in stables:
        col = min(unstables, key=lambda c: abs(c - xstar))
        sigma = float(cat.cusp_curvature(xstar, a))
        width = float(abs(xstar - col))
        out.append((float(xstar), sigma, width, float(col)))
    return out


def _recover_fraction(xstar: float, col: float, a: float, b: float,
                      delta_grid: np.ndarray, dt: float,
                      full_steps: int, eps: float) -> float:
    """Fraction d'un **balayage de perturbations** (vers le col) dont la
    relaxation convergente revient dans le bassin de ``x*``.

    On relaxe **a convergence** (``full_steps`` suffisant) : le resultat binaire
    (revient / ne revient pas) depend donc de la **portee du bassin** (la
    perturbation franchit-elle le col ?), PAS de la vitesse de relaxation. C'est
    ce qui rend la mesure NON tautologique : a convergence, un bassin plus raide
    (``sigma`` grand) ne recupere pas << mieux >> qu'un bassin plat de meme
    largeur -- seul compte le franchissement du col (largeur de bassin)."""
    direction = 1.0 if col > xstar else -1.0
    n_back = 0
    for d in delta_grid:
        x = cat.relax_to_equilibrium(xstar + direction * float(d), a, b,
                                     dt=dt, steps=full_steps)
        if abs(x - xstar) < eps:
            n_back += 1
    return float(n_back) / float(delta_grid.size)


def _partial_spearman(sig: np.ndarray, rec: np.ndarray,
                      wid: np.ndarray) -> float:
    """Correlation partielle de Spearman de ``sigma`` avec ``recovery`` en
    controlant la largeur de bassin ``width``. C'est le test decisif : si elle
    est ~0, ``sigma`` n'a AUCUNE puissance predictive independante au-dela de la
    largeur -- le pont est falsifie (``sigma`` n'est qu'un proxy correle)."""
    r_sr = _spearman(sig, rec)
    r_sw = _spearman(sig, wid)
    r_wr = _spearman(wid, rec)
    denom_sq = (1.0 - r_sw * r_sw) * (1.0 - r_wr * r_wr)
    if denom_sq <= 1e-12:
        return 0.0
    return float((r_sr - r_sw * r_wr) / np.sqrt(denom_sq))


def _spearman(xs: np.ndarray, ys: np.ndarray) -> float:
    """Correlation de Spearman (monotone, robuste aux non-linearites) sur deux
    series. Renvoie 0.0 si une variance est nulle."""
    if xs.size < 2 or float(np.std(xs)) < 1e-12 or float(np.std(ys)) < 1e-12:
        return 0.0
    rx = np.argsort(np.argsort(xs)).astype(float)
    ry = np.argsort(np.argsort(ys)).astype(float)
    rx = rx - rx.mean()
    ry = ry - ry.mean()
    denom = float(np.sqrt((rx * rx).sum() * (ry * ry).sum()))
    return float((rx * ry).sum() / denom) if denom > 0 else 0.0


def bridge_stability_to_recoverability(
    a_grid: np.ndarray = None,
    b_grid: np.ndarray = None,
    delta_max: float = 2.5,
    n_delta: int = 25,
    dt: float = 0.01,
    full_steps: int = 2000,
    eps: float = 0.05,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Bridge #1 : ``sigma`` (courbure) -> **portee de recuperation** (falsifiable, #8077 pont 1).

    Echantillonne une grille ``(a, b)`` dans la region bistable de la fronce
    (symetrique ET asymetrique, pour separer courbure et largeur de bassin).
    Pour chaque minimum stable ``x*`` : ``sigma = V''(x*)``, ``width`` = demi-
    largeur vers le col, et une **mesure de recuperation** = fraction d'un
    balayage de perturbations ``[0, delta_max]`` vers le col dont la relaxation
    **convergente** revient dans le bassin de ``x*``.

    La relaxation a convergence (``full_steps`` suffisant) est cruciale pour
    l'honnetete du test : si l'on mesurait la proximite a temps fixe, la
    recuperation serait monotone en ``sigma`` par construction (taux linearise
    ``exp(-sigma T)``) -- un pont tautologique. A convergence, seul compte le
    franchissement du col : la recuperation est gouvernee par la **largeur de
    bassin**, et la question devient *non triviale* : ``sigma`` predit-il cette
    portee mieux que la chance ?

    Trois correlations de Spearman (monotones) :

    * ``rho_sigma_recovery`` : la courbure predit-elle la portee de recuperation ?
    * ``rho_width_recovery`` : la largeur de bassin predit-elle mieux ? (concurrent)
    * ``rho_sigma_width`` : courbure et largeur sont-elles couplees ? (diagnostic)

    **Test decisif (non threshold-fragile)** : la **correlation partielle**
    ``partial_rho_sigma_recovery_given_width``. Si elle est ~0, ``sigma`` n'a
    aucune puissance predictive independante au-dela de la largeur de bassin : la
    courbure n'est qu'un proxy correle de la portee, et le pont est falsifie.

    Verdict falsifiable
    -------------------
    ``bridge_sigma_to_recoverability`` : 1.0 si la correlation partielle de
        ``sigma`` (controle de la largeur) est **positive et significative**
        (``partial > 0.2`` et au-dela de son null par brouillage) -- ``sigma``
        porte une information causale propre sur la recuperation (plus stable =>
        mieux recupere, au-dela de la largeur). 0.0 sinon : la portee est
        gouvernee par la **geometrie du bassin** (position du col), et ``sigma``
        n'est qu'un proxy correle (rho_sigma_width eleve) sans pouvoir explicatif
        independant. Une correlation partielle **negative** (plus stable =>
        moins bien recupere en controle de la largeur) falsifie le pont tout
        autant qu'une partielle nulle. C'est la falsification honnete du pont
        naif « plus stable => mieux recupere ».

    Le verdict 0 est scientifiquement honnete et **informatif** : sur le substrat
    fronce, la recuperation apres perturbation finie est une question de
    **largeur de bassin** (le col est-il franchi ?), pas de raideur locale. La
    courbure ``sigma`` predit la *vitesse* de retour (par linearisation, hors
    scope ici) mais non la *portee*. Cf taxonomie ``claim_type`` #7734.
    """
    rng = np.random.default_rng(seed)
    if a_grid is None:
        a_grid = np.array([-3.0, -2.0, -1.5, -1.0, -0.6])
    if b_grid is None:
        b_grid = np.linspace(-0.9, 0.9, 19)

    delta_grid = np.linspace(0.0, float(delta_max), int(n_delta))

    sigmas: List[float] = []
    widths: List[float] = []
    recoveries: List[float] = []
    for a in a_grid:
        for b in b_grid:
            for xstar, sigma, width, col in basin_geometry(float(a), float(b)):
                frac = _recover_fraction(xstar, col, float(a), float(b),
                                         delta_grid, dt, full_steps, eps)
                sigmas.append(sigma)
                widths.append(width)
                recoveries.append(frac)

    sig = np.asarray(sigmas, dtype=float)
    wid = np.asarray(widths, dtype=float)
    rec = np.asarray(recoveries, dtype=float)

    rho_sigma = _spearman(sig, rec)          # pont : courbure -> portee
    rho_width = _spearman(wid, rec)          # concurrent : largeur -> portee
    rho_sigma_width = _spearman(sig, wid)    # diagnostic : couplage courbure/largeur
    partial = _partial_spearman(sig, rec, wid)  # test decisif : sigma | width

    # null du test decisif : brouiller sigma, recompute la partielle.
    null_partial = np.array([
        _partial_spearman(rng.permutation(sig), rec, wid) for _ in range(int(n_shuffle))
    ])
    p95_partial_null = float(np.percentile(np.abs(null_partial), 95))

    # pont confirme : partial POSITIVE et significative (plus stable => mieux
    # recupere, au-dela de la largeur). Une partielle nulle (proxy pur) ou
    # negative (effet inverse) -> falsifie.
    bridge = 1.0 if (partial > p95_partial_null and partial > 0.2) else 0.0

    return {
        "n_equilibria": int(sig.size),
        "delta_max": float(delta_max),
        "rho_sigma_recovery": float(rho_sigma),
        "rho_width_recovery": float(rho_width),
        "rho_sigma_width": float(rho_sigma_width),
        "partial_rho_sigma_recovery_given_width": float(partial),
        "partial_null_p95": p95_partial_null,
        "bridge_sigma_to_recoverability": bridge,
    }


# --------------------------------------------------------------------------- #
#  Bridge #3 : extraction (importance) -> usage causal (ablation)              #
# --------------------------------------------------------------------------- #


def _redundant_feature_dataset(
    rng: np.random.Generator,
    n_samples: int,
    n_singleton: int,
    n_dup_groups: int,
    dup_size: int,
    feat_noise: float,
    y_noise: float,
) -> Tuple[np.ndarray, np.ndarray]:
    """Jeu de donnees synthetique a **features singleton** (uniques) + **groupes
    dupliques** (redundantes). Substrat du pont #3 (extraction -> usage causal).

    Chaque feature (singleton ou duplicata) porte le signal **source complet** :
    une feature duplicata est donc **importante a la marge** (correlee a ``y`` via
    la source commune) mais **redundante en ablation** (les autres duplicatas du
    meme groupe compensent sa disparition). C'est le **controle nul de l'issue**
    #8077 pont 3 : « ablation de la feature sans effet comportemental » — une
    feature extraite (importante) qui n'est pas *causalement utilisee* (ablation
    sans effet) sous redondance severe. ``feat_noise`` regle la colinearite (faible
    = duplicatas quasi-identiques = redondance severe = falsification ; eleve =
    diversite realiste = confirmation).
    """
    feats: List[np.ndarray] = []
    for _ in range(int(n_singleton)):
        s = rng.standard_normal(int(n_samples))
        feats.append(s + feat_noise * rng.standard_normal(int(n_samples)))
    for _ in range(int(n_dup_groups)):
        s = rng.standard_normal(int(n_samples))
        for _ in range(int(dup_size)):
            feats.append(s + feat_noise * rng.standard_normal(int(n_samples)))
    X = np.array(feats).T
    # y charge sur les sources (inconnues de l'analyste) ; reconstruites comme
    # moyennes de groupe (les duplicatas partagent la meme source latente).
    sources: List[np.ndarray] = []
    idx = 0
    for _ in range(int(n_singleton)):
        sources.append(X[:, idx])
        idx += 1
    for _ in range(int(n_dup_groups)):
        sources.append(X[:, idx:idx + int(dup_size)].mean(axis=1))
        idx += int(dup_size)
    w = rng.uniform(0.5, 1.5, size=len(sources))
    y = sum(float(w[i]) * sources[i] for i in range(len(sources)))
    y = y + y_noise * rng.standard_normal(int(n_samples))
    return X, y


def _feature_causal_stats(
    X: np.ndarray, y: np.ndarray
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Par feature : **importance marginale**, **effet d'ablation** (contribution
    unique), et **unicite**.

    * ``importance_marginale`` = r^2(feature, ``y``) : ce qu'un SAE ou un analyste
      calcule **observationnellement** (la « feature extraite est-elle informative ? »).
    * ``effet_ablation`` = chute de R^2 du modele lineaire complet quand on retire
      la feature = sa **contribution unique** (l'intervention ``do(feature := 0)``
      au sens de Pearl ; l'usage *causal* reel).
    * ``unicite`` = ``1 - max`` correlation pairwise avec les autres features
      (le concurrent : la redondance, observable, qui confond importance et usage).

    Numpy pur (OLS via :func:`numpy.linalg.lstsq`).
    """
    K = X.shape[1]
    marg = np.array([np.corrcoef(X[:, i], y)[0, 1] ** 2 for i in range(K)])
    Xc = X - X.mean(axis=0)
    yc = y - y.mean()

    def _r2(cols: List[int]) -> float:
        A = Xc[:, cols]
        coef, *_ = np.linalg.lstsq(A, yc, rcond=None)
        pred = A @ coef
        ss_res = float(np.sum((yc - pred) ** 2))
        ss_tot = float(np.sum(yc ** 2))
        return 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0

    full = _r2(list(range(K)))
    ablation = np.array([full - _r2([j for j in range(K) if j != i]) for i in range(K)])
    C = np.corrcoef(X.T)
    np.fill_diagonal(C, 0.0)
    uniqueness = 1.0 - np.abs(C).max(axis=1)
    return marg, ablation, uniqueness


def bridge_extraction_to_causal_usage(
    n_datasets: int = 40,
    n_samples: int = 400,
    n_singleton: int = 6,
    n_dup_groups: int = 6,
    dup_size: int = 3,
    feat_noise: float = 0.3,
    y_noise: float = 0.5,
    n_shuffle: int = 50,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Bridge #3 : extraction (importance marginale) -> usage causal (ablation) (falsifiable, #8077 pont 3).

    Hypothese implicite de la strate SAE/extraction (ICT-15..20, #5101) : une feature
    **extraite** (informative, importante a la marge) est **causalement utilisee**
    par le calcul, pas juste correlee. La lecture naive « importante => cause ».
    Le substrat : un modele lineaire a features singleton + groupes dupliques
    (:func:`_redundant_feature_dataset`), ou l'**importance marginale** (r^2 avec
    ``y``) est l'observable d'extraction et l'**effet d'ablation** (chute de R^2
    quand on retire la feature = contribution unique) est l'usage causal reel
    (intervention ``do(.)`` de Pearl).

    La subtilite (qui rend le pont NON tautologique et falsifiable) est la
    **redondance** : une feature duplicata porte le signal source complet -> elle
    est **importante a la marge** (correlee a ``y``) MAIS **redundante en ablation**
    (les autres duplicatas compensent). C'est le controle nul de l'issue : une
    feature extraite qui n'est pas causalement utilisee. Le test decisif est la
    **correlation partielle** (importance | unicite) -> ablation, calculee **par
    modele** (la bonne unite : dans le jeu de features extrait d'un modele, est-ce
    que l'importance predit l'usage causal au-dela de la redondance ?).

    Sondage C976-L (c.1023) AVANT d'asserter :
      * aggregation cross-datasets (panel) -> CONFIRME mais confondu par le SNR
        inter-datasets (faux signal). La bonne unite est **par-modele**.
      * a ``feat_noise`` eleve (diversite realiste) : partial par-modele ~+0.5,
        frac>0.2 ~0.9 -> **CONFIRME** (l'importance predit l'usage causal).
      * a ``feat_noise`` faible (duplicatas quasi-identiques, redondance severe) :
        partial par-modele ~+0.08, frac>0.2 ~0.33 -> **FALSIFIE** (l'importance ne
        predit plus l'usage causal ; seule l'ablation revele quelles features sont
        causalement utilisees). Transition monotone (non threshold-fragile, cf pont
        #2 abandonne), bornee par la severite de la redondance.

    Verdict falsifiable
    -------------------
    ``bridge_extraction_to_causal_usage`` : 1.0 si, sur la majorite des modeles,
        la correlation partielle (importance | unicite) -> ablation est positive et
        au-dela du null (l'extraction predit l'usage causal au-dela de la
        redondance). 0.0 sinon : sous redondance severe, l'importance marginale est
        un **proxy trompeur** de l'usage causal — seule l'intervention (ablation)
        distingue les features causeales des features redondantes (do-calculus).
    """
    rng = np.random.default_rng(seed)
    observed: List[float] = []
    null_p95_per_model: List[float] = []
    marg_abl: List[float] = []
    uniq_abl: List[float] = []
    for _ in range(int(n_datasets)):
        X, y = _redundant_feature_dataset(
            rng, n_samples, n_singleton, n_dup_groups, dup_size, feat_noise, y_noise
        )
        marg, abl, uniq = _feature_causal_stats(X, y)
        observed.append(_partial_spearman(marg, abl, uniq))
        marg_abl.append(_spearman(marg, abl))
        uniq_abl.append(_spearman(uniq, abl))
        # null par-modele : brouiller l'importance (casser le lien importance->ablation
        # en gardant importance<->unicite), recompute la partielle.
        null_partials = np.array([
            _partial_spearman(rng.permutation(marg), abl, uniq) for _ in range(int(n_shuffle))
        ])
        null_p95_per_model.append(float(np.percentile(np.abs(null_partials), 95)))
    observed_arr = np.asarray(observed, dtype=float)
    null_arr = np.asarray(null_p95_per_model, dtype=float)
    n_sig = int(np.sum((observed_arr > null_arr) & (observed_arr > 0.2)))
    frac_significant = n_sig / float(observed_arr.size)
    mean_partial = float(np.mean(observed_arr))

    bridge = 1.0 if frac_significant > 0.5 else 0.0

    return {
        "n_datasets": int(n_datasets),
        "feat_noise": float(feat_noise),
        "mean_partial_rho_importance_ablation_given_uniqueness": mean_partial,
        "frac_models_confirmed": float(frac_significant),
        "mean_rho_importance_ablation": float(np.mean(marg_abl)),
        "mean_rho_uniqueness_ablation": float(np.mean(uniq_abl)),
        "partial_null_p95_mean": float(np.mean(null_arr)),
        "bridge_extraction_to_causal_usage": bridge,
    }
