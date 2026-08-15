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
* **Pont #4** (workspace -> diffusion fonctionnelle, c.1025) : **CONFIRME** sur
  substrat reseau a bus broadcast -- la disponibilite globale (broadcast)
  etend la porte fonctionnelle au-dela de la connectivite directe (elle fait
  atteindre des modules structurellement inaccessibles). Controle nul
  structural : un bus present mais ignore (``read_p=0``) est **fonctionnellement
  inerte** (frac atteint = 0 exact) -- c'est le null « broadcast present mais
  non exploite en aval » de #8077.
* **Pont #5** (MDL compression -> generalisation, c.1021/c.1024) :
  **CONFIRME-CONDITIONNEL** -- la compressibilite du train predit la
  generalisation held-out **sur source stationnaire** (rho ~ +0.9) et
  l'**anti-predit sous decalage de source** (rho ~ -0.8). La lecture
  MDL-as-generalization a donc un **domaine de validite** (source stationnaire),
  pas une valeur de verite ; en dehors de ce domaine, la fleche s'inverse. C'est
  le genre de fleche « vraie sous condition » de la taxonomie ``claim_type``
  (#7734) -- distincte d'un pont binaire confirme/falsifie.

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


# --------------------------------------------------------------------------- #
#  Bridge #4 : workspace (broadcast) -> diffusion fonctionnelle (portee)       #
# --------------------------------------------------------------------------- #


def _random_module_network(
    rng: np.random.Generator, n_modules: int, density: Tuple[float, float]
) -> np.ndarray:
    """Reseau de modules a connectivite directe aleatoire et **clairsemee**.

    Renvoie une matrice d'adjacence booleenne ``(n_modules, n_modules)`` ou
    ``adj[i, j]`` indique un lien direct ``i -> j``. La densite est tiree dans
    ``density`` (plage faible : connectivite directe **partielle**, laissant de
    la place pour que le broadcast etende la portee -- sondage c.1025 : densite
    trop elevee => connectivite directe saturee => regime degenere). Diagonale
    nulle (un module ne s'influence pas lui-meme)."""
    d = float(rng.uniform(*density))
    adj = rng.random((n_modules, n_modules)) < d
    np.fill_diagonal(adj, False)
    return adj


def _direct_reach_set(adj: np.ndarray, source: int) -> np.ndarray:
    """Ensemble des modules atteignables par **chemins directs uniquement**
    (fermeture transitive des aretes directes depuis ``source``). C'est la portee
    de base, sans le bus broadcast -- le concurrent structurel du pont."""
    n = adj.shape[0]
    reached = np.zeros(n, dtype=bool)
    reached[source] = True
    for _ in range(n):
        newly = (adj.T @ reached.astype(int)) > 0
        if np.array_equal(reached, reached | newly):
            break
        reached |= newly
    return reached


def _broadcast_reach_set(
    adj: np.ndarray, read_p: float, pub_p: float, source: int,
    rng: np.random.Generator, max_iter: int = 60,
) -> np.ndarray:
    """Portee avec un **bus broadcast global** (substrat du pont #4).

    A chaque iteration, un module ``j`` devient actif si (a) un predecesseur
    direct actif le pointe, OU (b) le **bus** porte le signal ET ``j`` le lit
    (probabilite ``read_p``). Un module nouvellement actif **publie** le signal
    sur le bus avec probabilite ``pub_p`` (ignition) -- une fois le bus allume,
    il le reste (memoire globale du workspace). ``read_p`` = **usage** du bus
    par les modules en aval ; ``pub_p`` = **ignition** (le signal entre-t-il sur
    le bus ?). Les deux sont necessaires : bus allume sans lecteurs = inert ;
    lecteurs sans ignition = bus vide.
    """
    n = adj.shape[0]
    active = np.zeros(n, dtype=bool)
    active[source] = True
    bus_has_signal = False
    for it in range(max_iter):
        new_active = active.copy()
        for j in range(n):
            if active[j]:
                continue
            direct_in = bool(np.any(active & adj[:, j]))
            bus_in = bus_has_signal and (rng.random() < read_p)
            if direct_in or bus_in:
                new_active[j] = True
        if not bus_has_signal and np.any(new_active & ~active):
            for m in np.where(new_active & ~active)[0]:
                if rng.random() < pub_p:
                    bus_has_signal = True
                    break
        if np.array_equal(new_active, active) and it > 0:
            break
        active = new_active
    return active


def bridge_workspace_to_diffusion(
    n_networks: int = 120,
    n_modules: int = 40,
    density: Tuple[float, float] = (0.02, 0.06),
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Bridge #4 : workspace (broadcast global) -> diffusion fonctionnelle (falsifiable, #8077 pont 4).

    Hypothese naive de la strate Global Workspace (ICT-24, #4588) : la
    **disponibilite globale** d'une information (le bus broadcast du workspace)
    **change ce que d'autres mecanismes peuvent faire** -- elle etend la portee
    fonctionnelle au-dela de la connectivite directe. Le substrat : un reseau de
    modules (:func:`_random_module_network`) ou un signal entre au module source
    et peut se propager par les liens directs (portee locale,
    :func:`_direct_reach_set`) OU par le bus broadcast
    (:func:`_broadcast_reach_set`).

    La subtilite (qui rend le pont NON tautologique et falsifiable) est qu'on
    isole ce que le broadcast apporte **de neuf** : la fraction des modules
    **structurellement inaccessibles** par chemins directs (hors portee locale)
    que le broadcast **fait atteindre**. Si le broadcast n'apportait rien, cette
    fraction serait nulle (la portee = portee directe). La mesure discrimine
    donc la contribution **unique** du bus au-dela de la connectivite.

    Le **controle nul de l'issue** (« broadcast present mais non exploite en
    aval ») : un bus structurellement present mais que les modules **ignorent**
    (``read_p = 0``) est **fonctionnellement inerte** -- la fraction des
    inaccessibles atteints tombe a **0 exact**. Le bus existe mais ne change rien
    (c'est le null « dark broadcast » de #8077).

    Test decisif : la **correlation partielle** (capacite_broadcast | n_inaccessibles)
    -> fraction_inaccessibles_atteints, ou la capacite = ``read_p * pub_p``
    (usage x ignition, les deux requis). ``n_inaccessibles`` est le concurrent
    **reel** (le denominateur structurel : plus d'inaccessibles => plus d'opportunite
    mais aussi plus dur a tous atteindre), et la partielle isole la contribution du
    broadcast au-dela (sondage c.1025 : partielle +0.45 > brute +0.35, le controle
    *affine* le signal, c.1024-L : concurrent reel, pas orthogonal).

    Sondage C976-L (c.1025) AVANT d'asserter :
      * graphes trop denses (K=30, dens 0.05-0.25) => connectivite directe saturee
        (portee directe ~0.93) => regime degenere, partial non significatif.
        Bon regime : graphes **clairsemes** (K=40, dens 0.02-0.06, portee directe
        ~0.34) => vraie place pour le broadcast.
      * formulation naive « increment = total - direct » est **confondue** par la
        portee directe (rho +0.60) => borderline (partial ~+0.18, seuil nul). La
        bonne mesure isole les **inaccessibles** atteints => partial +0.45 propre.

    Verdict falsifiable
    -------------------
    ``bridge_workspace_to_diffusion`` : 1.0 si la capacite du broadcast predit
        significativement la fraction des inaccessibles atteints au-dela du
        denominateur structurel (partial positive > null p95) **et** le controle
        nul structural (bus ignore) donne une fraction ~0 (bus inerte). 0.0 sinon.

    Robuste (c.1014-L) : le verdict tient sur plusieurs graines (partial +0.41..+0.53
    sur seeds {0,1,2,3,7,42}).
    """
    rng = np.random.default_rng(seed)
    capacities: List[float] = []
    fracs: List[float] = []
    n_unreachable_list: List[int] = []
    for _ in range(int(n_networks)):
        adj = _random_module_network(rng, n_modules, density)
        read_p = float(rng.uniform(0.0, 1.0))
        pub_p = float(rng.uniform(0.0, 1.0))
        direct = _direct_reach_set(adj, source=0)
        n_unreachable = int((~direct).sum())
        if n_unreachable < 2:
            continue  # pas d'inaccessibles a mesurer (reseau quasi-sature)
        broadcast = _broadcast_reach_set(adj, read_p, pub_p, source=0, rng=rng)
        newly_reached = int((broadcast & ~direct).sum())
        capacities.append(read_p * pub_p)
        fracs.append(newly_reached / float(n_unreachable))
        n_unreachable_list.append(n_unreachable)
    cap = np.asarray(capacities, dtype=float)
    frac = np.asarray(fracs, dtype=float)
    n_un = np.asarray(n_unreachable_list, dtype=float)

    rho_cap_frac = _spearman(cap, frac)
    rho_nun_frac = _spearman(n_un, frac)
    partial = _partial_spearman(cap, frac, n_un)

    null_partial = np.array([
        _partial_spearman(rng.permutation(cap), frac, n_un) for _ in range(int(n_shuffle))
    ])
    p95_partial_null = float(np.percentile(np.abs(null_partial), 95))

    # controle nul structural : bus ignore (read_p=0) => inaccessibles atteints ~0
    null_frac = []
    for _ in range(30):
        adj = _random_module_network(rng, n_modules, density)
        direct = _direct_reach_set(adj, source=0)
        n_unreachable = int((~direct).sum())
        if n_unreachable < 2:
            continue
        dark = _broadcast_reach_set(adj, read_p=0.0, pub_p=1.0, source=0, rng=rng)
        null_frac.append(int((dark & ~direct).sum()) / float(n_unreachable))
    null_control_frac = float(np.mean(null_frac)) if null_frac else 0.0

    bridge = 1.0 if (partial > p95_partial_null and partial > 0.2
                     and null_control_frac < 0.05) else 0.0

    return {
        "n_networks": int(cap.size),
        "n_modules": int(n_modules),
        "mean_frac_unreachable_reached": float(np.mean(frac)),
        "null_control_frac_dark_bus": null_control_frac,
        "rho_capacity_frac": float(rho_cap_frac),
        "rho_n_unreachable_frac": float(rho_nun_frac),
        "partial_rho_capacity_frac_given_n_unreachable": float(partial),
        "partial_null_p95": p95_partial_null,
        "bridge_workspace_to_diffusion": bridge,
    }


# --------------------------------------------------------------------------- #
#  Bridge #5 : MDL (compression) -> generalisation (held-out)                  #
# --------------------------------------------------------------------------- #


def _markov_sequence(rng: np.random.Generator, n: int, n_states: int,
                     regularity: float, drift: float) -> List[int]:
    """Sequence markovienne stationnaire a structure reglable.

    ``regularity`` in [0,1] : probabilite de repeter l'etat precedent (1 = cycle
    quasi-deterministe = tres compressible ; 0 = iid = incompressible). ``drift``
    in [0,1] : probabilite, a **chaque pas**, de tirer un etat iid.

    .. warning::
       ``drift`` est un levier **stationnaire** : il est applique uniformement a
       chaque pas, a l'identique dans la moitie train et la moitie test. Il n'y a
       donc **aucun changement de source entre train et test** -- la source reste
       markovienne stationnaire a tous les niveaux de ``drift``. Sous ce regime,
       ``drift`` degrade la compression du train ET la generalisation du test
       *ensemble* (elles restent correlees) : c'est pourquoi le controle nul naif
       « drift stationnaire eleve » **ne falsifie pas** le pont (rho reste ~+0.7).
       Le **vrai** controle nul falsifiant exige une source **non-stationnaire**
       (decouplage train/test) -- cf :func:`_markov_sequence_two_regime`.
    """
    s = int(rng.integers(0, n_states))
    out = [s]
    for _ in range(n - 1):
        if rng.random() < drift:
            s = int(rng.integers(0, n_states))      # tirage iid stationnaire
        elif rng.random() < regularity:
            s = s                                     # persistance (compressible)
        else:
            s = int(rng.integers(0, n_states))       # hasard
        out.append(s)
    return out


def _markov_sequence_two_regime(rng: np.random.Generator, n_half: int,
                                n_states: int, reg_train: float, dr_train: float,
                                reg_test: float, dr_test: float) -> List[int]:
    """Source **non-stationnaire** : la 1ere moitie (train) et la 2eme (test) viennent
    de regimes markoviens **differents**. C'est le **controle nul falsifiant** du
    pont #5 : si le train est compressible (``reg_train`` eleve, ``dr_train``
    faible) mais le test vient d'une source decalee (``dr_test`` eleve), la
    compression du train ne predit plus la generalisation held-out -- elle
    **s'inverse** (rho ~ -0.8, robuste). C'est le null « compression misleads » de
    #8077, et il borne le domaine de validite du verdict (source stationnaire).

    Contrast avec :func:`_markov_sequence` (stationnaire), ou le ``drift`` uniforme
    fait que compression et generalisation se degradent **ensemble** (restent
    correlees, rho ~ +0.7 meme sous drift eleve) : le controle nul naif ne falsifie
    donc PAS le pont. Seul le decouplage train/test (cette fonction) produit le
    null falsifiant.
    """
    train = _markov_sequence(rng, n_half, n_states, reg_train, dr_train)
    test = _markov_sequence(rng, n_half, n_states, reg_test, dr_test)
    return train + test


def bridge_compression_to_generalization(
    n_trials: int = 60,
    n: int = 300,
    n_states: int = 4,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Bridge #5 : MDL (compression du train) -> generalisation held-out (falsifiable, #8077 pont 5).

    Hypothese naive (MDL-as-generalization, Rissanen) : un modele qui **compresse
    mieux** sa trajectoire d'entrainement (taux d'entropie faible) **generalise
    mieux** sur du held-out (residuel MDL faible = peu de surprise sur les
    transitions non vues). Le substrat : :mod:`ict.mdl` (``two_part_code`` ->
    ``residual_bits`` = erreur de generalisation) et ``entropy_rate_estimate``
    (compressibilite du train).

    Verdict : **CONFIRME-CONDITIONNEL** (domaine de validite, pas valeur de verite)
    -----------------------------------------------------------------------
    La compressibilite du train predit la generalisation held-out **sur source
    stationnaire** et l'**anti-predit sous decalage de source**. La fleche
    MDL-as-generalization a donc un **domaine de validite** (source stationnaire) ;
    en dehors, elle s'inverse. C'est le genre « vraie sous condition » de la
    taxonomie ``claim_type`` (#7734).

    Pour mesurer CE domaine (et non le cacher), la fonction echantillonne DEUX
    regimes et expose les deux correlations de Spearman :

    * **regime stationnaire** (:func:`_markov_sequence`, ``regularity`` et ``drift``
      uniformes sur toute la sequence) -> ``rho_compress_gen`` (~+0.9) : la source
      est stable, le train et le test viennent du meme regime, donc compresser le
      train predit la generalisation. C'est le pole CONFIRME.
    * **regime non-stationnaire** (:func:`_markov_sequence_two_regime`, train
      compressible + test decale) -> ``rho_compress_gen_nonstationary`` (~-0.8) :
      la source bascule entre train et test, donc un train tres compressible est
      couple a un test imprevisible -> la compression **anti-predit** la
      generalisation. C'est le pole FALSIFIE.

    Sur le **controle nul naif** (``drift`` stationnaire eleve)
    -------------------------------------------------------
    ``drift`` est un levier **stationnaire** (applique uniformement) : il est
    quasi-orthogonal a la fois au predicteur (compression) et a la sortie
    (generalisation), avec ``rho_compress_drift ~ -0.1``. La **correlation
    partielle** (compression | drift) est donc essentiellement egale a la
    correlation brute (~+0.92 vs ~+0.91) -- le controle ne deplace **rien** parce
    qu'il n'y avait **pas de concurrent** (arithmetique, pas une opinion). La
    partielle n'est PAS ici le test decisif d'un « pouvoir predictif independant
    au-dela du drift » : le verdict est porte par le **contraste stationnaire vs
    non-stationnaire** (les deux ``rho_*_gen``), qui est le vrai discriminateur.

    Verdict falsifiable
    -------------------
    ``bridge_compression_to_generalization`` : 1.0 si le **pattern conditionnel**
        tient -- ``rho_compress_gen > 0.7`` (predit sur source stationnaire) ET
        ``rho_compress_gen_nonstationary < -0.3`` (anti-predit sous decalage de
        source). 0.0 sinon. Ce n'est ni un confirme ni un falsifie naif : c'est un
        domaine de validite explicite (claim_type « vraie sous condition », #7734).

    Robuste (c.1014-L) : le verdict conditionnel tient sur plusieurs graines (le
    ``_markov_sequence`` est stochastique ET ``regularity``/``drift`` sont tires par
    essai, donc le seed traverse le calcul et les correlations varient -- mesure
    de robustesse reelle, contrairement au pont #1 deterministe).
    """
    from . import mdl as M

    rng = np.random.default_rng(seed)

    def _score(seq: List[int]) -> Tuple[float, float]:
        tp = M.two_part_code(seq, split=0.5)
        er = M.entropy_rate_estimate(seq[: int(0.5 * len(seq))], block=2)
        # 1/(1+x) : grand = bon (compressible / generalise bien). Inversions monotones.
        compress = 1.0 / (1.0 + float(er["entropy_rate"]))
        gen = 1.0 / (1.0 + float(tp["residual_bits"]))
        return compress, gen

    # --- regime stationnaire : regularity et drift tires, source stable -------
    comp_s, gen_s, drift_s = [], [], []
    for _ in range(int(n_trials)):
        reg = float(rng.uniform(0.0, 1.0))
        dr = float(rng.uniform(0.0, 0.5))
        seq = _markov_sequence(rng, n, n_states, reg, dr)
        c, g = _score(seq)
        comp_s.append(c); gen_s.append(g); drift_s.append(dr)
    comp_s = np.asarray(comp_s); gen_s = np.asarray(gen_s); drift_s = np.asarray(drift_s)
    rho_compress_gen = _spearman(comp_s, gen_s)
    rho_drift_gen = _spearman(drift_s, gen_s)
    rho_compress_drift = _spearman(comp_s, drift_s)
    partial = _partial_spearman(comp_s, gen_s, drift_s)  # diagnostic (cf docstring)

    # --- regime non-stationnaire : train compressible + test decale ------------
    # regularite du train tiree (compressibilite variable) ; test systematiquement
    # decale (dr_test eleve) -> decouplage train/test = le vrai null falsifiant.
    comp_ns, gen_ns = [], []
    for _ in range(int(n_trials)):
        reg_train = float(rng.uniform(0.0, 1.0))
        seq = _markov_sequence_two_regime(rng, n // 2, n_states,
                                          reg_train, 0.0,    # train compressible
                                          0.0, 0.5)           # test decale
        c, g = _score(seq)
        comp_ns.append(c); gen_ns.append(g)
    comp_ns = np.asarray(comp_ns); gen_ns = np.asarray(gen_ns)
    rho_compress_gen_nonstationary = _spearman(comp_ns, gen_ns)

    bridge = 1.0 if (rho_compress_gen > 0.7 and rho_compress_gen_nonstationary < -0.3) else 0.0

    return {
        "n_trials": int(n_trials),
        "rho_compress_gen": float(rho_compress_gen),
        "rho_compress_gen_nonstationary": float(rho_compress_gen_nonstationary),
        "rho_drift_gen": float(rho_drift_gen),
        "rho_compress_drift": float(rho_compress_drift),
        "partial_rho_compress_gen_given_drift": float(partial),
        "bridge_compression_to_generalization": bridge,
    }


# --------------------------------------------------------------------------- #
#  Bridge #2 : recouvrabilite (recovery_score) -> agentivite (repair_gain)     #
# --------------------------------------------------------------------------- #


def _naive_repair_trajectory(
    target_structures: List[float],
    seed: int,
) -> List[float]:
    """Modele nul : trajectoire de reparation NAIVE-EQUIVALENTE.

    Le null reproduit la meme sequence de structures regionales ``target_structures``
    (par exemple, la trajectoire que la reaction-diffusion a reellement suivie)
    par un **random walk calibre** : a chaque pas, on tire un increment de loi
    gaussienne centree dont la variance est choisie pour atteindre l'ecart-type
    observe des increments du vrai systeme. Ce modele n'a AUCUNE anticipation : il
    ne regarde ni le gradient de la structure, ni la courbure locale du champ, ni
    la disponibilite des voisines. Il « reussit » le score final par chance
    statistique, pas par regulation.

    C'est le pendant falsifiable du null « broadcast present mais ignore » de
    bridge #4 et du null « drift constant mais orthogonal » de bridge #5 :
    reproduire la sortie sans reproduire la dynamique.
    """
    rng = np.random.default_rng(seed)
    out: List[float] = list(target_structures)
    increments = np.diff(np.asarray(target_structures, dtype=float))
    if increments.size < 2:
        return out
    sigma = float(np.std(increments)) + 1e-12
    for i in range(1, len(out)):
        # random walk d'incertitude constante ; la trajectoire garde le point
        # de depart (post-ablation) et le point final (cible) mais le chemin
        # entre les deux n'est PAS contraint par anticipation.
        out[i] = float(out[i - 1] + rng.normal(0.0, sigma))
    # on ancre les deux extremites (post-ablation, cible) au signal observe pour
    # que la comparaison reste sur la SIGNATURE TEMPORELLE, pas sur l'amplitude.
    out[0] = target_structures[0]
    out[-1] = target_structures[-1]
    return out


def _trajectory_signature(structures: List[float]) -> Dict[str, float]:
    """Signature temporelle d'une trajectoire de recuperation (scalaires 5-D).

    Retourne un dict :
      - ``early_slope`` : taux marginal moyen sur le premier tiers (le vrai systeme
        reussit-il plus vite au debut ?) ;
      - ``late_slope`` : taux marginal moyen sur le dernier tiers (ralentit-il ?) ;
      - ``slope_ratio`` : ``early_slope / late_slope`` (ratio de concentration) ;
      - ``monotonicity`` : 1 - (nb de rebroussements / (n-1)) ; 1 = strictement
        croissant, 0 = oscillation pure ;
      - ``skewness`` : asymetrie des increments (distribution des gains) ; >0
        = concentres en debut, <0 = concentres en fin.
    """
    s = np.asarray(structures, dtype=float)
    n = s.size
    if n < 3:
        return {
            "early_slope": 0.0,
            "late_slope": 0.0,
            "slope_ratio": 0.0,
            "monotonicity": 1.0,
            "skewness": 0.0,
        }
    inc = np.diff(s)
    third = max(1, n // 3)
    early = float(np.mean(inc[:third])) if third > 0 else 0.0
    late = float(np.mean(inc[-third:])) if third > 0 else 0.0
    ratio = float(early / (abs(late) + 1e-12))
    n_turns = int(np.sum(np.sign(inc[1:]) * np.sign(inc[:-1]) < 0))
    monotonicity = float(1.0 - n_turns / max(1, inc.size - 1))
    mu = float(np.mean(inc))
    sd = float(np.std(inc)) + 1e-12
    skewness = float(np.mean(((inc - mu) / sd) ** 3)) if sd > 1e-12 else 0.0
    return {
        "early_slope": early,
        "late_slope": late,
        "slope_ratio": ratio,
        "monotonicity": monotonicity,
        "skewness": skewness,
    }


def bridge_recoverability_to_agency(
    n_trials: int = 80,
    n: int = 64,
    block: int = 8,
    steps: int = 800,
    record_every: int = 20,
    seed: int = 0,
    F: float = 0.0367,
    k: float = 0.0649,
) -> Dict[str, float]:
    r"""Bridge #2 : recouvrabilite (``recovery_score``) -> agentivite (``repair_gain``) (falsifiable, #8077 pont 2).

    Hypothese naive (la mesure d'agence d'ICT-9) : un systeme qui **reussit a
    reparer** une structure apres ablation est d'autant PLUS **agentif** que sa
    recuperation est profonde. C'est le pont implicite que ``repair_gain`` (ICT-9)
    presume : ``recouvrabilite -> agentivite``. Le substrat : une ablation
    aleatoire (:func:`ict.agency.disk_mask`) sur le systeme Gray-Scott (:mod:`ict.
    reaction_diffusion`), puis integration et lecture de la trajectoire de
    structure regionale dans la zone ablatee.

    La subtilite (qui rend le pont NON tautologique et falsifiable) est que le
    **meme score final** ``recovery_score`` peut etre atteint par deux systemes
    tres differents : un qui **repare regulierement** (anticipation, regulation)
    et un qui **tombe juste** par chance (random walk calibre sur les memes
    extremas). Si l'agentivite se reduit au score final, le pont est trivial ;
    si elle porte sur la **dynamique** (comment on arrive au score), le pont
    falsifie. On distingue donc la trajectoire vraie (reaction-diffusion) d'une
    trajectoire **naive-équivalente** (:func:`_naive_repair_trajectory`) qui
    reproduit les points extremaux mais pas la regulation interne.

    Mesure discriminante : la **signature temporelle** (:func:`_trajectory_signature`)
    comparee par **distance de Mahalanobis** sur les 5 dimensions (early_slope,
    late_slope, slope_ratio, monotonicity, skewness). Si la trajectoire vraie est
    significativement distincte du null (distance > p95 du null par
    permutation des labels), le pont tient. Sinon, le pont est **partiellement
    falsifie** : la **mesure** d'agentivite (score final) est insuffisante, il
    faut une signature temporelle pour la qualifier.

    Controle nul structurel : un systeme purement diffusif (meme ``recovery_score``
    plus bas) est le contrepoint : sa trajectoire de recuperation est **plate**
    (peu ou pas d'increments), donc une signature tres eloignee du systeme
    reaction-diffusion ET du null naif. Verifier que la discrimination porte
    BIEN sur la dynamique (true vs naive), pas sur l'absence de dynamique
    (diffusion).

    Verdict falsifiable
    -------------------
    ``bridge_recoverability_to_agency`` : 1.0 si la trajectoire vraie est
        significativement distincte du null (distance Mahalanobis > p95 par
        permutation) ET la discrimination porte reellement sur la dynamique
        (true <-> naive, pas juste true <-> diffusion). 0.0 sinon : la mesure
        scalaire d'agence est insuffisante, l'agentivite est une propriete de
        la **dynamique** (pas seulement de l'amplitude finale).

    Robuste (c.1014-L) : le verdict tient sur plusieurs graines (la trajectoire
    null est regeneree par ``seed`` ; le systeme Gray-Scott lui-meme depend du
    seed via ``seed()``, donc la mesure fluctue de maniere non triviale).
    """
    from . import agency as A
    from . import reaction_diffusion as RD

    rng = np.random.default_rng(seed)
    model = RD.GrayScott(F=F, k=k, Du=0.16, Dv=0.08, dt=1.0)

    # vecteurs de la signature temporelle (5 dimensions) pour chaque essai :
    # - vrai systeme (reaction-diffusion) ;
    # - null naif (memes extremas, chemin random) ;
    # - controle structurel (diffusion pure, attendu : signature tres differente).
    sigs_true: List[Dict[str, float]] = []
    sigs_naive: List[Dict[str, float]] = []
    sigs_diff: List[Dict[str, float]] = []

    for trial in range(int(n_trials)):
        trial_seed = int(rng.integers(0, 2**31 - 1))
        rng_trial = np.random.default_rng(trial_seed)
        U0, V0 = model.seed(n=n, block=block, rng=rng_trial)
        # choix d'un rayon d'ablation adapte a la grille (8 <= n=64, region
        # non negligeable mais pas dominante : ~13% de la grille).
        cx = float(rng_trial.uniform(n * 0.30, n * 0.70))
        cy = float(rng_trial.uniform(n * 0.30, n * 0.70))
        radius = float(rng_trial.uniform(n * 0.10, n * 0.18))
        mask = A.disk_mask(n, cx, cy, radius)
        U_abl, V_abl = A.ablate(U0, V0, mask)
        # --- vrai systeme : reaction-diffusion ---
        U_end, V_end, snaps = model.run(
            U_abl, V_abl, steps, record_every=record_every, include_initial=True
        )
        # trajectoire de structure regionale (variance sur le masque)
        struct_true = [
            float(np.var(s[mask])) for s in snaps
        ]
        # --- null naif : meme point final, chemin random ---
        struct_naive = _naive_repair_trajectory(struct_true, trial_seed + 17)
        # --- controle structurel : diffusion pure ---
        V_diff_end = RD.run_pure_diffusion(V_abl, model.Dv, steps)
        # trajectoire diff : on approxime par interpolation lineaire entre
        # la structure initiale et la structure finale (la diffusion pure n'a
        # pas de snapshots intermediaires, on prend la trajectoire triviale).
        s_init = float(np.var(V_abl[mask]))
        s_end = float(np.var(V_diff_end[mask]))
        struct_diff = list(np.linspace(s_init, s_end, len(struct_true)))

        sigs_true.append(_trajectory_signature(struct_true))
        sigs_naive.append(_trajectory_signature(struct_naive))
        sigs_diff.append(_trajectory_signature(struct_diff))

    # conversion en matrices (n_trials x 5)
    def _stack(sigs: List[Dict[str, float]]) -> np.ndarray:
        return np.asarray(
            [
                [
                    s["early_slope"],
                    s["late_slope"],
                    s["slope_ratio"],
                    s["monotonicity"],
                    s["skewness"],
                ]
                for s in sigs
            ],
            dtype=float,
        )

    M_true = _stack(sigs_true)
    M_naive = _stack(sigs_naive)
    M_diff = _stack(sigs_diff)

    # distance de Mahalanobis pairwise (essai i : true vs naive)
    diff_tn = M_true - M_naive
    # estimation de la matrice de covariance pooled (true + naive) pour la
    # distance de Mahalanobis.
    pooled = np.vstack([M_true, M_naive])
    cov = np.cov(pooled, rowvar=False)
    # regularisation pour eviter singularite.
    cov = cov + 1e-6 * np.eye(cov.shape[0])
    inv_cov = np.linalg.pinv(cov)
    # distance euclidienne puis Mahalanobis (approximation diagonale) si la
    # matrice est mal conditionnee.
    try:
        dist_tn = float(
            np.sqrt(np.einsum("ij,jk,ik->i", diff_tn, inv_cov, diff_tn).mean())
        )
    except np.linalg.LinAlgError:
        dist_tn = float(np.sqrt((diff_tn ** 2).sum(axis=1).mean()))

    # discrimination vraie vs diffusion : autre proxy (les signatures sont
    # tres differentes par construction, on le mesure).
    diff_td = M_true - M_diff
    try:
        dist_td = float(
            np.sqrt(np.einsum("ij,jk,ik->i", diff_td, inv_cov, diff_td).mean())
        )
    except np.linalg.LinAlgError:
        dist_td = float(np.sqrt((diff_td ** 2).sum(axis=1).mean()))

    # null par permutation : on brouille les labels true/naive et on recalcule
    # la distance Mahalanobis. Le p95 de cette distribution est le seuil
    # « significatif au-dela du hasard ».
    n_shuffle = 200
    null_dist = np.empty(int(n_shuffle), dtype=float)
    for s_idx in range(int(n_shuffle)):
        labels = rng.permutation(2 * len(M_true))
        M_pool = np.vstack([M_true, M_naive])[labels]
        M_a = M_pool[: len(M_true)]
        M_b = M_pool[len(M_true):]
        d = M_a - M_b
        try:
            null_dist[s_idx] = float(
                np.sqrt(np.einsum("ij,jk,ik->i", d, inv_cov, d).mean())
            )
        except np.linalg.LinAlgError:
            null_dist[s_idx] = float(np.sqrt((d ** 2).sum(axis=1).mean()))
    p95_null = float(np.percentile(null_dist, 95))

    # diagnostic : la discrimination porte-t-elle sur la dynamique (true vs
    # naive, qui ont le meme score final attendu) OU seulement sur l'absence
    # de dynamique (diffusion = pathologie) ? Si dist_td > dist_tn * 1.5, c'est
    # probablement le second cas (pathologique), pas le premier (le pont reel).
    dynamic_ratio = dist_tn / (dist_td + 1e-12)

    # verdict : la signature vraie est distincte du null (dist > p95) ET le
    # ratio dynamique est >= 0.5 (la discrimination n'est pas uniquement
    # pathologique).
    bridge = 1.0 if (dist_tn > p95_null and dynamic_ratio >= 0.5) else 0.0

    return {
        "n_trials": int(n_trials),
        "n": int(n),
        "steps": int(steps),
        "mahalanobis_true_vs_naive": dist_tn,
        "mahalanobis_true_vs_diffusion": dist_td,
        "dynamic_discrimination_ratio": dynamic_ratio,
        "p95_null_mahalanobis": p95_null,
        "mean_signature_true": {
            k: float(np.mean([s[k] for s in sigs_true])) for k in sigs_true[0]
        },
        "mean_signature_naive": {
            k: float(np.mean([s[k] for s in sigs_naive])) for k in sigs_naive[0]
        },
        "mean_signature_diffusion": {
            k: float(np.mean([s[k] for s in sigs_diff])) for k in sigs_diff[0]
        },
        "bridge_recoverability_to_agency": bridge,
    }
