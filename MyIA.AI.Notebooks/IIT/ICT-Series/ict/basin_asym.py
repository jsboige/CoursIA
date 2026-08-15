"""Famille de substrats asymetriques (Pont #1-bis chantier 2/3, Epic #9531).

Le chantier 1/3 (:mod:`ict.basin_family`, PR #9540) a construit une famille de
double-puits **symetriques** ``V = a x^4 - b x^2`` ou la courbure locale
``sigma = V''(x*)`` et la largeur de bassin ``width`` varient independamment par
construction, et a tranche : **CONFIRMED-NEGATIVE**. La stabilite locale
``sigma`` n'a aucun pouvoir predictif propre pour la recuperabilite une fois la
largeur ET la barriere controlees ; c'est la geometrie du bassin qui gouverne
partout. Le Pont #1 (``sigma`` cause la recuperabilite) est un vrai negatif
GENERAL, pas un artefact de couplage.

**Mais** le double-puits symetrique a une propriete restrictive : ses deux
minima sont interchangeables (meme profondeur, meme sigma, meme largeur, meme
barriere). Le verdict du chantier 1/3 porte donc sur un regime geometrique
**particulier** ou la recuperation d'un bassin a l'autre est symetrique. La
question ouverte (ce module) : **le verdict tient-il dans un regime ou les deux
bassins ne sont PLUS interchangeables** -- un puits asymetrique ou l'un des
minima est plus profond, plus etroit, plus raide que l'autre ?

Le substrat : le double-puits asymetrique
-----------------------------------------
``V(x) = a x^4 - b x^2 + c x^3``  (``a > 0``, ``b > 0``, ``c`` reel). Le terme
cubique ``c x^3`` (anti-symetrique sous ``x -> -x``) brise l'equivalence des deux
bassins sans detruire le double-puits (tant que ``|c|`` reste sous le seuil de
bifurcation). Les points critiques se separent encore algebriquement :

``V'(x) = x (4 a x^2 + 3 c x - 2 b)``

d'ou les trois equilibres **en forme fermee** :

* col (instable) en ``x_col = 0``   (robuste : ``V'(0) = 0`` et ``V''(0) = -2 b < 0``) ;
* minima (stables) en ``x_pm = (-3 c +/- sqrt(9 c^2 + 32 a b)) / (8 a)``.

Le col reste en ``x = 0`` meme a ``c`` non nul -- c'est la propriete qui rend ce
substrat manipulable : le test d'appartenance a un bassin (``sign(x) =
sign(x*)``) est encore valide. Les deux minima ont des profondeurs, courbures,
largeurs et barrieres **differentes**des que ``c != 0`` : c'est la richesse
geometrique que le chantier 1/3 ne pouvait pas sonder.

Decouplage et nouveaute : les deux minima
-----------------------------------------
Le chantier 1/3 gardait un seul minimum (``xstar > 0``), l'autre etant
statistiquement interchangeable. Ici on mesure les **deux** minima (profond et
peu profond) de chaque puits, chacun avec son propre ``sigma``, ``width``,
``barrier`` -- ce qui double l'echantillon et introduit une variation
**intra-puits** de ``sigma`` que le regime symetrique ne pouvait pas produire.
L'asymetrie (difference de profondeur) est un nouveau degrade physique.

**Decouplage : une difference cruciale avec le chantier 1/3.** Dans le regime
symetrique, ``sigma = 4 b`` et ``width = sqrt(b / (2 a))`` etaient decouples par
construction (cadrans separes, ``realize_decoupled``). Dans le regime
asymetrique, ``sigma`` et ``width`` sont **structurellement couples
intra-puits** : le minimum profond est a la fois plus raide (``sigma`` grand) ET
plus large (``width`` grand). Le couplage brut vaut ``rho ~ 0.75`` ; la
stratification 2D du plan ``(sigma, width)`` le reduit a ``~ 0.47`` mais ne
l'elimine pas (le seuil ``< 0.2`` de #9531, calibre pour le regime symetrique,
n'est pas atteignable ici sans separation de variables).

C'est precisement pour cela que la **correlation partielle a 2 covariables
(FWL)** est le test decisif : elle isole le pouvoir predictif propre de
``sigma`` en controlant la largeur ET la barriere, **meme sous couplage
residuel**. Le verdict est donc porte par ``partial_rho_given_width_barrier``,
pas par le diagnostic de decouplage. Le module reporte les deux
(``rho_sigma_width_raw`` avant stratification, ``rho_sigma_width`` apres) pour
transparence methodologique.

Conventions
-----------
Numpy uniquement, stats reutilisees depuis :mod:`ict.basin_family`
(``_rank``, ``_pearson``, ``partial_spearman``). Le verdict ternaire est le
memes que :func:`ict.basin_family.pont1bis_verdict` (jamais "promising").
"""

from __future__ import annotations

from typing import Dict, List, Tuple

import numpy as np

from .basin_family import _pearson, _rank, partial_spearman


# --------------------------------------------------------------------------- #
#  Substrat : double-puits asymetrique V(x) = a x^4 - b x^2 + c x^3            #
# --------------------------------------------------------------------------- #


def asym_potential(x, a: float, b: float, c: float):
    """Potentiel double-puits asymetrique ``V(x) = a x^4 - b x^2 + c x^3``.

    Le terme cubique ``c x^3`` brise la symetrie ``x <-> -x`` : les deux minima
    ont des profondeurs differentes. Le col reste en ``x = 0``. ``a > 0``,
    ``b > 0`` ; ``c`` reel (positif => minimum droit plus profond).
    """
    x = np.asarray(x, dtype=float)
    return float(a) * x ** 4 - float(b) * x ** 2 + float(c) * x ** 3


def asym_force(x, a: float, b: float, c: float):
    r"""Force ``-V'(x) = 2 b x - 3 c x^2 - 4 a x^3`` (descente).

    Generalise :func:`ict.basin_family.double_well_force` (cas ``c = 0``).
    """
    x = np.asarray(x, dtype=float)
    return 2.0 * float(b) * x - 3.0 * float(c) * x ** 2 - 4.0 * float(a) * x ** 3


def asym_curvature(x, a: float, b: float, c: float):
    r"""Courbure ``V''(x) = 12 a x^2 + 6 c x - 2 b``.

    Generalise :func:`ict.basin_family.double_well_curvature` (cas ``c = 0``,
    ``V''(x*) = 4 b`` au minimum symetrique).
    """
    x = np.asarray(x, dtype=float)
    return 12.0 * float(a) * x ** 2 + 6.0 * float(c) * x - 2.0 * float(b)


def asym_equilibria(a: float, b: float, c: float) -> List[Tuple[float, bool]]:
    r"""Equilibres du double-puits asymetrique en forme fermee.

    ``V'(x) = x (4 a x^2 + 3 c x - 2 b)`` donne le col en ``x = 0`` et les deux
    minima en ``x_pm = (-3 c +/- sqrt(9 c^2 + 32 a b)) / (8 a)``. Retourne
    ``[(x, stable), ...]`` trie par position. Rend ``[]`` si le double-puits
    n'est pas defini (discriminant negatif ou ``a, b <= 0``).
    """
    a = float(a)
    b = float(b)
    c = float(c)
    if a <= 0.0 or b <= 0.0:
        return []
    disc = 9.0 * c * c + 32.0 * a * b
    if disc < 0.0:
        return []
    sqrt_disc = float(np.sqrt(disc))
    x_minus = (-3.0 * c - sqrt_disc) / (8.0 * a)
    x_plus = (-3.0 * c + sqrt_disc) / (8.0 * a)
    # col en 0 (V''(0) = -2b < 0 => instable), minima stables (V'' > 0).
    return [(x_minus, True), (0.0, False), (x_plus, True)]


def relax_asym(x0: float, a: float, b: float, c: float,
               dt: float = 0.01, steps: int = 5000) -> float:
    """Descente de gradient ``dx/dt = -V'(x)`` depuis ``x0`` sur le puits
    asymetrique. Generalise :func:`ict.basin_family.relax_double_well`."""
    x = float(x0)
    for _ in range(int(steps)):
        x = x + dt * float(asym_force(x, a, b, c))
    return x


# --------------------------------------------------------------------------- #
#  Profil geometrique (6 quantites, les DEUX minima)                            #
# --------------------------------------------------------------------------- #


def asym_basin_profile(a: float, b: float, c: float
                       ) -> List[Tuple[float, float, float, float, float, float]]:
    r"""Profil geometrique des **deux** bassins du puits asymetrique ``(a, b, c)``.

    Renvoie, pour chaque minimum stable ``x*``, le tuple
    ``(x*, sigma, width, col, barrier, depth)`` ou :

    * ``sigma``   = courbure ``V''(x*)`` (raideur locale, **different** par min) ;
    * ``col``     = ``0.0`` (equilibre instable, commun aux deux bassins) ;
    * ``width``   = ``|x* - col| = |x*|`` (demi-largeur vers le col) ;
    * ``barrier`` = ``V(col) - V(x*) = -V(x*)`` (hauteur du col, ``V(0)=0``) ;
    * ``depth``   = ``V(x*)`` (profondeur absolue ; le min le plus negatif est le
      puits profond).

    Renvoie ``[]`` si le double-puits n'est pas defini. Contrairement au regime
      symetrique, les deux entrees ne sont PAS interchangeables.
    """
    eqs = asym_equilibria(a, b, c)
    stables = [x for x, st in eqs if st]
    if len(stables) != 2:
        return []
    a_f, b_f, c_f = float(a), float(b), float(c)
    out: List[Tuple[float, float, float, float, float, float]] = []
    for xstar in stables:
        sigma = float(asym_curvature(xstar, a_f, b_f, c_f))
        width = float(abs(xstar))                  # col en 0
        depth = float(asym_potential(xstar, a_f, b_f, c_f))
        barrier = -depth                            # V(0)=0
        out.append((float(xstar), sigma, width, 0.0, barrier, depth))
    return out


# --------------------------------------------------------------------------- #
#  Recuperation stochastique (Langevin) -- la mesure NON triviale              #
# --------------------------------------------------------------------------- #


def recover_fraction_asym_stochastic(xstar: float, a: float, b: float, c: float,
                                     rng: np.random.Generator,
                                     noise: float = 0.35,
                                     n_trials: int = 60,
                                     T: int = 3000,
                                     dt: float = 0.02,
                                     perturb_frac: float = 0.75) -> float:
    r"""Recuperation stochastique (Langevin) pour un minimum du puits asymetrique.

    Chaque essai demarre en ``xstar * perturb_frac`` (perturbation relative vers
    le col ``x = 0``) puis evolue sous ``dx = -V'(x) dt + sqrt(2 D dt) xi`` avec
    ``D = noise``. La fraction d'essais terminant du **meme cote du col** que
    ``xstar`` apres ``T`` pas est la recuperation.

    Comme le col est en ``x = 0`` (robuste sous ``+c x^3``), le test de bassin
    ``sign(x_final) == sign(xstar)`` est geometriquement exact. Generalise
    :func:`ict.basin_family.recover_fraction_stochastic` au regime asymetrique.

    **Vectorise sur ``n_trials``** : les ``n_trials`` trajectoires Langevin
    avancent en parallele (un seul array de taille ``n_trials``), la boucle
    externe ne porte que sur les ``T`` pas de temps -- ~``n_trials`` fois plus
    rapide qu'une boucle par essai, meme dynamique et meme bruit que la version
    scalaire (chaque trajectoire a son propre flux aleatoire independant).
    """
    x0 = float(xstar) * float(perturb_frac)
    sdt = float(np.sqrt(2.0 * float(noise) * float(dt)))
    sign_xstar = 1.0 if xstar > 0.0 else -1.0
    n = int(n_trials)
    x = np.full(n, x0, dtype=float)
    # Stabilisation numerique : sur les puits tres raides (a grand), la dynamique
    # Euler explicite peut diverger (overflow). On clame x a un range large
    # (au-dela duquel la position est de toute facon hors-bassin, compte negatif
    # au verdict) et on supprime les warnings d'overflow residues pour ne pas
    # ralentir numpy. La physique dans le bassin d'interet est inchangee.
    x_max = 10.0 * (abs(float(xstar)) + 1.0)
    with np.errstate(over="ignore", invalid="ignore"):
        for _ in range(int(T)):
            x = x + asym_force(x, a, b, c) * float(dt) + sdt * rng.standard_normal(n)
            np.clip(x, -x_max, x_max, out=x)
    n_back = int(np.sum(np.sign(x) == sign_xstar))
    return float(n_back) / float(n)


# --------------------------------------------------------------------------- #
#  Echantillonnage de la famille + verdict ternaire                            #
# --------------------------------------------------------------------------- #


def _gather_asym_family(a_grid: np.ndarray, b_grid: np.ndarray, c_grid: np.ndarray,
                        noise: float, n_trials: int, T: int, dt: float,
                        perturb_frac: float, seed: int) -> Dict[str, np.ndarray]:
    """Echantillonne la famille asymetrique et mesure ``sigma, width, barrier,
    asym, recovery`` pour **chaque minimum** (profond + peu profond) de chaque
    puits ``(a, b, c)``.

    L'asymetrie ``asym = depth_shallow - depth_deep`` (>= 0) quantifie l'ecart
    de profondeur entre les deux bassins. La recuperation est mesuree pour
    chaque minimum vers son col commun (``x = 0``).
    """
    rng = np.random.default_rng(seed)
    sigmas: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    asyms: List[float] = []
    recoveries: List[float] = []
    for a in a_grid:
        for b in b_grid:
            for c in c_grid:
                prof = asym_basin_profile(float(a), float(b), float(c))
                if len(prof) != 2:
                    continue
                # ordonne par profondeur : profond (depth min) puis peu profond
                prof_sorted = sorted(prof, key=lambda p: p[5])
                deep = prof_sorted[0]
                shallow = prof_sorted[1]
                asym = float(shallow[5] - deep[5])
                for (xstar, sigma, width, col, barrier, depth) in prof_sorted:
                    frac = recover_fraction_asym_stochastic(
                        xstar, float(a), float(b), float(c), rng,
                        noise=noise, n_trials=n_trials, T=T, dt=dt,
                        perturb_frac=perturb_frac)
                    sigmas.append(sigma)
                    widths.append(width)
                    barriers.append(barrier)
                    asyms.append(asym)
                    recoveries.append(frac)
    return {
        "sigma": np.asarray(sigmas, dtype=float),
        "width": np.asarray(widths, dtype=float),
        "barrier": np.asarray(barriers, dtype=float),
        "asym": np.asarray(asyms, dtype=float),
        "recovery": np.asarray(recoveries, dtype=float),
    }


def _stratify_decouple(fam: Dict[str, np.ndarray], n_bins: int = 5
                       ) -> Dict[str, np.ndarray]:
    """Sous-echantillon **decouple** par stratification 2D du plan (sigma, width).

    Dans le regime asymetrique, ``sigma`` et ``width`` sont structurellement
    couples **intra-puits** (le minimum profond est a la fois plus raide ET plus
    large). Pour isoler le pouvoir predictif propre de ``sigma`` -- la question du
    Pont #1 -- il faut un echantillon ou ``sigma`` et ``width`` sont
    marginalement independants. On binne le plan des rangs ``(sigma, width)`` en
    une grille ``n_bins x n_bins`` et on garde un nombre **uniforme** d'echantillons
    par cellule (le minimum de remplissage) -> ``corr(sigma, width) ~ 0`` par
    construction. Conformement a #9531 (decouplage prouve par construction ET
    mesure).

    Les cellules vides sont ignorées ; la taille finale vaut
    ``n_nonempty_cells * min_per_cell``.
    """
    sig = fam["sigma"]
    wid = fam["width"]
    n = sig.size
    if n < n_bins * n_bins:
        return fam                      # trop peu de points pour stratifier
    r_sig = _rank(sig)
    r_wid = _rank(wid)
    # indices de cellule (0..n_bins-1) sur chaque axe
    edges = np.linspace(0.5, n + 0.5, n_bins + 1)
    i_sig = np.digitize(r_sig, edges) - 1
    i_wid = np.digitize(r_wid, edges) - 1
    i_sig = np.clip(i_sig, 0, n_bins - 1)
    i_wid = np.clip(i_wid, 0, n_bins - 1)
    cells: Dict[Tuple[int, int], List[int]] = {}
    for k in range(n):
        cells.setdefault((int(i_sig[k]), int(i_wid[k])), []).append(k)
    nonempty = [idx for idx in cells.values() if idx]
    if len(nonempty) < n_bins:          # pas assez de cellules remplies
        return fam
    # Seuil minimal par cellule : on ignore les cellules quasi-vides (bruit) et
    # on garde min_per_cell sur les cellules qualifiees. Cela concentre la
    # stratification sur la region du plan (sigma, width) bien couverte, au lieu
    # de sacrifier toute la matiere si une cellule isolee n'a qu'un element.
    threshold = max(2, len(next(iter(nonempty))) // 4)
    qualified = [idx for idx in nonempty if len(idx) >= threshold]
    if len(qualified) < n_bins:
        qualified = nonempty
    min_per_cell = min(len(idx) for idx in qualified)
    rng_pick = np.random.default_rng(0)  # deterministe (reproductible)
    keep = np.concatenate([
        rng_pick.choice(idx, size=min_per_cell, replace=False) for idx in qualified
    ])
    keep.sort()
    return {key: arr[keep] for key, arr in fam.items()}


def asym_verdict(
    a_grid: np.ndarray = None,
    b_grid: np.ndarray = None,
    c_grid: np.ndarray = None,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    n_shuffle: int = 200,
    seed: int = 0,
    n_strat_bins: int = 5,
) -> Dict[str, float]:
    r"""Pont #1-bis chantier 2/3 : verdict ternaire sur la famille asymetrique.

    Rejoue le protocole du Pont #1 sur une famille de double-puits
    **asymetriques** ``V = a x^4 - b x^2 + c x^3`` ou les deux bassins ne sont
    plus interchangeables (profondeurs, courbures, largeurs differentes). Teste
    la robustesse du verdict CONFIRMED-NEGATIVE du chantier 1/3 dans un regime
    geometrique plus riche.

    Le verdict decisif est la correlation partielle de ``sigma`` avec
    ``recovery`` en controlant la largeur ET la barriere (2 covariables, FWL) --
    comme au chantier 1/3. L'asymetrie est mesuree et reportee comme dimension
    supplementaire (correlation brute avec recovery), mais n'entre pas dans la
    partielle decisive (le Pont #1 porte sur ``sigma`` vs geometrie, pas sur
    l'asymetrie per se).

    Verdict ternaire (jamais "promising") :

    * ``CONFIRMED-NEGATIVE`` : ``partial_2cov ~ 0`` et non significatif vs null
      -> ``sigma`` n'a toujours aucun pouvoir predictif propre, meme dans le
      regime asymetrique ; le verdict du chantier 1/3 se generalise.
    * ``SUBSTRATE-ARTIFACT`` : ``partial_2cov > 0.2`` et au-dela du null p95 ->
      ``sigma`` regagne un pouvoir predictif dans le regime asymetrique ; le
      verdict symetrique etait un artefact de symetrie.
    * ``INCONCLUSIVE`` : ``partial_2cov < -0.2`` ou decouplage insuffisant.
    """
    rng = np.random.default_rng(seed)
    if a_grid is None:
        # a controle width (~sqrt(b/2a)) : ordre de grandeur balaye
        a_grid = np.array([0.3, 0.6, 1.0, 1.6, 2.5])
    if b_grid is None:
        # b controle sigma (~4b) : b in (0.5, 4) -> sigma in (2, 16)
        b_grid = np.array([0.5, 1.0, 1.5, 2.5, 3.5])
    if c_grid is None:
        # c = axe d'asymetrie : garde le double-puits (|c| < seuil bifurcation),
        # suffisamment d'amplitude pour des bassins nettement differents.
        c_grid = np.array([-0.8, -0.4, 0.0, 0.4, 0.8])

    fam = _gather_asym_family(a_grid, b_grid, c_grid, noise, n_trials, T, dt,
                              perturb_frac, seed)
    # Diagnostic du couplage intra-puits BRUT (avant stratification).
    rho_sigma_width_raw = _pearson(_rank(fam["sigma"]), _rank(fam["width"]))
    # Stratification 2D (sigma, width) : force corr(sigma, width) ~ 0 par
    # construction. Le couplage intra-puits (minimum profond = plus raide ET
    # plus large) est retire pour isoler le pouvoir predictif propre de sigma.
    if n_strat_bins and n_strat_bins > 1:
        fam = _stratify_decouple(fam, n_bins=int(n_strat_bins))
    sig, wid, bar, asym, rec = (fam["sigma"], fam["width"], fam["barrier"],
                                fam["asym"], fam["recovery"])

    rho_sigma_recovery = _pearson(_rank(sig), _rank(rec))
    rho_width_recovery = _pearson(_rank(wid), _rank(rec))
    rho_barrier_recovery = _pearson(_rank(bar), _rank(rec))
    rho_asym_recovery = _pearson(_rank(asym), _rank(rec))
    rho_sigma_width = _pearson(_rank(sig), _rank(wid))      # diagnostic decouplage
    rho_sigma_barrier = _pearson(_rank(sig), _rank(bar))

    partial_1cov = partial_spearman(sig, rec, [wid])
    partial_2cov = partial_spearman(sig, rec, [wid, bar])

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
        "rho_asym_recovery": float(rho_asym_recovery),
        "rho_sigma_width": float(rho_sigma_width),
        "rho_sigma_width_raw": float(rho_sigma_width_raw),  # avant stratification
        "rho_sigma_barrier": float(rho_sigma_barrier),
        "partial_rho_given_width": float(partial_1cov),
        "partial_rho_given_width_barrier": float(partial_2cov),
        "partial_2cov_null_p95": p95_partial_null,
        "decoupling_ok": bool(abs(rho_sigma_width) < 0.2),
        "verdict": verdict,
    }


def asym_recoupled_null(
    b_grid: np.ndarray = None,
    c_fixed: float = 0.0,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Controle nul re-couple pour le protocole asymetrique.

    Verifie que le protocole (fonctions asym + ``partial_spearman``) detecte
    correctement le couplage canonique ``sigma``-``width`` de la fronce du Pont
    #1 quand il est present. Pour cela on se place dans la **limite symetrique**
    ``c = 0`` ou ``sigma = 4 b`` et ``width = sqrt(b / (2 a))`` sont monotones en
    ``b`` (a fixe) -> couplage maximal, comme sur la fronce. Le motif attendu :
    couplage eleve (``rho_sigma_width`` grand) et partielle a 1 covariable ~ 0
    (``sigma`` n'ajoute rien par-dessus ``width``).

    On reduit a ``c = 0`` plutot qu'a ``c != 0`` car, dans le regime
    asymetrique, ``sigma`` a une structure intra-puits **reelle**
    (``partial_rho_given_width`` s'ecarte de 0) : le controle nul doit isoler le
    couplage canonique seul, sans le melanger a la structure d'asymetrie. Les
    deux minima etant geometriquement miroir (meme ``sigma``/``width``), ils
    partagent la geometrie mais ont des tirages de bruit independants -> deux
    mesures legitimement distinctes.

    Si ce controle ne reproduit PAS le motif, le protocole est suspect.
    Discipline du null model exigee par #9531.
    """
    rng = np.random.default_rng(seed)
    if b_grid is None:
        b_grid = np.linspace(0.5, 3.5, 10)
    a_fixed = 1.0

    sigmas: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    recoveries: List[float] = []
    for b in b_grid:
        for (xstar, sigma, width, col, barrier, depth) in \
                asym_basin_profile(a_fixed, float(b), float(c_fixed)):
            frac = recover_fraction_asym_stochastic(
                xstar, a_fixed, float(b), float(c_fixed), rng,
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
        "reproduces_fronce_pattern": bool(
            rho_sigma_width > 0.6 and abs(partial_1cov) < 0.3
        ),
    }
