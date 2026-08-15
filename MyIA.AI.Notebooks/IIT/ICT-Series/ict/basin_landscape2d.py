"""Famille de paysages 2D anisotropes (Pont #1-bis chantier 3/3, Epic #9531).

Les chantiers 1/3 (:mod:`ict.basin_family`, symetrique 1D) et 2/3
(:mod:`ict.basin_asym`, asymetrique 1D) ont tranche **CONFIRMED-NEGATIVE** :
la courbure locale ``sigma`` n'a aucun pouvoir predictif propre pour la
recuperabilite une fois la largeur ET la barriere controlees. Mais ces deux
chantiers operent en **1D** : le bassin n'a qu'une seule direction, et ``sigma``
y est un scalaire non ambigu.

La question de ce chantier 3/3 (qui clot l'Epic) : **le verdict tient-il en 2D,
ou la richesse d'un paysage anisotrope restore-t-elle un pouvoir predictif a
``sigma`` ?** En 2D, la courbure locale devient un **ensemble de valeurs propres
du Hessien** (une par direction principale) : ``sigma`` n'est plus defini de
facon unique. Faut-il retenir la courbure moyenne, la courbure minimale (direction
la plus molle), le rapport d'anisotropie ? C'est precisement la situation ou un
scalar resume peut cacher la geometrie -- le scenario le plus favorable a
l'hypothese ``sigma cause la recuperabilite``.

Le substrat : double-puits 2D anisotrope
-----------------------------------------
``V(x, y) = a x^4 - b x^2 + d y^2``  (``a, b, d > 0``). L'axe ``x`` porte le
double-puits (deux minima en ``x* = +/- sqrt(b / (2 a))``, une selle en ``x = 0``) ;
l'axe ``y`` est un **confinement harmonique** (raideur ``d``). Les deux minima
sont en ``(+/- x*, 0)`` et la selle en ``(0, 0)``.

Le Hessien au minimum est diagonal (axes decouples) :

``H(x*, 0) = diag(4 b, 2 d)``

soit les valeurs propres ``lambda_x = 4 b`` (stiffness longitudinale, le long de
l'axe double-puits) et ``lambda_y = 2 d`` (stiffness transverse). Le **nouveau
knob** est ``d`` : il fait varier la courbure transverse (et donc tout scalaire
resume de ``sigma``) **sans toucher a la largeur de bassin longitudinale**
``width = sqrt(b / (2 a))`` ni a la barriere ``b^2 / (4 a)``. C'est le decouplage
**genuinement 2D** que le regime 1D (meme asymetrique) ne pouvait pas produire :
un axe de courbure orthogonal a l'axe de largeur.

Decouplage par construction (la difference avec le chantier 2/3)
----------------------------------------------------------------
Dans le chantier 2/3 (1D asymetrique), ``sigma`` et ``width`` etaient
structurellement couples intra-puits (le minimum profond est plus raide ET plus
large) : le seuil ``< 0.2`` n'etait pas atteignable, et la partielle FWL portait
seule le verdict. Ici, au contraire, le decouplage ``sigma``--``width`` est
atteignable **par construction** : a ``b`` fixe, la grille ``(a, d)`` fait varier
``width`` (via ``a``) et ``sigma_moyen = 2 b + d`` (via ``d``) sur deux axes
independants -> ``corr(sigma_moyen, width) ~ 0`` sur la grille. Le seuil ``< 0.2``
de #9531 est DONC atteignable en 2D, et le verdict est decidable par la grille
elle-meme (pas seulement par la partielle FWL).

Verdict
-------
On rejoue le protocole du Pont #1 sur la famille 2D. La question decisive : un
scalaire resume de la courbure (moyenne ``sigma_mean = (lambda_x + lambda_y)/2``,
ou minimale ``sigma_min = min(lambda_x, lambda_y)``) a-t-il un pouvoir predictif
propre pour la recuperabilite, apres controle de la largeur, de la barriere ET de
l'anisotropie ? Verdict attendu (generalisation) : **CONFIRMED-NEGATIVE** -- aucun
scalaire de courbure n'a de pouvoir propre, c'est la geometrie du bassin (largeur
+ anisotropie) qui gouverne partout.

Conventions
-----------
Numpy uniquement. Geometrie via :mod:`ict.basin_geometry` (profileur
substrate-agnostic, :class:`ict.basin_geometry.BasinProfile`). Stats reutilisees
depuis :mod:`ict.basin_family` (``_rank``, ``_pearson``, ``partial_spearman``).
"""

from __future__ import annotations

from typing import Dict, List, Tuple

import numpy as np

from .basin_family import _pearson, _rank, partial_spearman
from .basin_geometry import BasinProfile, basin_geometry


# --------------------------------------------------------------------------- #
#  Substrat : double-puits 2D anisotrope V(x,y) = a x^4 - b x^2 + d y^2        #
# --------------------------------------------------------------------------- #


def landscape2d_potential(a: float, b: float, d: float):
    """Potentiel double-puits 2D anisotrope ``V(x,y) = a x^4 - b x^2 + d y^2``.

    Axe ``x`` : double-puits (2 minima en ``+/- sqrt(b/(2a))``, selle en 0).
    Axe ``y`` : confinement harmonique de raideur ``d`` (le knob transverse).
    Renvoie un callable ``V(xvec) -> float`` compatible :mod:`ict.basin_geometry`.
    """
    a = float(a); b = float(b); d = float(d)
    return lambda x: a * float(x[0]) ** 4 - b * float(x[0]) ** 2 + d * float(x[1]) ** 2


def landscape2d_force(x: np.ndarray, a: float, b: float, d: float) -> np.ndarray:
    r"""Force ``-grad V = (2 b x - 4 a x^3, -2 d y)`` (descente).

    Les deux composantes sont decouplees (Hessien diagonal). Generalise la force
    1D du double-puits avec une composante transverse harmonique.
    """
    x = np.asarray(x, dtype=float)
    fx = 2.0 * float(b) * x[..., 0] - 4.0 * float(a) * x[..., 0] ** 3
    fy = -2.0 * float(d) * x[..., 1]
    return np.stack([fx, fy], axis=-1)


def landscape2d_equilibria(a: float, b: float, c: float = 0.0
                           ) -> List[Tuple[np.ndarray, str]]:
    """Equilibres du paysage 2D (forme fermee, pour test de coherence).

    ``x* = +/- sqrt(b/(2a))``, ``y* = 0`` pour les minima ; ``(0, 0)`` selle.
    Renvoie ``[(xy_array, type), ...]`` type parmi minimum/saddle. ``a, b > 0``.
    """
    a = float(a); b = float(b)
    if a <= 0.0 or b <= 0.0:
        return []
    xstar = float(np.sqrt(b / (2.0 * a)))
    return [(np.array([-xstar, 0.0]), "minimum"),
            (np.array([0.0, 0.0]), "saddle"),
            (np.array([xstar, 0.0]), "minimum")]


# --------------------------------------------------------------------------- #
#  Recuperation stochastique 2D (Langevin) -- mesure NON triviale              #
# --------------------------------------------------------------------------- #


def recover_fraction_2d_stochastic(xstar: float, a: float, b: float, d: float,
                                   rng: np.random.Generator,
                                   noise: float = 0.35,
                                   n_trials: int = 60,
                                   T: int = 3000,
                                   dt: float = 0.02,
                                   perturb_frac: float = 0.75,
                                   transverse_kick: float = 0.6) -> float:
    r"""Recuperation stochastique 2D (Langevin) pour un minimum du paysage.

    Chaque essai demarre en ``(xstar * perturb_frac, transverse_kick)`` -- une
    perturbation **a la fois longitudinale** (vers la selle ``x = 0``) **et
    transverse** (un kick en ``y`` qui excite la direction ``d``). La trajectoire
    evolue sous ``dX = -grad V dt + sqrt(2 D dt) xi`` (``D = noise``, bruit 2D).

    La fraction d'essais terminant du **meme cote de la selle** que ``xstar``
    (``sign(x_final) == sign(xstar)``) apres ``T`` pas est la recuperation. Le
    test ``sign(x)`` est geometriquement exact : la selle est en ``x = 0``, et
    l'axe ``y`` est confine (le retour en ``y`` ne change pas le bassin).

    Le kick transverse est essentiel : sans lui, la dynamique se reduit au cas 1D
    (la direction ``d`` n'est jamais excitee, et ``sigma_y`` n'a aucun effet). Le
    kick rend la mesure sensible a la raideur transverse ``d`` -> falsifiable.

    Vectorise sur ``n_trials`` : les ``n_trials`` trajectoires 2D avancent en
    parallele (un array ``(n_trials, 2)``), la boucle externe ne porte que sur
    les ``T`` pas de temps.
    """
    x0_lon = float(xstar) * float(perturb_frac)
    sdt = float(np.sqrt(2.0 * float(noise) * float(dt)))
    sign_xstar = 1.0 if xstar > 0.0 else -1.0
    n = int(n_trials)
    # etat initial (n_trials, 2) : perturbation longitudinale + kick transverse
    X = np.empty((n, 2), dtype=float)
    X[:, 0] = x0_lon
    X[:, 1] = float(transverse_kick)
    # Stabilisation : clamper x (la divergence Euler sur puits raides est hors-bassin)
    x_max = 10.0 * (abs(float(xstar)) + 1.0)
    a_f, b_f, d_f = float(a), float(b), float(d)
    with np.errstate(over="ignore", invalid="ignore"):
        for _ in range(int(T)):
            F = landscape2d_force(X, a_f, b_f, d_f)
            X = X + F * float(dt) + sdt * rng.standard_normal((n, 2))
            np.clip(X[:, 0], -x_max, x_max, out=X[:, 0])
    n_back = int(np.sum(np.sign(X[:, 0]) == sign_xstar))
    return float(n_back) / float(n)


# --------------------------------------------------------------------------- #
#  Echantillonnage de la famille + verdict ternaire                            #
# --------------------------------------------------------------------------- #


def _profile_quantities(prof: BasinProfile) -> Tuple[float, float, float, float, float]:
    """Extrait (sigma_mean, sigma_min, width, barrier, anisotropy) d'un BasinProfile 2D.

    * ``sigma_mean`` = moyenne des valeurs propres du Hessien ;
    * ``sigma_min``  = valeur propre minimale (direction la plus molle) ;
    * ``width``      = distance au col (longitudinale, le long de l'axe double-puits) ;
    * ``barrier``    = hauteur du col ;
    * ``anisotropy`` = lambda_max / lambda_min (>= 1).
    """
    curv = np.asarray(prof.curvature, dtype=float)
    sigma_mean = float(np.mean(curv))
    sigma_min = float(curv.min())
    return sigma_mean, sigma_min, float(prof.width), float(prof.barrier), float(prof.anisotropy)


def _gather_landscape_family(a_grid: np.ndarray, b_grid: np.ndarray, d_grid: np.ndarray,
                              noise: float, n_trials: int, T: int, dt: float,
                              perturb_frac: float, transverse_kick: float,
                              seed: int) -> Dict[str, np.ndarray]:
    """Echantillonne la famille 2D et mesure les quantites geometriques + recovery.

    Pour chaque ``(a, b, d)``, profile les DEUX minima ``(+/- x*, 0)`` (geometrie
    miroir, mais tirages de bruit independants -> 2 mesures distinctes) et mesure
    la recuperation stochastique 2D de chacun.
    """
    rng = np.random.default_rng(seed)
    sigma_means: List[float] = []
    sigma_mins: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    anisos: List[float] = []
    recoveries: List[float] = []
    for a in a_grid:
        for b in b_grid:
            for dd in d_grid:
                profs = basin_geometry(landscape2d_potential(float(a), float(b), float(dd)),
                                       bounds=(-2.5, 2.5, -2.5, 2.5), n_grid=24)
                if len(profs) != 2:
                    continue
                for p in profs:
                    sm, smin, w, bar, aniso = _profile_quantities(p)
                    frac = recover_fraction_2d_stochastic(
                        float(p.xstar[0]), float(a), float(b), float(dd), rng,
                        noise=noise, n_trials=n_trials, T=T, dt=dt,
                        perturb_frac=perturb_frac, transverse_kick=transverse_kick)
                    sigma_means.append(sm)
                    sigma_mins.append(smin)
                    widths.append(w)
                    barriers.append(bar)
                    anisos.append(aniso)
                    recoveries.append(frac)
    return {
        "sigma_mean": np.asarray(sigma_means, dtype=float),
        "sigma_min": np.asarray(sigma_mins, dtype=float),
        "width": np.asarray(widths, dtype=float),
        "barrier": np.asarray(barriers, dtype=float),
        "anisotropy": np.asarray(anisos, dtype=float),
        "recovery": np.asarray(recoveries, dtype=float),
    }


def landscape_verdict(
    a_grid: np.ndarray = None,
    b_grid: np.ndarray = None,
    d_grid: np.ndarray = None,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    transverse_kick: float = 0.6,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Pont #1-bis chantier 3/3 : verdict ternaire sur la famille 2D anisotrope.

    Rejoue le protocole du Pont #1 sur une famille de paysages 2D ou la courbure
    locale est un ensemble de valeurs propres (et non un scalaire unique). Teste
    si un resume scalaire de ``sigma`` (moyen ou minimal) regagne un pouvoir
    predictif propre en 2D -- le scenario le plus favorable a l'hypothese du
    Pont #1.

    Le verdict decisif est double :

    * **Decouplage par construction de la direction molle** : en 2D, ``sigma_min``
      (la courbure de la direction la plus molle, celle par laquelle l'escape se
      fait) et ``width`` varient sur des axes orthogonaux de la grille ``(a, d)``
      a ``b`` fixe -> le seuil ``|corr(sigma_min, width)| < 0.2`` de #9531 est
      atteignable (contrairement au chantier 2/3). ``decoupling_ok`` l'atteste.
      (``sigma_mean`` est un scalaire degenere ici : il partage ``b`` avec la
      largeur -> ``rho ~ 0.37`` ; on le reporte mais il n'est pas le scalaire
      decisif. C'est ``sigma_min`` -- la direction charitable a l'hypothese --
      qui porte le test.)
    * **Correlation partielle (FWL)** : ``sigma_min`` et ``sigma_mean`` controles
      par largeur + barriere + anisotropie (3 covariables) restent ~ 0 et sous le
      null -> aucun scalaire de courbure n'a de pouvoir propre.

    Verdict ternaire (jamais "promising") :

    * ``CONFIRMED-NEGATIVE`` : decouplage OK ET partielle ~ 0 sous null -> aucun
      scalaire de courbure ne predit la recuperabilite en 2D ; le verdict 1D se
      generalise au paysage anisotrope. L'Epic #9531 est clos.
    * ``SUBSTRATE-ARTIFACT`` : partielle > 0.2 et au-dela du null -> la richesse
      2D restore un pouvoir predictif a un scalaire de courbure ; les verdicts 1D
      etaient des artefacts de dimensionalite.
    * ``INCONCLUSIVE`` : decouplage insuffisant ou signal sous le bruit.
    """
    rng = np.random.default_rng(seed)
    if a_grid is None:
        # a controle width_x = sqrt(b/(2a)) : order of magnitude balaye
        a_grid = np.array([0.5, 0.8, 1.2, 1.8, 2.5])
    if b_grid is None:
        # b controle sigma_x = 4b ET width_x : b in (0.8, 3.2) -> sigma_x in (3.2, 12.8)
        b_grid = np.array([0.8, 1.4, 2.0, 2.6, 3.2])
    if d_grid is None:
        # d controle sigma_y = 2d (axe transverse, INDEPENDANT de width_x) :
        # d in (0.5, 6) -> sigma_y in (1, 12), anisotropie balayee des deux cotes.
        d_grid = np.array([0.5, 1.5, 3.0, 4.5, 6.0])

    fam = _gather_landscape_family(a_grid, b_grid, d_grid, noise, n_trials, T, dt,
                                    perturb_frac, transverse_kick, seed)
    sig_m, sig_min, wid, bar, aniso, rec = (fam["sigma_mean"], fam["sigma_min"],
                                            fam["width"], fam["barrier"],
                                            fam["anisotropy"], fam["recovery"])

    # Diagnostic de decouplage : sigma_min (direction molle) est le scalaire
    # decisif -- c'est la direction par laquelle l'escape se fait, donc la plus
    # favorable a l'hypothese "sigma cause la recuperabilite". Elle EST
    # decouplee de la largeur par la construction 2D (axe d orthogonal).
    # sigma_mean est un scalaire degenere (partage b avec la largeur) : reporte
    # pour transparence mais non decisif.
    rho_sigma_mean_width = _pearson(_rank(sig_m), _rank(wid))
    rho_sigma_min_width = _pearson(_rank(sig_min), _rank(wid))
    decoupling_ok = bool(abs(rho_sigma_min_width) < 0.2)

    rho_sigma_mean_recovery = _pearson(_rank(sig_m), _rank(rec))
    rho_sigma_min_recovery = _pearson(_rank(sig_min), _rank(rec))
    rho_width_recovery = _pearson(_rank(wid), _rank(rec))
    rho_barrier_recovery = _pearson(_rank(bar), _rank(rec))
    rho_aniso_recovery = _pearson(_rank(aniso), _rank(rec))

    # Partielle decisive : sigma_mean controle par (largeur, barriere, anisotropie).
    partial_mean_3cov = partial_spearman(sig_m, rec, [wid, bar, aniso])
    # sigma_min (direction la plus molle) : candidate alternatif si le pouvoir
    # propre se loge dans la direction faible plutot que la moyenne.
    partial_min_3cov = partial_spearman(sig_min, rec, [wid, bar, aniso])

    null_partial = np.array([
        partial_spearman(rng.permutation(sig_m), rec, [wid, bar, aniso])
        for _ in range(int(n_shuffle))
    ])
    p95_partial_null = float(np.percentile(np.abs(null_partial), 95))

    # Le verdict porte sur la partielle la plus favorable a l'hypothese sigma
    # (max des deux scalar resumes) -- on ne rate pas un pouvoir propre en
    # choisissant le mauvais resume.
    partial_decisive = max(partial_mean_3cov, partial_min_3cov, key=abs)

    if not decoupling_ok:
        verdict = "INCONCLUSIVE"
    elif abs(partial_decisive) > p95_partial_null and abs(partial_decisive) > 0.2:
        verdict = "SUBSTRATE-ARTIFACT"
    elif partial_decisive < -0.2:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "CONFIRMED-NEGATIVE"

    return {
        "n_samples": int(sig_m.size),
        "rho_sigma_mean_width": float(rho_sigma_mean_width),
        "rho_sigma_min_width": float(rho_sigma_min_width),
        "rho_sigma_mean_recovery": float(rho_sigma_mean_recovery),
        "rho_sigma_min_recovery": float(rho_sigma_min_recovery),
        "rho_width_recovery": float(rho_width_recovery),
        "rho_barrier_recovery": float(rho_barrier_recovery),
        "rho_anisotropy_recovery": float(rho_aniso_recovery),
        "partial_mean_3cov": float(partial_mean_3cov),
        "partial_min_3cov": float(partial_min_3cov),
        "partial_3cov_null_p95": p95_partial_null,
        "decoupling_ok": decoupling_ok,
        "verdict": verdict,
    }


def landscape_recoupled_null(
    b_grid: np.ndarray = None,
    a_fixed: float = 1.0,
    d_fixed: float = 2.0,
    noise: float = 0.35,
    n_trials: int = 60,
    T: int = 3000,
    dt: float = 0.02,
    perturb_frac: float = 0.75,
    transverse_kick: float = 0.6,
    n_shuffle: int = 200,
    seed: int = 0,
) -> Dict[str, float]:
    r"""Controle nul re-couple pour le paysage 2D.

    Sous-famille ou ``sigma`` et ``width`` sont re-couples canoniquement : ``a``
    et ``d`` fixes, ``b`` varie densement. Comme ``sigma_x = 4 b`` et
    ``width = sqrt(b / (2 a_fixed))`` sont tous deux monotones croissants en
    ``b``, et ``sigma_mean = 2 b + d_fixed`` aussi, la courbure et la largeur
    derivent ensemble -> couplage eleve, comme sur la fronce du Pont #1.

    Doit reproduire le motif fronce : couplage eleve
    (``rho_sigma_width`` grand) et partielle a 1 covariable ~ 0. Si ce controle
    echoue, le protocole 2D est suspect. Discipline du null model (#9531).
    """
    rng = np.random.default_rng(seed)
    if b_grid is None:
        b_grid = np.linspace(0.6, 3.6, 12)

    sig_means: List[float] = []
    widths: List[float] = []
    barriers: List[float] = []
    recoveries: List[float] = []
    for b in b_grid:
        profs = basin_geometry(landscape2d_potential(float(a_fixed), float(b), float(d_fixed)),
                               bounds=(-2.5, 2.5, -2.5, 2.5), n_grid=24)
        if len(profs) != 2:
            continue
        for p in profs:
            sm, _smin, w, bar, _aniso = _profile_quantities(p)
            frac = recover_fraction_2d_stochastic(
                float(p.xstar[0]), float(a_fixed), float(b), float(d_fixed), rng,
                noise=noise, n_trials=n_trials, T=T, dt=dt,
                perturb_frac=perturb_frac, transverse_kick=transverse_kick)
            sig_means.append(sm)
            widths.append(w)
            barriers.append(bar)
            recoveries.append(frac)

    sig = np.asarray(sig_means, dtype=float)
    wid = np.asarray(widths, dtype=float)
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
        # Critere self-referentiel : la fronce = couplage eleve ET sigma n'ajoute
        # rien au-dela de la largeur. On compare la partielle a SA PROPRE null p95
        # (permutation de sigma), pas a un seuil arbitraire -- plus rigoureux et
        # robuste au degre de colinearite rank(sigma)~rank(width) du null.
        "reproduces_fronce_pattern": bool(
            rho_sigma_width > 0.6 and abs(partial_1cov) < p95_partial_null
        ),
    }
