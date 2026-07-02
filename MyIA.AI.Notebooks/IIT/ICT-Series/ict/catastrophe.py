"""Grammaire des catastrophes elementaires (squelette morphodynamique mesure).

Outille le notebook **ICT-10**, le *prelude Thom* de la serie ICT. Le substrat
est la catastrophe **fronce** (*cusp*) de Rene Thom (*Esquisse d'une
semiophysique*, 1991 ; *Stabilite structurelle et morphogenese*, 1972) — la
catastrophe elementaire a **deux parametres de controle**, potentiel :

    V(x ; a, b) = x^4 / 4  +  a x^2 / 2  +  b x

dont la dynamique gradient ``dx/dt = -dV/dx = -(x^3 + a x + b)`` a pour
equilibres les racines reelles du cubique ``x^3 + a x + b = 0``. C'est le
**modele canonique** de Thom, pas un potentiel-jouet : dans la region
``4 a^3 + 27 b^2 < 0`` (donc ``a < 0``) le cubique a **trois** racines reelles
— deux minima stables separes par un col instable, soit **deux actants** au sens
de Thom (deux formes co-existantes, chacune un bassin). Ailleurs il n'en a
**qu'une**. La courbe de bifurcation ``4 a^3 + 27 b^2 = 0`` (parabole
semi-cubique, le *bord du pli*) est le lieu ou un minimum et le col **fusionnent
et disparaissent** : un **pli** (*fold*), la transition qualitative generique.

Deux fils, tresses dans ICT-10 :

* **Le metatheoreme de Thom (Ch. 3, « l'obstacle comme source de l'ontologie »).**
  La non-linearite ``x^3`` est l'*obstacle* qui engendre la multiplicite des
  bassins ; le long d'un chemin generique dans le plan ``(a, b)``, le **nombre
  d'equilibres ne change qu'aux plis**, par naissance/disparition d'une paire
  (min + col). C'est exactement le ralentissement critique mesure en **ICT-8**
  (valeur propre -> 0 au pli) : ICT-10 *rend explicite* le squelette catastrophique
  de ce qu'ICT-8 mesurait deja.
* **Le lacet de predation (Ch. 4), scene actantielle canonique.** Un cycle
  d'hysteresis a ``a < 0`` fixe traverse **deux** plis — interpretes par Thom
  comme la **catastrophe de perception** (J) et la **catastrophe de capture** (K)
  entre deux actants (proie / predateur). Le saut est mesure : l'equilibre suivi
  est *discontinu* a J et a K, et l'aire du lacet ne s'annule que hors region
  bistable.

Y est adjoint le **representant interne** ``p_hat`` (Thom, lacet de predation :
« la proie a un representant interne dans l'etat metabolique du predateur, qui
*anticipe* la proie reelle ») : un estimateur interne minimal dont on **mesure**
le contenu predictif (correlation croisee a decalage positif). C'est l'observable
honnete d'une proto-representation — le pont, sous caveat explicite, vers les
strates ulterieures (agents, features de SAE).

Numpy uniquement (racines via ``numpy.roots``), comme le reste du package leger
``ict``.
"""

from __future__ import annotations

from typing import List, Optional, Tuple

import numpy as np

# --------------------------------------------------------------------------- #
#  Catastrophe fronce (cusp) : potentiel, force, equilibres                    #
# --------------------------------------------------------------------------- #


def cusp_potential(x, a: float, b: float):
    """Potentiel de la fronce ``V(x) = x^4/4 + a x^2/2 + b x``."""
    x = np.asarray(x, dtype=float)
    return x ** 4 / 4.0 + a * x ** 2 / 2.0 + b * x


def cusp_force(x, a: float, b: float):
    """Champ de vitesse gradient ``dx/dt = -dV/dx = -(x^3 + a x + b)``."""
    x = np.asarray(x, dtype=float)
    return -(x ** 3 + a * x + b)


def cusp_curvature(x, a: float):
    """Courbure ``V''(x) = 3 x^2 + a`` (> 0 => minimum stable, < 0 => col)."""
    x = np.asarray(x, dtype=float)
    return 3.0 * x * x + a


def cusp_equilibria(a: float, b: float) -> List[Tuple[float, bool]]:
    """Equilibres ``(x*, stable)`` : racines reelles de ``x^3 + a x + b = 0``.

    Stable ssi ``V''(x*) = 3 x*^2 + a > 0`` (minimum du potentiel). Trie par
    ``x`` croissant.
    """
    roots = np.roots([1.0, 0.0, float(a), float(b)])
    real = sorted(float(r.real) for r in roots if abs(r.imag) < 1e-9)
    return [(x, bool(cusp_curvature(x, a) > 0.0)) for x in real]


def cusp_discriminant(a: float, b: float) -> float:
    """Discriminant ``Delta = -(4 a^3 + 27 b^2)`` du cubique reduit.

    ``Delta > 0`` => trois racines reelles distinctes (region **bistable**) ;
    ``Delta < 0`` => une seule racine reelle ; ``Delta = 0`` => sur le pli.
    """
    return -(4.0 * a ** 3 + 27.0 * b ** 2)


def in_bistable_region(a: float, b: float) -> bool:
    """Vrai si ``(a, b)`` est dans la region a trois equilibres (deux minima)."""
    return cusp_discriminant(a, b) > 0.0


def count_equilibria(a: float, b: float) -> int:
    """Nombre d'equilibres reels (1 hors region bistable, 3 dedans)."""
    return len(cusp_equilibria(a, b))


def count_stable(a: float, b: float) -> int:
    """Nombre de minima stables (1 ou 2)."""
    return sum(1 for _, st in cusp_equilibria(a, b) if st)


def fold_lines(a: float) -> Optional[Tuple[float, float]]:
    """Les deux ``b`` de pli a ``a`` fixe : ``b = +/- sqrt(-4 a^3 / 27)``.

    Renvoie ``None`` si ``a >= 0`` (pas de region bistable, pas de pli).
    """
    if a >= 0.0:
        return None
    b = float(np.sqrt(-4.0 * a ** 3 / 27.0))
    return (-b, b)


def bifurcation_curve(a_grid) -> Tuple[np.ndarray, np.ndarray]:
    """Branches ``(b_inf, b_sup)`` de la courbe de bifurcation sur ``a_grid``.

    Pour ``a < 0`` : ``b = +/- sqrt(-4 a^3 / 27)`` ; ``NaN`` pour ``a >= 0``.
    Pratique pour tracer la parabole semi-cubique (le « bec » de la fronce).
    """
    a = np.asarray(a_grid, dtype=float)
    with np.errstate(invalid="ignore"):
        b = np.sqrt(np.where(a < 0.0, -4.0 * a ** 3 / 27.0, np.nan))
    return -b, b


# --------------------------------------------------------------------------- #
#  Relaxation gradient et lacet d'hysteresis (le lacet de predation)           #
# --------------------------------------------------------------------------- #


def relax_to_equilibrium(
    x0: float, a: float, b: float, dt: float = 0.01, steps: int = 5000
) -> float:
    """Descente de gradient ``dx/dt = -(x^3 + a x + b)`` depuis ``x0``.

    Converge vers le minimum du **bassin** contenant ``x0`` (Euler explicite).
    """
    x = float(x0)
    for _ in range(int(steps)):
        x = x + dt * float(cusp_force(x, a, b))
    return x


def hysteresis_loop(
    a: float,
    b_values: np.ndarray,
    x_start: Optional[float] = None,
    dt: float = 0.01,
    relax_steps: int = 400,
) -> np.ndarray:
    """Suit **adiabatiquement** le minimum quand ``b`` parcourt ``b_values``.

    Pour ``a < 0``, faire varier ``b`` vers le haut puis vers le bas
    (``b_values`` aller-retour) produit le **lacet d'hysteresis** : le systeme
    reste sur sa branche jusqu'a ce qu'elle disparaisse a un pli, ou il **saute**
    (catastrophe). C'est le *lacet de predation* de Thom — deux sauts, deux
    catastrophes (perception J, capture K). Renvoie ``x`` suivi le long de
    ``b_values`` (l'etat est reporte d'un pas au suivant : memoire de branche).
    """
    b_values = np.asarray(b_values, dtype=float)
    x = float(x_start) if x_start is not None else float(
        cusp_equilibria(a, float(b_values[0]))[0][0]
    )
    xs = np.empty(b_values.shape[0], dtype=float)
    for i, b in enumerate(b_values):
        x = relax_to_equilibrium(x, a, float(b), dt=dt, steps=relax_steps)
        xs[i] = x
    return xs


def loop_jumps(b_values: np.ndarray, xs: np.ndarray, threshold: float = 0.5) -> List[int]:
    """Indices ou ``xs`` saute de plus de ``threshold`` entre deux pas.

    Localise les **catastrophes** (sauts de branche) le long d'un lacet
    d'hysteresis. Un lacet de predation bien pose en compte **deux** (J et K).
    """
    xs = np.asarray(xs, dtype=float)
    jumps = np.abs(np.diff(xs))
    return [int(i + 1) for i in np.where(jumps > threshold)[0]]


# --------------------------------------------------------------------------- #
#  Representant interne p_hat : la proto-representation, mesuree               #
# --------------------------------------------------------------------------- #


def constant_velocity_tracker(
    observation: np.ndarray, lead: int = 1, alpha: float = 0.25
) -> np.ndarray:
    """Estimateur interne **anticipateur** ``p_hat`` (extrapolation a vitesse).

    Modele interne a vitesse constante qui **projette** la proie ``lead`` pas
    dans le futur : ``p_hat[t] = obs[t] + lead * v[t]``, ou ``v`` est la vitesse
    estimee par **moyenne mobile exponentielle** des differences premieres,
    ``v[t] = alpha * (obs[t] - obs[t-1]) + (1 - alpha) * v[t-1]``. C'est le
    *representant interne* de Thom — il vise non pas ou la proie *est*, mais ou
    elle *sera*.

    Le lissage ``alpha`` n'est pas cosmetique : la vitesse **brute**
    (``alpha = 1``) amplifie le bruit d'observation d'un facteur ``lead`` et
    *degrade* l'anticipation en milieu bruite (compromis biais-variance, a
    mesurer). ``alpha`` plus petit echange de la reactivite contre de la
    robustesse. Renvoie ``p_hat`` aligne sur ``observation``.
    """
    obs = np.asarray(observation, dtype=float)
    alpha = float(alpha)
    vel = np.zeros_like(obs)
    for k in range(1, obs.shape[0]):
        vel[k] = alpha * (obs[k] - obs[k - 1]) + (1.0 - alpha) * vel[k - 1]
    return obs + float(lead) * vel


def persistence_tracker(observation: np.ndarray) -> np.ndarray:
    """Estimateur **sans modele** (persistance) : ``p_hat[t] = obs[t-1]``.

    Le temoin honnete : il **suit** la proie (retard d'un pas) au lieu de
    l'anticiper. Sert de baseline pour crediter le contenu predictif du modele.
    """
    obs = np.asarray(observation, dtype=float)
    out = np.empty_like(obs)
    out[0] = obs[0]
    out[1:] = obs[:-1]
    return out


def moving_average_tracker(observation: np.ndarray, window: int = 5, lead: int = 1) -> np.ndarray:
    """Estimateur **moyenne mobile** : ``p_hat[t] = mean(obs[t-w+1 : t+1])``.

    Baseline de lissage sans modele de tendance. Pour ``lead > 0`` on extrapole
    en deplacement la moyenne mobile d'un pas, comme un *dead-reckoning* sur
    la valeur moyenne. Le compromis biais-variance est pilote par ``window``
    (petite fenetre = reactif mais bruite ; grande fenetre = lisse mais
    dephase). Distinct de la persistance (qui regarde le dernier point
    seulement) et de l'AR(1) (qui modelise une dynamique lineaire).
    """
    obs = np.asarray(observation, dtype=float)
    window = max(1, int(window))
    n = obs.shape[0]
    out = np.empty_like(obs)
    csum = np.concatenate([[0.0], np.cumsum(obs)])
    for k in range(n):
        lo = max(0, k - window + 1)
        hi = k + 1
        out[k] = (csum[hi] - csum[lo]) / (hi - lo)
    if lead > 0:
        # Extrapolation dead-reckoning sur la valeur moyenne (difference
        # entre la derniere moyenne mobile et la precedente).
        diff = np.diff(out, prepend=out[0])
        out = out + float(lead) * diff
    return out


def ar1_tracker(observation: np.ndarray, lead: int = 1) -> np.ndarray:
    """Estimateur **AR(1)** : ``p_hat[t] = phi * obs[t-1] + c``.

    Baseline lineaire classique : on ajuste un modele AR(1) ``obs[t] = phi *
    obs[t-1] + c + eps`` sur les observations (OLS a 1 pas), puis on **itere**
    ``lead`` fois depuis l'amorce ``obs[-1]`` pour obtenir la prediction
    multi-pas ``p_hat[t]`` (forward, sans reutiliser les observations). Le
    scalaire projete est **aligne** sur toute la trajectoire : on reporte
    cette prediction constante comme l'horizon de reference de la baseline.

    Le coefficient ``phi`` est appris par regression sur toute la trajectoire,
    ce qui distingue cette baseline de la persistance (``phi = 1, c = 0``)
    et du modele a vitesse constante ``p_hat = obs + lead * v`` (qui extrapole
    lineairement a partir de la derive recente).
    """
    obs = np.asarray(observation, dtype=float)
    if obs.shape[0] < 3:
        return np.full_like(obs, float(obs[-1]))
    y = obs[1:]
    x = obs[:-1]
    x_mean = float(x.mean())
    y_mean = float(y.mean())
    var_x = float(np.mean((x - x_mean) ** 2))
    if var_x < 1e-12:
        return np.full_like(obs, y_mean)
    phi = float(np.mean((x - x_mean) * (y - y_mean)) / var_x)
    c = y_mean - phi * x_mean
    # Projection multi-pas iterative (forward sans observation), amorce sur
    # la derniere observation.
    projected = float(obs[-1])
    for _ in range(int(lead)):
        projected = phi * projected + c
    # Le modele AR(1) fournit un scalaire de prediction a horizon ``lead``.
    # On l'aligne sur toute la trajectoire (la baseline "voit" ce scalaire
    # constant comme son estimation pour chaque pas).
    return np.full_like(obs, projected)


def cross_correlation(p_hat: np.ndarray, target: np.ndarray, max_lag: int = 12):
    """Correlation croisee normalisee entre ``p_hat[t]`` et ``target[t + lag]``.

    Renvoie ``(lags, corr)`` pour ``lag`` dans ``[-max_lag, +max_lag]``. Un
    estimateur **anticipateur** a son pic a un **lag positif** (il correle avec
    le *futur* de la cible) ; un suiveur, a un lag <= 0. Le **lag du pic** est la
    mesure operationnelle de l'anticipation.
    """
    p = np.asarray(p_hat, dtype=float)
    t = np.asarray(target, dtype=float)
    p = (p - p.mean()) / (p.std() + 1e-12)
    t = (t - t.mean()) / (t.std() + 1e-12)
    n = p.shape[0]
    lags = np.arange(-int(max_lag), int(max_lag) + 1)
    corr = np.empty(lags.shape[0], dtype=float)
    for i, lag in enumerate(lags):
        if lag >= 0:
            a, b = p[: n - lag], t[lag:]
        else:
            a, b = p[-lag:], t[: n + lag]
        corr[i] = float(np.mean(a * b)) if a.size else 0.0
    return lags, corr


def peak_lag(lags: np.ndarray, corr: np.ndarray) -> int:
    """Lag du maximum de correlation (l'horizon d'anticipation mesure)."""
    return int(np.asarray(lags)[int(np.argmax(np.asarray(corr)))])


def lead_error(p_hat: np.ndarray, target: np.ndarray, lead: int) -> float:
    """Erreur quadratique moyenne de ``p_hat[t]`` contre ``target[t + lead]``.

    Mesure *combien* le representant interne anticipe juste : un anticipateur
    correct doit battre la persistance sur cet horizon ``lead``.
    """
    p = np.asarray(p_hat, dtype=float)
    t = np.asarray(target, dtype=float)
    if lead <= 0:
        return float(np.mean((p - t) ** 2))
    return float(np.mean((p[:-lead] - t[lead:]) ** 2))
