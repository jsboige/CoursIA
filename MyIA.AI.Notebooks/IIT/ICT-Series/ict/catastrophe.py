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

Une derniere section (``#19333-G``) ajoute le **pont cusp <-> trefle** demande par
la distillation #19333-G.alpha : la courbe de bifurcation ``4 a^3 + 27 b^2 = 0``
tracee ici est la **cubique cuspidale**, que l'article de hidden-phenomena
(Michael & Kenta, 2026-10-03, https://hidden-phenomena.com/articles/trefoil)
identifie a un **noeud de trefle** releve en polaires sur le tore (``2 phi = 3
theta``). La section mesure les invariants du noeud torique ``(2, n)`` (nombres
d'enroulement, polynome d'Alexander) et fournit le trace 3D.

Numpy uniquement (racines via ``numpy.roots``), comme le reste du package leger
``ict``. Le seul point de contact avec matplotlib est le trace
(``cusp_polar_plot``, ``torus_surface``) : l'import y est **paresseux**, fait
dans le corps des fonctions -- ``import ict.catastrophe`` reste donc numpy-only.
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

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


# --------------------------------------------------------------------------- #
#  Durcissement de p_hat (cran 10.1, #4588) : familles de trajectoires,       #
#  baselines adverses, banc de mesure aux deux metriques separees             #
# --------------------------------------------------------------------------- #


def moving_average_tracker(observation: np.ndarray, window: int = 5) -> np.ndarray:
    """Baseline **lissage** : moyenne mobile causale sur ``window`` points.

    Ne regarde que le passe (``obs[t-window+1 .. t]``) : elle debruite mais
    **retarde** — sur une rampe, elle est systematiquement en dessous. Sert
    d'adversaire « lisse » a ``p_hat`` : si l'anticipation ne bat pas un simple
    lissage, elle n'apporte rien.
    """
    obs = np.asarray(observation, dtype=float)
    w = int(window)
    out = np.empty_like(obs)
    for k in range(obs.shape[0]):
        lo = max(0, k - w + 1)
        out[k] = float(obs[lo : k + 1].mean())
    return out


def ar1_coefficient(observation: np.ndarray) -> float:
    """Coefficient AR(1) ``phi`` ajuste par moindres carres sur la serie centree.

    ``phi = <x[t] x[t-1]> / <x[t-1]^2>`` avec ``x = obs - mean(obs)``. C'est
    l'estimateur Yule-Walker au premier ordre.
    """
    obs = np.asarray(observation, dtype=float)
    x = obs - obs.mean()
    num = float(np.dot(x[1:], x[:-1]))
    den = float(np.dot(x[:-1], x[:-1])) + 1e-12
    return num / den


def ar1_tracker(observation: np.ndarray, lead: int = 1) -> np.ndarray:
    """Baseline **autoregressive** : prediction AR(1) a l'horizon ``lead``.

    ``p_hat[t] = mu + phi^lead * (obs[t] - mu)`` — retour geometrique vers la
    moyenne. ``phi`` est ajuste **in-sample sur la serie complete** : la
    baseline voit des donnees que ``p_hat`` ne voit pas, elle est donc
    volontairement *avantagee* (adversaire severe, pas homme de paille).
    """
    obs = np.asarray(observation, dtype=float)
    mu = float(obs.mean())
    phi = ar1_coefficient(obs)
    return mu + (phi ** int(lead)) * (obs - mu)


def prey_trajectory(
    kind: str,
    n_steps: int = 300,
    noise: float = 0.10,
    rng: Optional[np.random.Generator] = None,
    drift: float = 0.02,
) -> np.ndarray:
    """Trois familles de trajectoires de proie, aux cinematiques opposees.

    * ``"sinus"``   — periodique lisse bruitee : **inertie exploitable** par une
      extrapolation de vitesse (le regime du claim initial d'ICT-10).
    * ``"derive"``  — marche aleatoire a derive ``drift`` : l'increment est du
      bruit, la « vitesse » estimee n'est que du bruit amplifie.
    * ``"creneau"`` — onde carree bruitee (rebond) : discontinuites que nulle
      extrapolation de vitesse ne peut anticiper (la vitesse EMA sur-reagit au
      saut et depasse la cible).

    Un banc honnete doit croiser les trois : un seul regime ne peut crediter
    l'anticipation *en general* (gate du cran 10.1, #4588).
    """
    if rng is None:
        rng = np.random.default_rng(7)
    n = int(n_steps)
    t = np.linspace(0.0, 8.0 * np.pi, n)
    if kind == "sinus":
        return np.sin(t) + noise * rng.standard_normal(n)
    if kind == "derive":
        return np.cumsum(drift + noise * rng.standard_normal(n))
    if kind == "creneau":
        return np.sign(np.sin(t / 2.0)) + noise * rng.standard_normal(n)
    raise ValueError(f"famille de trajectoire inconnue : {kind!r}")


def anticipation_report(
    observation: np.ndarray,
    lead: int = 4,
    alpha: float = 0.25,
    window: int = 5,
    max_lag: int = 10,
) -> Dict[str, Dict[str, float]]:
    """Banc de mesure de l'anticipation : ``p_hat`` contre 3 baselines adverses.

    Pour chaque estimateur (``p_hat``, ``persistance``, ``moyenne_mobile``,
    ``ar1``), renvoie les **deux metriques separees** que le recit initial
    fusionnait : ``erreur`` (quadratique moyenne a l'horizon ``lead``) et
    ``pic_lag`` (lag du pic de correlation croisee). Elles peuvent **diverger**
    — un pic de lag flatteur avec une erreur pire est exactement le fantome
    statistique que la serie s'engage a debusquer. A reporter **par famille**
    de trajectoire, jamais agrege (gates du cran 10.1, #4588).
    """
    obs = np.asarray(observation, dtype=float)
    estimateurs = {
        "p_hat": constant_velocity_tracker(obs, lead=lead, alpha=alpha),
        "persistance": persistence_tracker(obs),
        "moyenne_mobile": moving_average_tracker(obs, window=window),
        "ar1": ar1_tracker(obs, lead=lead),
    }
    rapport: Dict[str, Dict[str, float]] = {}
    for nom, est in estimateurs.items():
        lags, corr = cross_correlation(est, obs, max_lag=max_lag)
        rapport[nom] = {
            "erreur": lead_error(est, obs, lead),
            "pic_lag": peak_lag(lags, corr),
        }
    return rapport


# --------------------------------------------------------------------------- #
#  Pont cusp <-> trefle (#19333-G) : la cubique cuspidale en polaires sur le   #
#  tore, et les noeuds toriques (2, n)                                        #
# --------------------------------------------------------------------------- #
#
# Le pont lui-meme est *cite*, jamais re-derive : l'article de hidden-phenomena
# (Michael & Kenta, 2026-10-03, https://hidden-phenomena.com/articles/trefoil)
# identifie la **cubique cuspidale** ``y^2 = x^3`` -- qui EST la courbe de
# bifurcation de la fronce, ``4 a^3 + 27 b^2 = 0``, tracee par
# ``bifurcation_curve`` ci-dessus -- a un **noeud de trefle** releve en polaires
# sur le tore. Figures non reproduites ; renvoi.
#
# Ce que ce module *mesure*, en revanche, ne depend d'aucun article : les
# nombres d'enroulement d'une courbe fermee sur le tore, et le polynome
# d'Alexander du noeud torique ``(2, n)`` -- ce dernier etant exactement l'objet
# du theoreme ``alexander_trefoil`` de ``knot_lean`` (``X^2 - X + 1`` pour le
# trefle). Le temoin negatif est le meme calcul pour ``n = 5`` (cinquefoil).


def torus_points(theta, phi, R: float = 2.0, r: float = 1.0):
    """Plongement du tore dans ``R^3`` : ``(theta, phi) -> (x, y, z)``.

    ``theta`` est l'angle tournant autour de l'axe du tore (le grand cercle de
    rayon ``R``), ``phi`` l'angle tournant dans le tube (le petit cercle de rayon
    ``r``) ::

        x = (R + r cos phi) cos theta
        y = (R + r cos phi) sin theta
        z = r sin phi

    Renvoie ``(x, y, z)`` de la meme forme que ``theta`` (tout tableau numpy
    diffusable). C'est le seul releve utilise par tout le reste de la section :
    une courbe sur le tore n'est rien d'autre qu'un couple ``(theta, phi)``.
    """
    th = np.asarray(theta, dtype=float)
    ph = np.asarray(phi, dtype=float)
    rho = R + r * np.cos(ph)
    return rho * np.cos(th), rho * np.sin(th), r * np.sin(ph)


def torus_knot(n: int, points: int = 2000, turns: int = 2):
    """Courbe ``(theta, phi)`` du noeud torique ``(2, n)`` : ``2 phi = n theta``.

    Le noeud torique ``(p, q)`` est l'image d'une droite de pente ``q/p`` sur le
    tore ; pour ``p = 2`` la relation s'ecrit ``2 phi = n theta``. Le trefle est
    le cas ``n = 3`` ; ``n = 5`` donne le cinquefoil (temoin negatif).

    Le domaine ``theta in [0, turns * 2 pi]`` avec ``turns = 2`` est le plus
    petit qui referme la courbe pour ``n`` impair : ``theta`` s'enroule 2 fois,
    ``phi`` s'enroule ``n`` fois. Renvoie ``(theta, phi)``, deux tableaux 1-D.
    """
    theta = np.linspace(0.0, float(turns) * 2.0 * np.pi, int(points))
    return theta, 0.5 * float(n) * theta


def torus_knot_winding(theta, phi) -> Tuple[int, int]:
    """Nombres d'enroulement ``(w_theta, w_phi)`` **mesures** sur la courbe.

    ``w = arrondi( (angle_final - angle_initial) / 2 pi )`` sur chaque angle.
    C'est un invariant *mesure*, pas declare : le trefle ``2 phi = 3 theta``
    doit rendre ``(2, 3)``, le cinquefoil ``(2, 5)``. Deux courbes dont les
    paires different ne sont pas le meme noeud -- c'est ce que le temoin negatif
    de la section exploite.
    """
    th = np.asarray(theta, dtype=float)
    ph = np.asarray(phi, dtype=float)
    return (
        int(round(float(th[-1] - th[0]) / (2.0 * np.pi))),
        int(round(float(ph[-1] - ph[0]) / (2.0 * np.pi))),
    )


def alexander_torus_knot(n: int) -> np.ndarray:
    """Coefficients du polynome d'Alexander du noeud torique ``(2, n)``.

    ``Delta(t) = (t^n + 1) / (t + 1) = t^(n-1) - t^(n-2) + ... + 1`` pour ``n``
    impair, soit ``coefficients[k] = (-1)^(n-1-k)`` en **degre croissant**
    (``coefficients[0]`` est le terme constant).

    Pour le trefle (``n = 3``) cela donne ``[1, -1, 1]``, soit ``t^2 - t + 1``
    -- exactement la valeur que ``knot_lean`` prouve dans ``alexander_trefoil``
    (``Knots/Conway.lean``). La fonction ne calcule pas la valeur : elle la
    **reconstruit par la formule du noeud torique**, ce qui en fait un controle
    croise independant du cote Python (tests et notebook).
    """
    n = int(n)
    if n < 1:
        raise ValueError(f"n doit etre >= 1, recu {n!r}")
    return np.array([(-1.0) ** (n - 1 - k) for k in range(n)], dtype=float)


def alexander_roots_torus_knot(n: int):
    """Racines complexes du polynome d'Alexander du noeud torique ``(2, n)``.

    Ce sont les **racines ``2n``-iemes primitives de l'unite** : pour le trefle
    (``n = 3``), la paire conjuguee ``exp(+/- i pi / 3)`` -- les racines 6-iemes
    primitives. Le module les **calcule** (``numpy.roots`` sur les coefficients
    en degre decroissant) au lieu de les declarer : c'est la mesure qui rend le
    pont falsifiable, et elle se compare directement a ``exp(2 i pi k / 2n)``
    pour ``k`` premier avec ``2n``.
    """
    coeffs = alexander_torus_knot(n)[::-1]
    return np.roots(coeffs)


def torus_surface(ax, R: float = 2.0, r: float = 1.0, nu: int = 60, nv: int = 30, **kwargs):
    """Trace la **surface** du tore dans l'axe 3D ``ax`` (support du noeud).

    Sans la surface, une courbe « sur le tore » flotte dans le vide et le propos
    ne se lit pas. Import matplotlib **paresseux** (fait ici, pas en tete de
    module) : le module reste numpy-only a l'import. Renvoie ``ax``.
    """
    import matplotlib.pyplot as plt  # noqa: F401  (import paresseux assume)

    u = np.linspace(0.0, 2.0 * np.pi, int(nu))
    v = np.linspace(0.0, 2.0 * np.pi, int(nv))
    uu, vv = np.meshgrid(u, v)
    x, y, z = torus_points(uu, vv, R=R, r=r)
    kwargs.setdefault("alpha", 0.18)
    kwargs.setdefault("color", "0.55")
    kwargs.setdefault("linewidth", 0)
    kwargs.setdefault("antialiased", True)
    ax.plot_surface(x, y, z, **kwargs)
    return ax


def cusp_polar_plot(theta, phi, ax, R: float = 2.0, r: float = 1.0, **kwargs):
    """Trace la courbe ``(theta, phi)`` **en polaires sur le tore**, dans ``ax``.

    C'est le geste de l'article : la cubique cuspidale -- courbe de bifurcation
    de la fronce -- relevee en polaires, s'enroule sur le tore. L'argument
    ``(theta, phi)`` accepte un **meshgrid** (deux tableaux de meme forme) : 1-D
    pour une courbe (le noeud), 2-D pour une famille de courbes. Le trace est
    delegue a matplotlib, importe **paresseusement** dans le corps de la
    fonction : ``import ict.catastrophe`` reste numpy-only.

    Renvoie ``ax`` pour l'enchainement.
    """
    x, y, z = torus_points(theta, phi, R=R, r=r)
    ax.plot(x, y, z, **kwargs)
    return ax
