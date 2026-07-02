"""Champs de valence spatiaux et animats (notebook ICT-12).

Premier toy model **actantiel spatial** de la strate 3 : des animats evoluent
dans un champ de valence (source attractive + obstacles repulsifs). La scene
actantielle de Thom (ICT-10) cesse d'etre une correspondance nommee : les
**roles deviennent des grandeurs mesurees** sur trajectoires.

Deux animats, un meme environnement
------------------------------------
* **Reactif** (suivi de gradient) : le temoin. Il monte le gradient local de
  valence : il poursuit la source la ou elle *est*. C'est la version spatiale
  de la baseline ``persistance`` du Cran A (cf. :func:`ict.catastrophe.persistence_tracker`).
* **Anticipateur p_hat** : l'animat dote d'un modele interne a vitesse
  constante (generalisation 2D de :func:`ict.catastrophe.constant_velocity_tracker`).
  Il extrapole la position future de la source et vise son point d'interception
  la ou elle *sera*.

La question directrice (gate 1 de l'issue #4878) : **dans quels environnements
le modele interne paie-t-il son cout ?** Le banc croise >= 3 regimes de
cinematique de la source, dont au moins un ou p_hat **perd** contre le reactif.

Quatre grandeurs de role (gate 2)
---------------------------------
Chaque role (predateur / proie / obstacle) doit etre identifiable depuis la
trajectoire seule, via :

* :func:`capture_rate`      — cadence de capture de la source (recompense).
* :func:`escape_rate`       — cadence de sortie des regions de valence negative.
* :func:`path_irreversibility` — caractere « sans retour » : asymetrie du gain
  de valence entre le sens aller et le sens retour le long du chemin.
* :func:`role_switching`    — frequence des bascules de cap (changements de
  direction marques).

Discipline « sans complaisance » (gate 4) : les baselines adverses du Cran A
(persistance, moyenne mobile, AR(1), cf. :mod:`ict.catastrophe`) servent de
temoins pour tout claim d'anticipation 2D. Les verdicts sont **par regime,
jamais agrenes**.

numpy CPU pur, gel GPU respecte.
"""

from __future__ import annotations

from typing import Callable, Dict, List, Optional, Tuple

import numpy as np

# --------------------------------------------------------------------------- #
#  Champ de valence (source gaussienne attractive + obstacles repulsifs)       #
# --------------------------------------------------------------------------- #

_SIGMA = 6.0
_BUMP_AMP = 1.0
_OBST_AMP = 0.8
_OBST_SIGMA = 2.5


def valence_at(
    pos: np.ndarray,
    source: np.ndarray,
    obstacles: Optional[np.ndarray] = None,
    sigma: float = _SIGMA,
) -> float:
    """Valence scalaire (continue) en ``pos`` : bosse attractive en ``source``
    moins bosses repulsives en chaque obstacle. Pas de grille : evaluable en
    tout point, ce qui donne un gradient propre pour l'animat reactif."""
    p = np.asarray(pos, dtype=float)
    s = np.asarray(source, dtype=float)
    v = _BUMP_AMP * float(np.exp(-float(np.sum((p - s) ** 2)) / (2.0 * sigma ** 2)))
    if obstacles is not None and len(obstacles):
        for o in np.asarray(obstacles, dtype=float):
            v -= _OBST_AMP * float(np.exp(-float(np.sum((p - o) ** 2)) / (2.0 * _OBST_SIGMA ** 2)))
    return v


def valence_gradient(
    pos: np.ndarray,
    source: np.ndarray,
    obstacles: Optional[np.ndarray] = None,
    sigma: float = _SIGMA,
) -> np.ndarray:
    """Gradient analytique de :func:`valence_at` (derivee d'une gaussienne).
    Vecteur 2D pointant vers la source (en l'absence d'obstacles)."""
    p = np.asarray(pos, dtype=float)
    s = np.asarray(source, dtype=float)
    g = _BUMP_AMP * float(np.exp(-float(np.sum((p - s) ** 2)) / (2.0 * sigma ** 2))) * (
        (s - p) / (sigma ** 2)
    )
    if obstacles is not None and len(obstacles):
        for o in np.asarray(obstacles, dtype=float):
            e = _OBST_AMP * float(np.exp(-float(np.sum((p - o) ** 2)) / (2.0 * _OBST_SIGMA ** 2)))
            g += e * ((p - o) / (_OBST_SIGMA ** 2))  # repousse : gradient sortant
    return g


def valence_grid(
    size: int,
    source: np.ndarray,
    obstacles: Optional[np.ndarray] = None,
    sigma: float = _SIGMA,
) -> np.ndarray:
    """Echantillonne :func:`valence_at` sur une grille ``size x size`` pour la
    visualisation (imshow). Origine en haut a gauche, comme une image.
    Vectorise par diffusion numpy (la bosse gaussienne et les obstacles sont
    evalues sur toute la grille d'un coup)."""
    s = np.asarray(source, dtype=float)
    xs = np.arange(size, dtype=float)
    yy, xx = np.meshgrid(xs, xs, indexing="ij")
    r2 = (xx - s[0]) ** 2 + (yy - s[1]) ** 2
    grid = _BUMP_AMP * np.exp(-r2 / (2.0 * sigma ** 2))
    if obstacles is not None and len(obstacles):
        for o in np.asarray(obstacles, dtype=float):
            ro2 = (xx - o[0]) ** 2 + (yy - o[1]) ** 2
            grid -= _OBST_AMP * np.exp(-ro2 / (2.0 * _OBST_SIGMA ** 2))
    return grid


# --------------------------------------------------------------------------- #
#  Cinematiques de la source (3+ regimes opposes)                              #
# --------------------------------------------------------------------------- #

def source_trajectory(
    kind: str,
    n_steps: int,
    size: int,
    rng: Optional[np.random.Generator] = None,
    speed: float = 0.8,
    noise: float = 0.25,
    reversal_p: float = 0.18,
    start: Optional[np.ndarray] = None,
) -> np.ndarray:
    """Trajectoire 2D de la source selon le regime ``kind``.

    * ``"statique"``   — source immobile au centre (jitter negligeable).
    * ``"balistique"`` — vitesse constante, rebonds sur les bords : cinematique
      **previsible**, exploitable par une extrapolation a vitesse constante.
    * ``"erratique"``  — renversements de vitesse aleatoires (``reversal_p`` par
      pas) : nulle extrapolation ne peut anticiper le rebond, la vitesse EMA
      sur-reagit. p_hat doit y perdre (gate 1).
    * ``"bruite"``     — source quasi fixe mais agitee d'un bruit de position :
      la vitesse estimee n'est que du bruit amplifie par ``lead``.

    Renvoie un tableau ``(n_steps, 2)`` des positions dans ``[0, size)``.
    """
    _KNOWN = {"statique", "balistique", "erratique", "bruite"}
    if kind not in _KNOWN:
        raise ValueError(f"regime de source inconnu : {kind!r}")
    if rng is None:
        rng = np.random.default_rng(7)
    center = np.array([size / 2.0, size / 2.0])
    if start is None:
        start = center.copy()
    traj = np.empty((n_steps, 2), dtype=float)
    pos = np.asarray(start, dtype=float).copy()
    if kind == "statique":
        vel = np.zeros(2)
    else:
        angle = float(rng.uniform(0.0, 2.0 * np.pi))
        vel = np.array([np.cos(angle), np.sin(angle)]) * speed
    for t in range(n_steps):
        if kind == "statique":
            pos = center + noise * 0.2 * rng.standard_normal(2)
        elif kind == "bruite":
            pos = center + noise * rng.standard_normal(2)
        else:  # balistique / erratique : integrer la vitesse
            if kind == "erratique" and rng.random() < reversal_p:
                vel = -vel  # demi-tour aleatoire
            pos = pos + vel
            # rebonds sur les bords
            for d in range(2):
                if pos[d] < 0.0:
                    pos[d] = -pos[d]
                    vel[d] = -vel[d]
                elif pos[d] >= size:
                    pos[d] = 2.0 * size - pos[d]
                    vel[d] = -vel[d]
        traj[t] = pos
    return traj


# --------------------------------------------------------------------------- #
#  Modele interne p_hat : extrapolation 2D a vitesse constante                #
# --------------------------------------------------------------------------- #

def predict_source(
    source_traj: np.ndarray,
    t: int,
    lead: int = 4,
    alpha: float = 0.25,
) -> np.ndarray:
    """Position future predite de la source a l'instant ``t`` : generalisation
    2D de :func:`ict.catastrophe.constant_velocity_tracker`. La vitesse est
    estimee par moyenne mobile exponentielle des differences premieres
    (lissage ``alpha``), puis extrapolee de ``lead`` pas. Sur une trajectoire
    balistique c'est exact ; sur l'erratique, la EMA sur-reagit aux rebonds."""
    obs = np.asarray(source_traj, dtype=float)
    if t <= 0:
        return obs[t].copy()
    # vitesse EMA coordinate par coordinate, sur le passe observable [0..t]
    vel = np.zeros(2)
    for k in range(1, t + 1):
        vel = alpha * (obs[k] - obs[k - 1]) + (1.0 - alpha) * vel
    return obs[t] + float(lead) * vel


# --------------------------------------------------------------------------- #
#  Animats : reactif (gradient) vs anticipateur (interception p_hat)          #
# --------------------------------------------------------------------------- #

def _clip_to_bounds(pos: np.ndarray, size: int) -> np.ndarray:
    return np.clip(pos, 0.0, float(size - 1))


def _obstacle_repulsion(pos: np.ndarray, obstacles: Optional[np.ndarray]) -> np.ndarray:
    """Vecteur de repulsion somme sur les obstacles proches (chacun pousse vers
    l'exterieur). Utilise par l'animat p_hat, qui vise une interception pure et
    ne suit donc PAS le gradient attractif — il lui faut un evitement dedie."""
    if obstacles is None or len(obstacles) == 0:
        return np.zeros(2)
    p = np.asarray(pos, dtype=float)
    r = np.zeros(2)
    for o in np.asarray(obstacles, dtype=float):
        diff = p - o
        d = float(np.linalg.norm(diff))
        if d < 1e-9:
            continue
        e = _OBST_AMP * float(np.exp(-(d ** 2) / (2.0 * _OBST_SIGMA ** 2)))
        r += e * diff / (d * _OBST_SIGMA ** 2)
    return r


def simulate_reactive(
    source_traj: np.ndarray,
    size: int,
    start: np.ndarray,
    n_steps: int,
    step: float = 0.8,
    obstacles: Optional[np.ndarray] = None,
) -> np.ndarray:
    """Animat **reactif** (suivi de gradient) : monte :func:`valence_gradient`
    a chaque pas. C'est la baseline persistance en espace — il vise ou la
    source *est*."""
    pos = np.asarray(start, dtype=float).copy()
    traj = np.empty((n_steps, 2), dtype=float)
    for t in range(n_steps):
        g = valence_gradient(pos, source_traj[t], obstacles)
        n = float(np.linalg.norm(g))
        if n > 1e-9:
            pos = pos + step * (g / n)
        traj[t] = _clip_to_bounds(pos, size)
    return traj


def simulate_phat(
    source_traj: np.ndarray,
    size: int,
    start: np.ndarray,
    n_steps: int,
    lead: int = 4,
    alpha: float = 0.25,
    step: float = 0.8,
    obstacles: Optional[np.ndarray] = None,
) -> np.ndarray:
    """Animat **anticipateur p_hat** : interception pure vers la position future
    predite de la source (:func:`predict_source`), plus evitement dedie des
    obstacles (:func:`_obstacle_repulsion`).

    Il ne suit **pas** le gradient attractif — c'est tout son propos : parier sur
    le modele interne. Sur une source balistique, la prediction est exacte et il
    intercepte en avance. Sur l'erratique, les renversements trompent la vitesse
    EMA et il vise des fantomes : il y perd (gate 1). C'est la discipline du banc
    « sans complaisance » : si l'interception pure ne bat pas le reactif (suivi de
    gradient = persistance spatiale) sur un regime, le modele interne n'y paie pas."""
    pos = np.asarray(start, dtype=float).copy()
    traj = np.empty((n_steps, 2), dtype=float)
    for t in range(n_steps):
        # lead d'interception adapte au temps de fermeture : on vise la ou la
        # source sera quand l'animat arrivera, pas un horizon fixe (qui le
        # ferait mener la source sans jamais la rencontrer).
        dist = float(np.linalg.norm(np.asarray(source_traj[t]) - pos))
        lead_meet = max(1, int(round(dist / max(step, 1e-9))))
        lead_meet = min(lead_meet, lead * 2)  # borne (evite l'instabilite lointaine)
        target = predict_source(source_traj, t, lead=lead_meet, alpha=alpha)
        desired = target - pos
        nd = float(np.linalg.norm(desired))
        desired = desired / nd if nd > 1e-9 else np.zeros(2)
        repl = _obstacle_repulsion(pos, obstacles)
        move = desired + 0.5 * repl  # interception + evitement des obstacles
        nm = float(np.linalg.norm(move))
        if nm > 1e-9:
            pos = pos + step * (move / nm)
        traj[t] = _clip_to_bounds(pos, size)
    return traj


def random_walk(
    size: int,
    start: np.ndarray,
    n_steps: int,
    step: float = 0.8,
    rng: Optional[np.random.Generator] = None,
) -> np.ndarray:
    """Marche aleatoire isotrope : **controle d'ablation** (gate 2). Sans
    modele interne ni suivi de gradient, elle ne doit porter aucune signature
    de role — c'est le temoin negatif des 4 metriques."""
    if rng is None:
        rng = np.random.default_rng(0)
    pos = np.asarray(start, dtype=float).copy()
    traj = np.empty((n_steps, 2), dtype=float)
    for t in range(n_steps):
        angle = float(rng.uniform(0.0, 2.0 * np.pi))
        pos = pos + step * np.array([np.cos(angle), np.sin(angle)])
        traj[t] = _clip_to_bounds(pos, size)
    return traj


# --------------------------------------------------------------------------- #
#  Quatre grandeurs de role (mesurees sur trajectoire)                         #
# --------------------------------------------------------------------------- #

def capture_rate(
    traj: np.ndarray,
    source_traj: np.ndarray,
    radius: float = 1.5,
    burn: int = 0,
) -> float:
    """Cadence de capture : fraction des pas ou l'animat est a moins de
    ``radius`` de la source, sur la fenetre ``[burn:]`` (burn-in exclu pour
    mesurer la **precision de poursuite** apres convergence, pas la decouverte).

    Un predateur efficace intercepte (taux eleve) ; la marche aleatoire
    n'approche la source que par hasard (taux faible)."""
    tr = np.asarray(traj)[burn:]
    src = np.asarray(source_traj)[burn:]
    d = np.linalg.norm(tr - src, axis=1)
    return float(np.mean(d <= radius))


def escape_rate(
    traj: np.ndarray,
    source_traj: np.ndarray,
    obstacles: Optional[np.ndarray] = None,
    sigma: float = _SIGMA,
    danger_r: float = 1.0,
) -> float:
    """Cadence de fuite : inverse du temps moyen passe pres d'un obstacle
    (region repulsive). Une proie qui esquive sort vite ; un animat piege y
    sejourne (taux faible). Sans obstacle, reflue vers la cadence de fuite du
    seul bord, et reste faible et comparable entre animats — on s'attend a ce
    que la marche aleatoire y perde."""
    if obstacles is None or len(obstacles) == 0:
        return 0.0
    obs = np.asarray(obstacles, dtype=float)
    tr = np.asarray(traj, dtype=float)
    # distance min de chaque position aux obstacles
    dmin = np.min(np.linalg.norm(tr[:, None, :] - obs[None, :, :], axis=2), axis=1)
    trapped = dmin <= danger_r
    if not np.any(trapped):
        return 1.0  # jamais piege : fuite parfaite
    # taux = fraction des pas hors danger
    return float(np.mean(~trapped))


def path_irreversibility(
    traj: np.ndarray,
    source_traj: np.ndarray,
    obstacles: Optional[np.ndarray] = None,
    sigma: float = _SIGMA,
) -> float:
    """Caractere « sans retour » du chemin : asymetrie du gain de valence entre
    le sens aller et le sens retour le long des memes points geometriques.

    Pour chaque pas, on compare la valence acquise en avancant (du point t au
    t+1, la source etant ou elle est a t) a celle qu'on acquerrait en
    remontant. Sur un champ statique les deux sont egales (reversible,
    irreversibilite ~ 0). Sur une source que l'animat intercepte de facon
    engagee, l'aller gagne plus que le retour — l'agence *fait un travail sans
    retour*, fil ICT-9 (cf. :func:`ict.agency.basin_return_probability`)."""
    tr = np.asarray(traj, dtype=float)
    src = np.asarray(source_traj, dtype=float)
    n = len(tr)
    if n < 2:
        return 0.0
    forward, backward = 0.0, 0.0
    for t in range(n - 1):
        vf = valence_at(tr[t + 1], src[t], obstacles, sigma)
        vb = valence_at(tr[t], src[t], obstacles, sigma)  # « retour » : rester
        forward += vf
        backward += vb
    fw = forward - backward  # gain net d'aller vers l'avant vs stagner
    scale = abs(forward) + abs(backward) + 1e-9
    return float(fw / scale)


def role_switching(traj: np.ndarray, min_turn: float = 0.5) -> float:
    """Frequence des bascules de cap : fraction des pas ou la direction fait un
    demi-tour marque (cosinus de l'angle entre vecteurs de deplacement
    successifs inferieur a ``-min_turn`` en composante dominante, ou un virage
    net > ~90 deg).

    Une proie qui esquive change souvent de cap (taux eleve) ; un predateur en
    interception engagee garde le cap (taux faible) ; la marche aleatoire est
    intermediaire mais sans structure."""
    tr = np.asarray(traj, dtype=float)
    moves = np.diff(tr, axis=0)
    if len(moves) < 2:
        return 0.0
    dots = np.einsum("ij,ij->i", moves[1:], moves[:-1])
    norms = np.linalg.norm(moves[1:], axis=1) * np.linalg.norm(moves[:-1], axis=1) + 1e-12
    cos = dots / norms
    # bascule = virage serre (cos < -min_turn => angle > ~120 deg)
    return float(np.mean(cos < -min_turn))


# --------------------------------------------------------------------------- #
#  Banc de mesure par regime (gate 1 + gate 3)                                 #
# --------------------------------------------------------------------------- #

def regime_report(
    kind: str,
    size: int = 32,
    n_steps: int = 200,
    n_seeds: int = 4,
    lead: int = 4,
    alpha: float = 0.25,
    speed: float = 0.8,
    capture_radius: float = 1.0,
    capture_burn: int = 100,
    obstacles: Optional[np.ndarray] = None,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, Dict[str, float]]:
    """Croise reactif vs anticipateur p_hat sur ``n_seeds`` graines pour le
    regime ``kind``. Renvoie les **4 metriques de role** moyennees, pour les
    deux animats **et** la marche aleatoire (controle). Verdict **par regime**.

    ``capture_radius`` et ``capture_burn`` ciblent la mesure de capture sur la
    fenetre post-convergence (burn-in) a rayon serre : la capture est une mesure
    de **precision de poursuite**, pas de decouverte. ``speed`` permet
    d'explorer l'axe « source plus rapide que l'animat » (la ou le reactif
    laggué et l'interception p_hat paie).

    C'est le banc du gate 1 : on cherche les regimes ou p_hat **gagne**
    (source previsible + trop rapide pour le reactif) ET ou il **perd**
    (source imprevisible a vitesse attrapable).
    """
    if rng is None:
        rng = np.random.default_rng(7)
    start = np.array([2.0, 2.0])
    out: Dict[str, Dict[str, float]] = {"reactif": {}, "phat": {}, "aleatoire": {}}
    acc = {k: {m: [] for m in ("capture", "escape", "irrevers", "switch")} for k in out}
    for s in range(n_seeds):
        src = source_trajectory(kind, n_steps, size, rng=rng, speed=speed,
                                start=center_start(size))
        tr_r = simulate_reactive(src, size, start, n_steps, obstacles=obstacles)
        tr_p = simulate_phat(src, size, start, n_steps, lead=lead, alpha=alpha, obstacles=obstacles)
        tr_a = random_walk(size, start, n_steps, rng=rng)
        for name, tr in (("reactif", tr_r), ("phat", tr_p), ("aleatoire", tr_a)):
            acc[name]["capture"].append(capture_rate(tr, src, radius=capture_radius, burn=capture_burn))
            acc[name]["escape"].append(escape_rate(tr, src, obstacles))
            acc[name]["irrevers"].append(path_irreversibility(tr, src, obstacles))
            acc[name]["switch"].append(role_switching(tr))
    for name in out:
        out[name] = {m: float(np.mean(acc[name][m])) for m in acc[name]}
    return out


def center_start(size: int) -> np.ndarray:
    return np.array([size / 2.0, size / 2.0])


# --------------------------------------------------------------------------- #
#  Anticipation 2D : baselines adverses du Cran A (gate 3)                    #
# --------------------------------------------------------------------------- #

def anticipation_error_2d(
    predicted_traj: np.ndarray,
    source_traj: np.ndarray,
    lead: int,
) -> float:
    """Erreur quadratique moyenne 2D de la position predite contre la source a
    l'horizon ``lead`` (generalisation de :func:`ict.catastrophe.lead_error`).
    Basse = l'animat anticipe juste la ou la source sera."""
    p = np.asarray(predicted_traj, dtype=float)
    s = np.asarray(source_traj, dtype=float)
    if lead <= 0:
        return float(np.mean(np.sum((p - s) ** 2, axis=1)))
    return float(np.mean(np.sum((p[:-lead] - s[lead:]) ** 2, axis=1)))


def phat_predicted_trajectory(
    source_traj: np.ndarray,
    lead: int = 4,
    alpha: float = 0.25,
) -> np.ndarray:
    """Trajectoire des predictions p_hat a chaque pas (pour comparer aux
    baselines adverses du Cran A sur la meme metrique d'erreur d'anticipation)."""
    obs = np.asarray(source_traj, dtype=float)
    n = len(obs)
    out = np.empty_like(obs)
    for t in range(n):
        out[t] = predict_source(obs, t, lead=lead, alpha=alpha)
    return out


def persistence_trajectory_2d(source_traj: np.ndarray) -> np.ndarray:
    """Baseline persistance 2D : ``p_hat[t] = source[t-1]`` (generalisation de
    :func:`ict.catastrophe.persistence_tracker`). Le reactif spatial realise
    cette baseline puisqu'il vise la position courante."""
    obs = np.asarray(source_traj, dtype=float)
    out = np.empty_like(obs)
    out[0] = obs[0]
    out[1:] = obs[:-1]
    return out


def moving_average_trajectory_2d(source_traj: np.ndarray, window: int = 5) -> np.ndarray:
    """Baseline moyenne mobile causale 2D (generalisation de
    :func:`ict.catastrophe.moving_average_tracker`)."""
    obs = np.asarray(source_traj, dtype=float)
    out = np.empty_like(obs)
    for k in range(len(obs)):
        lo = max(0, k - window + 1)
        out[k] = obs[lo: k + 1].mean(axis=0)
    return out


def ar1_trajectory_2d(source_traj: np.ndarray, lead: int = 4) -> np.ndarray:
    """Baseline AR(1) 2D coordinate par coordinate (generalisation de
    :func:`ict.catastrophe.ar1_tracker`). Avantagee in-sample (adversaire severe)."""
    obs = np.asarray(source_traj, dtype=float)
    out = np.empty_like(obs)
    for d in range(2):
        x = obs[:, d]
        mu = float(x.mean())
        xc = x - mu
        phi = float(np.dot(xc[1:], xc[:-1]) / (np.dot(xc[:-1], xc[:-1]) + 1e-12))
        out[:, d] = mu + (phi ** lead) * xc
    return out
