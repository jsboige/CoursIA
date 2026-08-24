# -*- coding: utf-8 -*-
"""Ensembles limites de l'apprentissage — Poincare-Bendixson (GameTheory-26).

Backing notebook : GameTheory-26-Ensembles-Limites-Poincare-Bendixson.ipynb.
Source : Czechowski & Piliouras 2021, *Poincare-Bendixson Limit Sets in
Multi-Agent Learning* — cite par chemin bibliotheque
(G:/Mon Drive/MyIA/IA/Bibliographie IA/GameTheory/), jamais copiee.

Ce module fournit les deux briques que le notebook execute :

1. Des integrateurs RK4 pour la dynamique de replicateur, en deux cadres
   planaires (dimension 2, la hypothese de Poincare-Bendixson) :
   - une population sur n strategies (etat dans le simplexe, dimension n-1 ;
     n=3 donne le triangle planaire) ;
   - deux populations sur un jeu 2x2 (etat = produit de deux simplexes de
     dimension 1, ie un carre). L'etat est stocke comme vecteur 4-uple
     (x1, x2, y1, y2), chaque paire sommant a 1.
2. Un detecteur de regime qui classe la trajectoire dans l'alternative que le
   theoreme rend exhaustive en dimension 2 : point fixe, orbite periodique,
   ou cycle heteroclinique.

Le detecteur ne lit que la trajectoire (aucune connaissance du jeu) : les
signatures sont mecaniques —

- point fixe : la fin de trajectoire ne bouge plus (diametre de la fenetre
  terminale sous tolerance) ;
- orbite periodique : premier retour de la trajectoire a son point de depart
  (section de Poincare discrete) sans convergence ;
- cycle heteroclinique : ni convergence ni retour, et collage a la frontiere
  de l'espace d'etats (coordonnee minimale sous tolerance).

Toutes les fonctions travaillent en float numpy ; les invariants lineaires
(chaque paire somme a 1) sont preserves exactement par RK4.
"""

from typing import Callable, Dict, Optional, Tuple

import numpy as np

# Regimes detectables (l'alternative de Poincare-Bendixson en dimension 2,
# plus l'etat d'echec honnete).
POINT_FIXE = "point_fixe"
ORBITE_PERIODIQUE = "orbite_periodique"
CYCLE_HETEROCLINIQUE = "cycle_heteroclinique"
INDETERMINE = "indetermine"


# =============================================================================
# Champs de vecteurs : dynamique de replicateur
# =============================================================================

def replicator_1pop_rhs(A: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Second membre 1 population : dx_i/dt = x_i * ((Ax)_i - x^T A x).

    Le simplexe est invariant, et sa somme (lineaire) est conservee.
    """
    x = np.asarray(x, dtype=float)
    fitness = A @ x
    avg = x @ fitness
    return x * (fitness - avg)


def make_state_2pop(x: float, y: float) -> np.ndarray:
    """Etat 2 populations a partir des probabilites d'action 1 : (x, 1-x, y, 1-y)."""
    return np.array([x, 1.0 - x, y, 1.0 - y], dtype=float)


def unpack_2pop(z: np.ndarray) -> Tuple[float, float]:
    """Recupere (x, y) = probabilites d'action 1 de chaque population."""
    return float(z[0]), float(z[2])


def replicator_2pop_rhs(A: np.ndarray, B: np.ndarray, z: np.ndarray) -> np.ndarray:
    """Second membre 2 populations sur un jeu 2x2, etat 4-uple (x1, x2, y1, y2).

    dx_i/dt = x_i * ((A y)_i - x^T A y)   pour la population 1 (matrice A),
    dy_j/dt = y_j * ((B^T x)_j - y^T B^T x) pour la population 2 (matrice B),
    ou x = (x1, x2), y = (y1, y2) sont les distributions des deux populations.
    """
    z = np.asarray(z, dtype=float)
    x = z[:2]
    y = z[2:]
    fit_x = A @ y
    dx = x * (fit_x - x @ fit_x)
    fit_y = B.T @ x
    dy = y * (fit_y - y @ fit_y)
    return np.concatenate([dx, dy])


# =============================================================================
# Integrateur RK4
# =============================================================================

def integrate_rk4(rhs: Callable[[np.ndarray], np.ndarray],
                  z0: np.ndarray, t_max: float, dt: float) -> Tuple[np.ndarray, np.ndarray]:
    """Integre z' = rhs(z) de t=0 a t_max par Runge-Kutta 4 a pas fixe.

    Returns:
        times: (N,) instants ; traj: (N, len(z0)) etats, traj[0] = z0.
        Les invariants lineaires de rhs sont conserves exactement par RK4.
    """
    z0 = np.asarray(z0, dtype=float)
    n_steps = int(round(t_max / dt))
    times = np.arange(n_steps + 1) * dt
    traj = np.empty((n_steps + 1, z0.size))
    traj[0] = z0
    z = z0.copy()
    for k in range(n_steps):
        k1 = rhs(z)
        k2 = rhs(z + 0.5 * dt * k1)
        k3 = rhs(z + 0.5 * dt * k2)
        k4 = rhs(z + dt * k3)
        z = z + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)
        traj[k + 1] = z
    return times, traj


# =============================================================================
# Detection de regime
# =============================================================================

def first_return_index(times: np.ndarray, traj: np.ndarray,
                       tol_return: float, t_skip: float) -> Optional[Tuple[int, float]]:
    """Premier retour (section de Poincare discrete) pres du point initial.

    Cherche le premier indice i tel que times[i] >= t_skip et
    ||traj[i] - traj[0]|| <= tol_return. Retourne (i, distance) ou None.
    """
    traj = np.asarray(traj, dtype=float)
    times = np.asarray(times, dtype=float)
    start = int(np.searchsorted(times, t_skip, side="left"))
    d = np.linalg.norm(traj[start:] - traj[0], axis=1)
    hits = np.nonzero(d <= tol_return)[0]
    if hits.size == 0:
        return None
    i = start + int(hits[0])
    return i, float(d[hits[0]])


def _simplex_blocks(dim: int):
    """Decoupe l'espace d'etats en simplexes de population.

    Dimension 4 (jeu 2x2 bimatriciel) -> deux blocs de 2 : chaque population
    vit dans son propre simplexe, et la dominance se juge AU SEIN de chaque
    simplexe. Toute autre dimension -> un seul bloc (une population).

    C'est le point cle anti-faux-positif : un argmax sur le 4-uple entier
    compare des coordonnees de populations differentes (x1 avec y1) et
    produit un clignotement sans signification a proximite d'un coin du carre.
    """
    if dim == 4:
        return [(0, 2), (2, 4)]
    return [(0, dim)]


def dominant_episodes(times: np.ndarray, traj: np.ndarray,
                      share: float = 0.5):
    """Segments de trajectoire par action dominante de chaque population.

    L'etiquette d'un segment est un uplet (un element par population) : l'index
    dominant au sein du simplexe de chaque population. Un changement
    d'etiquette n'est compte que lorsque, pour CHAQUE population dont la
    dominance change, la nouvelle coordonnee dominante depasse ``share`` dans
    son simplexe (anti-rebond aux frontieres 50/50). Sert a la signature du
    cycle heteroclinique : une trajectoire qui quitte plusieurs sommets avec
    des temps de sejour croissants ne peut pas converger vers un point.

    Returns:
        (dominants, bornes) — etiquettes (liste d'uplets) et instants de
        debut de chaque segment (k,).
    """
    traj = np.asarray(traj, dtype=float)
    times = np.asarray(times, dtype=float)
    blocks = _simplex_blocks(traj.shape[1])

    def label(z):
        return tuple(int(np.argmax(z[a:b])) for a, b in blocks)

    dominants = [label(traj[0])]
    bounds = [0.0]
    for t_i, z in zip(times, traj):
        lab = label(z)
        if lab != dominants[-1]:
            changed = [p for p in range(len(blocks))
                       if lab[p] != dominants[-1][p]]
            if all(z[blocks[p][0] + lab[p]] > share for p in changed):
                dominants.append(lab)
                bounds.append(float(t_i))
    return dominants, np.array(bounds)


def detect_regime(times: np.ndarray, traj: np.ndarray, *,
                  tol_point: float = 2e-3,
                  tol_return: float = 5e-2,
                  tol_boundary: float = 1e-3,
                  window_frac: float = 0.2,
                  escape_growth: float = 1.5,
                  escape_floor: float = 1.0) -> Tuple[str, Dict]:
    """Classe la trajectoire : point fixe / orbite periodique / cycle heteroclinique.

    Signatures mecaniques (le detecteur ne connait pas le jeu) :

    1. point fixe — le diametre de la fenetre terminale (derniere fraction
       ``window_frac``) est sous ``tol_point`` ET la trajectoire n'a pas
       \"echappe\" (voir ci-dessous) ;
    2. orbite periodique — convergence ratee, mais premier retour au point
       initial (section de Poincare discrete) sous ``tol_return`` ;
    3. cycle heteroclinique — ni l'un ni l'autre, et soit collage a la
       frontiere (coordonnee minimale de la fenetre terminale sous
       ``tol_boundary``), soit trajectoire \"echappee\" : au moins 3 temps de
       sejour, le dernier a la fois au-dessus du plancher absolu
       ``escape_floor`` ET >= ``escape_growth`` x la mediane des precedents —
       chaque depart d'un sommet refute la convergence vers ce sommet, et
       l'allongement des sejours est la signature du ralentissement
       heteroclinique.

    La clause d'echappement est ce qui distingue le point fixe vrai du cliché
    d'une rampe heteroclinique profonde : pres d'un sommet du cycle, la
    trajectoire rampe si lentement que la fenetre terminale parait immobile.
    Son plancher absolu distingue reciproquement le transit pre-selle d'un
    jeu coordonne (changement de dominance de duree ~0.03) du sejour reel
    pres d'un sommet heteroclinique (duree > 1).

    Returns:
        (regime, info) — info porte les mesures brutes pour inspection.
    """
    traj = np.asarray(traj, dtype=float)
    times = np.asarray(times, dtype=float)
    n = len(times)
    w = max(2, int(window_frac * n))
    tail = traj[-w:]

    dominants, bounds = dominant_episodes(times, traj)
    gaps = np.diff(bounds) if len(bounds) > 1 else np.array([])
    escaped = bool(len(gaps) >= 3 and gaps[-1] >= escape_floor
                   and gaps[-1] >= escape_growth * float(np.median(gaps[:-1])))
    info: Dict = {"segments_dominance": len(dominants),
                  "temps_de_sejour": [float(g) for g in gaps]}

    drift = float(np.max(np.linalg.norm(tail - traj[-1], axis=1)))
    info["drift_final"] = drift
    if drift < tol_point and not escaped:
        return POINT_FIXE, info

    t_skip = float(times[w])
    ret = first_return_index(times, traj, tol_return, t_skip)
    info["premier_retour"] = (None if ret is None
                              else {"t": float(times[ret[0]]), "distance": ret[1]})
    if ret is not None:
        return ORBITE_PERIODIQUE, info

    min_coord_tail = float(np.min(tail))
    info["distance_frontiere_finale"] = min_coord_tail
    if min_coord_tail < tol_boundary or escaped:
        return CYCLE_HETEROCLINIQUE, info
    return INDETERMINE, info


# =============================================================================
# Jeux canoniques des trois regimes
# =============================================================================

def prisoner_dilemma_matrices() -> Tuple[np.ndarray, np.ndarray]:
    """Dilemme du Prisonnier (Axelrod T=5, R=3, P=1, S=0), actions (C, D).

    Regime : point fixe — (D, D) equilibre strict, coin attracteur du carre.
    """
    A = np.array([[3.0, 0.0],
                  [5.0, 1.0]])  # ligne : population 1 (C, D) ; colonne : population 2
    B = np.array([[3.0, 5.0],
                  [0.0, 1.0]])
    return A, B


def matching_pennies_matrices() -> Tuple[np.ndarray, np.ndarray]:
    """Matching Pennies (+1/-1), actions (Pile, Face).

    Regime : orbite periodique — chaque orbite interieure est fermee, d'invariant
    x(1-x) * y(1-y) (verifie numeriquement dans le notebook).
    """
    A = np.array([[1.0, -1.0],
                  [-1.0, 1.0]])
    B = -A
    return A, B


def stag_hunt_matrices() -> Tuple[np.ndarray, np.ndarray]:
    """Chasse au Cerf (Rousseau), actions (Cerf, Lievre).

    A[0][0] = 4 : deux chasseurs coordonnes prennent le cerf ; un chasseur
    seul qui vise le cerf prend 1, mais peut toujours prendre le lievre (2 ou
    3). A n'est PAS symetrique (A[0][1] = 1 != A[1][0] = 3) : la population 2
    joue avec B = A^T — oublier la transposee fabrique un faux jeu ou (Cerf,
    Cerf) attire depuis partout.

    Regime : point fixe — deux attracteurs en coin, (Cerf, Cerf) et (Lievre,
    Lievre), et une selle interieure dont la variete stable est la droite
    x + y = 1 : elle separe les bassins (x + y > 1 -> Cerf, x + y < 1 ->
    Lievre).
    """
    A = np.array([[4.0, 1.0],
                  [3.0, 2.0]])
    return A, A.T


def rps_matrix(w: float, l: float) -> np.ndarray:
    """Famille Pierre-Feuille-Ciseaux parametree par gain de victoire w et defaite l.

    A[i][j] = gain de i contre j : victoire w, defaite -l, nul 0 (matrice
    antisymetrique ssi w = l). Le mur w = l separe deux regimes — le sens est
    mesure par simulation ET par la linearisation au barycentre (partie reelle
    (l - w) / 6, derivee dans le notebook) :

    - w > l (vaincre rapporte plus que perdre ne coûte) : barycentre
      asymptotiquement stable, spirale rentrante — regime POINT_FIXE ;
    - w < l : barycentre instable, l'ensemble omega-limite des trajectoires
      interieures est le cycle heteroclinique Pierre -> Feuille -> Ciseaux ->
      Pierre sur la frontiere du simplexe.
    """
    return np.array([[0.0, -l, w],
                     [w, 0.0, -l],
                     [-l, w, 0.0]])


def mp_invariant(z: np.ndarray) -> float:
    """Invariant de Matching Pennies 2 populations : x(1-x) * y(1-y).

    Constant le long des trajectoires (demonstration dans le notebook) —
    ses lignes de niveau sont les orbites fermees.
    """
    x, y = unpack_2pop(np.asarray(z, dtype=float))
    return x * (1.0 - x) * y * (1.0 - y)
