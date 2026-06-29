"""Trajectoires causales : evolution d'un reseau dans son espace d'etats.

Ce module pose l'outillage de la serie ICT pour passer de la *photographie*
(Phi a un etat donne, calcule par PyPhi) au *film* (la suite des etats
traverses par le systeme, et la valeur de Phi le long de cette suite).

Conformement a la philosophie du package `ict`, ce module ne depend PAS de
PyPhi : il ne manipule que la matrice de transition (TPM, au format
state-by-node de PyPhi) et des cartes d'etats -> valeur fournies par
l'appelant. PyPhi reste sollicite uniquement dans les notebooks, pour
produire la carte de Phi que ces fonctions exploitent ensuite.

Dependances : bibliotheque standard + numpy.

Reference : ICT-0 (cadrage de la serie), Epic #4588.
"""

from __future__ import annotations

from collections import Counter
from typing import Optional

import numpy as np


# --------------------------------------------------------------- espace d'etats
def all_states(n: int):
    """Itere les 2**n etats d'un reseau de n noeuds, comme tuples binaires.

    Convention little-endian (celle de PyPhi) : le bit de poids faible
    correspond au noeud 0. L'ordre d'enumeration suit l'index d'etat 0..2**n-1.
    """
    for i in range(2 ** n):
        yield tuple((i >> b) & 1 for b in range(n))


def state_index(state) -> int:
    """Index little-endian d'un etat (inverse de la position dans all_states)."""
    return sum(int(bit) << b for b, bit in enumerate(state))


# --------------------------------------------------------------- dynamique
def deterministic_successor(sbn_tpm, state) -> tuple:
    """Etat suivant d'un reseau *deterministe*, lu directement dans la TPM.

    ``sbn_tpm`` est la TPM au format state-by-node de PyPhi (``network.tpm``) :
    indexee par le tuple d'etat, elle donne la probabilite d'activation de
    chaque noeud au pas suivant. Pour un reseau deterministe ces probabilites
    valent 0 ou 1 ; on les arrondit pour obtenir l'etat successeur.
    """
    probs = np.asarray(sbn_tpm[tuple(state)]).ravel()
    return tuple(int(round(float(p))) for p in probs)


def state_trajectory(sbn_tpm, start, max_steps: int = 128):
    """Evolue ``start`` pas a pas jusqu'a detecter un cycle.

    Retourne ``(chemin, debut_attracteur)`` ou ``chemin`` est la liste des
    etats visites (le dernier element ferme le cycle en re-citant un etat deja
    vu) et ``debut_attracteur`` l'indice, dans ``chemin``, du premier etat du
    cycle attracteur. ``debut_attracteur`` vaut None si aucun cycle n'est
    atteint en ``max_steps`` pas (ne peut pas arriver pour un reseau fini
    deterministe, mais protege la boucle).
    """
    seen: dict = {}
    s = tuple(start)
    path = [s]
    for step in range(max_steps):
        seen[s] = step
        nxt = deterministic_successor(sbn_tpm, s)
        path.append(nxt)
        if nxt in seen:
            return path, seen[nxt]
        s = nxt
    return path, None


def attractor_of(sbn_tpm, start, max_steps: int = 128) -> list:
    """Cycle attracteur (liste d'etats) atteint depuis ``start``.

    Un point fixe est retourne comme une liste a un seul etat.
    """
    path, cyc = state_trajectory(sbn_tpm, start, max_steps)
    if cyc is None:
        return []
    # path[-1] re-cite path[cyc] ; le cycle est path[cyc:-1]
    return path[cyc:-1]


def basin_sizes(sbn_tpm, n: int, max_steps: int = 128) -> dict:
    """Taille des bassins d'attraction : nb d'etats menant a chaque attracteur.

    Cle = signature canonique de l'attracteur (tuple trie de ses etats),
    valeur = nombre d'etats de depart qui y aboutissent.
    """
    counts: Counter = Counter()
    for s in all_states(n):
        attr = attractor_of(sbn_tpm, s, max_steps)
        counts[tuple(sorted(attr))] += 1
    return dict(counts)


# --------------------------------------------------------------- Phi le long du film
def phi_trajectory(phi_map: dict, path: list) -> list:
    """Suite des valeurs de Phi le long d'un chemin d'etats.

    ``phi_map`` associe chaque etat (tuple) a sa valeur de Phi (calculee par
    PyPhi dans le notebook). ``path`` est un chemin produit par
    ``state_trajectory``.
    """
    return [phi_map[tuple(s)] for s in path]


def detect_events(values, tol: float = 1e-9) -> dict:
    """Minima et maxima locaux stricts d'une courbe (evenements de trajectoire).

    Applique a une trajectoire de Phi, isole les *creux* (chutes locales de
    l'information integree) et les *pics* le long du film causal.
    """
    minima, maxima = [], []
    for i in range(1, len(values) - 1):
        if values[i] + tol < values[i - 1] and values[i] + tol < values[i + 1]:
            minima.append(i)
        if values[i] > values[i - 1] + tol and values[i] > values[i + 1] + tol:
            maxima.append(i)
    return {"minima": minima, "maxima": maxima}


def flip_bit(state, index: int) -> tuple:
    """Retourne l'etat obtenu en basculant le noeud ``index`` (perturbation 1-bit)."""
    s = list(state)
    s[index] = 1 - s[index]
    return tuple(s)
