"""Estimation de TPM a partir de trajectoires observees (pont vers CE 2.0).

Ce module construit une matrice de transition **etat-a-etat** (le format de
``ict.causal_emergence``) a partir de *trajectoires* discretes -- typiquement
les suites de configurations produites par les modeles de la serie ICT
(self-sorting arrays d'ICT-2, reseaux booleens d'ICT-1). C'est le pont qui
permet de soumettre une dynamique simulee a l'analyse d'emergence causale
d'ICT-6/ICT-7, sans la borne de taille de PyPhi.

Trois entrees principales :
  - ``tpm_from_transitions`` : une liste de transitions explicites
    ``(s_t, s_{t+1})`` ;
  - ``tpm_from_trajectory`` : une suite d'etats consecutifs ;
  - ``tpm_from_trajectories`` : plusieurs trajectoires agregees.

Les etats peuvent etre n'importe quel label hachable (entier, tuple,
chaine...). Les lignes jamais observees sont par defaut *self-absorbantes*
(``unseen="self"`` : l'etat se repete, on n'invente pas de transition) ;
``unseen="uniform"`` produit une ligne uniforme a la place.

Un pont supplementaire (``flat_tpm_from_sbn``) convertit une TPM state-by-node
deterministe (format PyPhi de ``ict.trajectories``) en TPM etat-a-etat, pour
analyser les reseaux booleens d'ICT-1 avec l'outillage CE 2.0 et comparer avec
``pyphi.macro`` (ICT-5).

Dependances : bibliotheque standard + numpy.
Reference : ICT-0 (cadrage de la serie), Epic #4588.
"""

from __future__ import annotations

from typing import Iterable, Optional

import numpy as np


# --------------------------------------------------------------- indexation des etats
def state_index_map(states: Iterable) -> dict:
    """Associe chaque label d'etat distinct a un index ``0..k-1``.

    L'ordre des index suit l'ordre de PREMIERE apparition dans ``states``, ce
    qui rend la TPM reproductible et lisible.
    """
    mapping: dict = {}
    for s in states:
        if s not in mapping:
            mapping[s] = len(mapping)
    return mapping


def _normalize_counts(counts: np.ndarray, unseen: str = "self") -> np.ndarray:
    """Normalise une matrice de comptes en TPM ligne-stochastique.

    ``unseen`` gere les lignes de somme nulle (etats jamais quittes / observes
    sans successeur) : ``"self"`` (defaut) place une auto-transition, "uniform"
    repartit uniformement.
    """
    n = counts.shape[0]
    tpm = counts.astype(float).copy()
    row_sums = tpm.sum(axis=1)
    for i in range(n):
        if row_sums[i] <= 0:
            if unseen == "uniform":
                tpm[i] = np.full(n, 1.0 / n)
            elif unseen == "self":
                tpm[i] = 0.0
                tpm[i, i] = 1.0
            else:
                raise ValueError(f"unseen inconnu : {unseen!r} (self|uniform)")
        else:
            tpm[i] = tpm[i] / row_sums[i]
    return tpm


# --------------------------------------------------------------- estimation
def tpm_from_transitions(transitions, mapping: Optional[dict] = None,
                         unseen: str = "self"):
    """TPM empirique a partir de transitions ``(s_t, s_{t+1})``.

    Retourne ``(tpm, mapping)`` ou ``mapping`` associe chaque label d'etat a son
    index de ligne/colonne. Si ``mapping`` est fourni, il est reutilise (tous
    les labels rencontres DOIVENT y figurer) ; sinon il est construit a partir
    des etats observes.
    """
    pairs = [(a, b) for a, b in transitions]
    if mapping is None:
        labels = []
        for a, b in pairs:
            labels.append(a)
            labels.append(b)
        mapping = state_index_map(labels)
    n = len(mapping)
    counts = np.zeros((n, n), dtype=float)
    for a, b in pairs:
        if a not in mapping or b not in mapping:
            raise KeyError(f"etat absent du mapping fourni : {a!r} ou {b!r}")
        counts[mapping[a], mapping[b]] += 1.0
    return _normalize_counts(counts, unseen), mapping


def tpm_from_trajectory(states, mapping: Optional[dict] = None,
                        unseen: str = "self"):
    """TPM empirique a partir d'une suite d'etats consecutifs.

    Les transitions sont les paires adjacentes ``(states[t], states[t+1])``.
    Retourne ``(tpm, mapping)``.
    """
    seq = list(states)
    transitions = list(zip(seq, seq[1:]))
    return tpm_from_transitions(transitions, mapping, unseen)


def tpm_from_trajectories(trajectories, mapping: Optional[dict] = None,
                          unseen: str = "self"):
    """TPM empirique agregeant PLUSIEURS trajectoires (transitions poolees).

    Le mapping (s'il n'est pas fourni) couvre l'union des etats de toutes les
    trajectoires, dans l'ordre de premiere apparition. Retourne ``(tpm,
    mapping)``.
    """
    all_transitions = []
    if mapping is None:
        labels = []
        for traj in trajectories:
            seq = list(traj)
            labels.extend(seq)
            all_transitions.extend(zip(seq, seq[1:]))
        mapping = state_index_map(labels)
    else:
        for traj in trajectories:
            seq = list(traj)
            all_transitions.extend(zip(seq, seq[1:]))
    return tpm_from_transitions(all_transitions, mapping, unseen)


# --------------------------------------------------------------- pont state-by-node
def flat_tpm_from_sbn(sbn_tpm, n_nodes: int) -> np.ndarray:
    """Convertit une TPM state-by-node DETERMINISTE en TPM etat-a-etat.

    Utilise ``ict.trajectories.deterministic_successor`` : chaque etat va vers
    son successeur deterministe avec probabilite 1, dans l'indexation
    little-endian de PyPhi (``state_index``). Pratique pour analyser les
    reseaux booleens d'ICT-1 avec l'outillage CE 2.0 et les comparer a
    ``pyphi.macro`` (ICT-5).

    Retourne une TPM ``(2**n_nodes, 2**n_nodes)``.
    """
    from . import trajectories as T

    size = 2 ** n_nodes
    tpm = np.zeros((size, size), dtype=float)
    for state in T.all_states(n_nodes):
        i = T.state_index(state)
        nxt = T.deterministic_successor(sbn_tpm, state)
        tpm[i, T.state_index(nxt)] = 1.0
    return tpm
