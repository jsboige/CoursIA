"""Boite a outils spectrale mutualisable pour ICT strate 5 (#7288 / Epic #4588).

Cible : calculer sur le **graphe de transition** (TPM = matrice de
transition markovienne) d'une trajectoire ICT les quantites spectrales qui
serviront de pont entre :

* la **sensibilite locale** (ICT-15b, Huang 2019 transpose au zoo ICT),
  voir :mod:`ict.sensitivity`,
* la **contextualite / Kochen-Specker** (ICT-29, annexe speculative,
  pont vers le zoo de proxys),
* le **substrat argumentation** (ICT strate 6, #7289, graphes de
  croyance et dette d'irreversibilite du discours).

L'idee structurante : la matrice d'adjacence *signee* du graphe de
transition et son Laplacien portent une information spectrale qui
discrimine les substrats meme quand les statistiques d'ordre 1 (Phi, F,
K) ne suffisent pas. C'est le complement *lineaire-algebrique* du
complement *markovien* de :func:`ict.time_arrow.entropy_production`.

Quatre primitives :

1. :func:`transition_graph` : graphe symetrise depuis la TPM (matrice
   d'adjacence ponderee non-dirigee, ``W = (P + P^T) / 2``) -- le
   substrat canonique.
2. :func:`signed_adjacency` : matrice de signes (-1/+1) construite
   depuis les flux nets de transition (le "courant" Markovien). C'est
   l'analogue direct de la matrice de signes de Huang 2019 sur
   l'hypercube : A^2 = n * Id dans le cas booleen ; ici on documente
   ce que devient cette propriete sur un graphe Markovien asymetrique.
3. :func:`laplacian_spectrum` : valeurs propres du Laplacien symetrique
   normalise, avec lacet (largest gap = temps de relaxation).
4. :func:`spectral_gap` : raccourci vers le gap spectral -- proxy
   classique de la "duree de memoire" d'un graphe (cheeger-like).

Numpy uniquement, comme le reste du package leger ``ict``. Aucun GPU
requis (garanti GPU-free, mandat user 2026-07-04). Toutes les fonctions
sont deterministes (numpy seul, pas d'aléatoire cache).
"""

from __future__ import annotations

from typing import Dict, Sequence

import numpy as np

from .time_arrow import transition_matrix

__all__ = [
    "transition_graph",
    "signed_adjacency",
    "laplacian_spectrum",
    "spectral_gap",
    "current_matrix",
]


# --------------------------------------------------------------------------- #
#  1. Graphe de transition (TPM symmetrisee, ponderee par flux nets)           #
# --------------------------------------------------------------------------- #
def transition_graph(
    states: Sequence,
    n_symbols: int,
    *,
    laplace_smoothing: float = 1e-9,
) -> np.ndarray:
    """Matrice d'adjacence **symetrique** du graphe de transition.

    Symetrisation standard : ``W = (P + P^T) / 2`` (matrice de transition
    symmetrisee). Pour chaque paire ``(i, j)``, on moyenne les
    probabilites de transition dans les deux directions : si
    ``P[i, j] > 0`` ou ``P[j, i] > 0``, l'arete est isante avec un
    poids = moyenne des deux flux directionnels. Les aretes absentes
    du graphe Markovien restent a 0.

    Pourquoi PAS le minimum des flux nets ``min(pi_i P[i,j], pi_j P[j,i])``
    : sur une chaine asymetrique (ex. cycle unidirectionnel), le flux
    reverse est nul et le minimum s'ecroule a zero pour toutes les
    aretes. La moyenne preserve la structure : un cycle unidirectionnel
    devient un cycle non-pese symmetrique avec aretes de poids 0.5.

    L'asymetrie directionnelle est preservee separement dans
    :func:`current_matrix`.

    Parametres :
      - ``states`` : sequence d'etats (entiers ou labels) ; voir
        :func:`ict.time_arrow.transition_matrix` pour le format.
      - ``n_symbols`` : taille du vocabulaire d'etats ``k``.
      - ``laplace_smoothing`` : transmis a :func:`transition_matrix`.

    Retourne une matrice carree ``(n_symbols, n_symbols)`` symmetrique,
    a diagonale nulle, a coefficients >= 0.
    """
    P = transition_matrix(states, n_symbols, laplace_smoothing=laplace_smoothing)
    # Matrice de transition symmetrisee : moyenne des flux directionnels.
    # Symetrique par construction, valeurs >= 0, diagonale nulle (apres
    # fill_diagonal). On n'utilise PAS le minimum des flux nets
    # ``min(pi_i P[i,j], pi_j P[j,i])`` qui s'ecroule a zero sur les
    # chaines asymetriques (le flux reverse est nul). La moyenne
    # preserve la structure : un cycle unidirectionnel devient un
    # cycle non-pese symmetrique avec aretes de poids 0.5.
    W = (P + P.T) / 2.0
    np.fill_diagonal(W, 0.0)
    return W


# --------------------------------------------------------------------------- #
#  2. Matrice de signes (courants nets)                                         #
# --------------------------------------------------------------------------- #
def current_matrix(
    P: np.ndarray,
    pi: np.ndarray,
) -> np.ndarray:
    """Matrice antisymetrique des **courants nets** entre paires.

    ``J[i, j] = pi_i * P[i, j] - pi_j * P[j, i]`` ; c'est la decomposition
    canonique de la production d'entropie (cf. Schnakenberg 1976, cite
    dans :func:`ict.time_arrow.entropy_production`).

    Retourne une matrice carree ``(k, k)`` antisymetrique (``J.T == -J``),
    a diagonale nulle. La **norme de Frobenius** de J vaut ``sqrt(2 * sigma)``
    ou ``sigma`` est la production d'entropie.

    Ce n'est PAS la matrice de signes booleenne de Huang 2019 (qui vit
    sur l'hypercube ``{0, 1}^n``). Mais c'est l'analogue **continu** sur
    un graphe Markovien : ses valeurs propres imaginaires pures
    encodent les "modes de circulation" du systeme hors equilibre.
    """
    pi = np.asarray(pi, dtype=float)
    flux_fwd = pi[:, None] * np.asarray(P, dtype=float)
    flux_bwd = pi[None, :] * np.asarray(P, dtype=float).T
    J = flux_fwd - flux_bwd
    np.fill_diagonal(J, 0.0)
    return J


def signed_adjacency(
    states: Sequence,
    n_symbols: int,
    *,
    laplace_smoothing: float = 1e-9,
) -> np.ndarray:
    """Matrice d'adjacence *signee* du graphe de transition Markovien.

    C'est la matrice de signes ``S = sign(W + J)`` ou ``W`` est le graphe
    symmetrique (:func:`transition_graph`) et ``J`` la matrice de courants
    (:func:`current_matrix`). On combine :

    * les aretes isantes ``W[i, j] > 0`` recoivent le signe du courant
      net ``sign(J[i, j])`` (le sens privilegie du flux) ;
    * les aretes absentes du graphe Markovien restent a 0.

    Sur l'hypercube booleen de Huang 2019, cette matrice est
    antisymetrique et verifie ``A^2 = n * Id``. Sur un graphe de
    transition Markovien quelconque, la propriete ne tient plus -- c'est
    une deviation structurelle documentee dans :mod:`ict.sensitivity`
    (qui pose la conjecture sur la sensibilite comme proxy de "distance
    spectrale a la reversibilite").

    Retourne une matrice carree ``(k, k)`` reelle, antisymetrique sur
    les aretes isantes.
    """
    P = transition_matrix(states, n_symbols, laplace_smoothing=laplace_smoothing)
    # Stationary distribution (meme fallback que transition_graph).
    try:
        vals, vecs = np.linalg.eig(P.T)
        idx = int(np.argmin(np.abs(vals - 1.0)))
        pi = np.real(vecs[:, idx])
        pi = np.maximum(pi, 0.0)
        if pi.sum() <= 0:
            raise ValueError("stationary vector degenerate")
        pi = pi / pi.sum()
    except (np.linalg.LinAlgError, ValueError):
        pi = np.full(n_symbols, 1.0 / n_symbols)

    W = transition_graph(states, n_symbols, laplace_smoothing=laplace_smoothing)
    J = current_matrix(P, pi)
    # Signe = signe du courant net sur les aretes isantes, 0 sinon.
    S = np.zeros_like(W)
    mask = W > 0
    S[mask] = np.sign(J[mask])
    # Anti-symetrisation : si on a signe J[i,j] et J[j,i] differemment
    # (ne peut pas arriver car J est antisym), on prend la moyenne.
    S = 0.5 * (S - S.T)
    return S


# --------------------------------------------------------------------------- #
#  3. Spectre du Laplacien                                                      #
# --------------------------------------------------------------------------- #
def laplacian_spectrum(W: np.ndarray) -> np.ndarray:
    """Valeurs propres du Laplacien symmetrique ``L = D - W``.

    ``W`` est la matrice d'adjacence symetrique (depuis
    :func:`transition_graph`).

    Retourne un vecteur de ``k`` valeurs propres triees par ordre
    croissant (la plus petite est ~0 si le graphe est connexe, plus
    grande si le graphe a plusieurs composantes).
    """
    W = np.asarray(W, dtype=float)
    if W.shape[0] != W.shape[1]:
        raise ValueError(f"W must be square, got shape {W.shape}")
    if not np.allclose(W, W.T, atol=1e-12):
        raise ValueError("W must be symmetric (use transition_graph output)")
    D = np.diag(W.sum(axis=1))
    L = D - W
    eigs = np.linalg.eigvalsh(L)
    return np.sort(eigs)


def spectral_gap(W: np.ndarray) -> float:
    """Gap spectral du Laplacien = ``lambda_2 - lambda_1``.

    ``lambda_1 = 0`` toujours (vecteur propre constant si le graphe est
    connexe). Le gap ``lambda_2 - lambda_1 = lambda_2`` est un proxy
    classique du temps de melange du graphe (cheeger-like).

    Pour un graphe de transition ICT, un **petit** gap spectral
    correspond a un substrat a **longue memoire** (convergence lente
    vers la distribution stationnaire). Un **grand** gap = dynamique
    rapide, substrat "peu de memoire".
    """
    eigs = laplacian_spectrum(W)
    if eigs.size < 2:
        return float("nan")
    return float(eigs[1] - eigs[0])


# --------------------------------------------------------------------------- #
#  4. Resume spectral d'un graphe de transition                                #
# --------------------------------------------------------------------------- #
def spectral_summary(states: Sequence, n_symbols: int) -> Dict[str, float]:
    """Resume spectral compact d'une trajectoire ICT.

    Retourne un dict avec ``n_states``, ``spectral_gap``, ``mean_degree``
    (degre moyen du graphe symmetrique), ``n_edges`` (nombre d'aretes
    isantes), ``density`` (fraction d'aretes presentes).
    """
    W = transition_graph(states, n_symbols)
    n_edges = int(np.sum(W > 0) // 2)
    density = float(n_edges) / float(n_symbols * (n_symbols - 1) / 2) if n_symbols > 1 else 0.0
    degree = W.sum(axis=1)
    return {
        "n_states": int(n_symbols),
        "n_edges": n_edges,
        "density": density,
        "mean_degree": float(np.mean(degree)),
        "spectral_gap": spectral_gap(W),
    }
