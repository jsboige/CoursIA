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
   substrat canonique. **Ponderee et lissee, donc dense** : voir
   :func:`observed_adjacency` pour le voisinage structurel.
1bis. :func:`observed_adjacency` : adjacence **booleenne non lissee**
   (« la transition a-t-elle ete observee ? »). A utiliser des qu'on
   compte des voisins plutot qu'on pondere des flux (issue #9764).
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
    "observed_adjacency",
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
    poids = moyenne des deux flux directionnels.

    .. warning::

       **``W`` n'est PAS une matrice d'adjacence structurelle.** Des que
       ``laplace_smoothing > 0`` -- c'est-a-dire **par defaut** --
       :func:`ict.time_arrow.transition_matrix` ajoute un plancher
       strictement positif a *chaque* coefficient (c'est precisement son
       role : donner une distribution uniforme aux etats non observes
       plutot qu'une ligne nulle). ``W`` est donc **dense hors
       diagonale**, et un test d'adjacence ``W[i, j] > 0`` renvoie
       ``True`` pour **toutes** les paires, y compris pour des etats
       jamais visites par la trajectoire.

       Pour obtenir le voisinage *structurel* (« la transition a-t-elle
       ete observee ? »), utiliser :func:`observed_adjacency`, qui ne
       depend d'aucun lissage. Le lissage de ``W`` est fait pour les
       usages *spectraux* (Laplacien, gap), ou une ligne nulle casserait
       la diagonalisation -- pas pour compter des voisins.

       Une version anterieure de cette docstring affirmait « les aretes
       absentes du graphe Markovien restent a 0 » : c'etait faux des que
       le lissage est actif, et cette fausse premisse a produit un
       defaut de mesure dans :mod:`ict.sensitivity` (issue #9764).

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
    a diagonale nulle, a coefficients >= 0 -- et **strictement** positifs
    hors diagonale des que ``laplace_smoothing > 0`` (cf. avertissement
    ci-dessus).
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


def observed_adjacency(
    states: Sequence,
    n_symbols: int,
) -> np.ndarray:
    """Adjacence **structurelle** du graphe de transition : booleenne, non lissee.

    ``A[i, j]`` est ``True`` si et seulement si la transition ``i -> j``
    **ou** ``j -> i`` a ete **effectivement observee** dans ``states``
    (paires consecutives). C'est la reponse a « ``j`` est-il un voisin de
    ``i`` ? », question **structurelle** qui ne doit dependre d'aucune
    ponderation ni d'aucun lissage.

    Pourquoi cette primitive existe separement de
    :func:`transition_graph` : ``transition_graph`` est ponderee et
    **lissee par defaut**, donc dense hors diagonale (cf. son
    avertissement). Deriver un voisinage d'un ``W[i, j] > 0`` y declare
    tout noeud voisin de tout noeud -- ce qui transforme silencieusement
    tout comptage de voisins en comptage de la **taille du vocabulaire**.
    C'est la cause du defaut de mesure de l'issue #9764.

    Les **boucles sont exclues** (diagonale ``False``), par coherence avec
    la diagonale nulle de :func:`transition_graph` : un etat n'est pas son
    propre voisin, et une transition ``i -> i`` (le systeme reste sur
    place) n'est pas une arete du graphe.

    Un etat **jamais visite** a une ligne entierement ``False`` : degre 0,
    aucun voisin. C'est le comportement voulu -- contrairement au lissage,
    qui lui attribue une distribution uniforme sur tout le vocabulaire.

    Parametres :
      - ``states`` : sequence d'etats **deja encodes** en entiers
        ``0..n_symbols-1`` (meme convention que
        :func:`ict.time_arrow.transition_matrix` ; les paires hors bornes
        sont ignorees silencieusement, comme la-bas).
      - ``n_symbols`` : taille du vocabulaire ``k``.

    Retourne une matrice ``(n_symbols, n_symbols)`` booleenne, symetrique
    (``A.T == A``), a diagonale ``False``. Aucune division : ni ``NaN``,
    ni ``RuntimeWarning``, meme quand aucune transition n'est observee.
    """
    states_int = [int(s) for s in states]
    A = np.zeros((n_symbols, n_symbols), dtype=bool)
    for s, t in zip(states_int[:-1], states_int[1:]):
        if s == t:
            # Boucle : le systeme reste sur place, pas une arete.
            continue
        if 0 <= s < n_symbols and 0 <= t < n_symbols:
            A[s, t] = True
            A[t, s] = True
    return A


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
