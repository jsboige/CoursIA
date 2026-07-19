"""Sensibilite locale ICT -- transposition du theoreme de Huang 2019 au zoo
ICT (ICT-15b, strate 5, #7288 / Epic #4588).

Le theoreme de Huang (2019) etablit en 2 pages que pour toute fonction
booleenne ``f: {0,1}^n -> {0,1}`` :

    s(f) >= sqrt(deg(f))

ou ``s(f)`` est la sensibilite (max nb de voisins ou ``f`` bascule) et
``deg(f)`` le degre polynomial de ``f`` comme representant sur
l'hypercube. La preuve est spectrale : la matrice de signes ``A`` sur
l'hypercube verifie ``A^2 = n * Id``, et un entrelacement de Cauchy
conclut. Avant Huang, la borne inferieure ``s(f) = Omega(log n)`` etait
le verrou ; apres Huang, ``s(f) = Omega(sqrt(deg(f)))``.

La legon structurelle au-dela des fonctions booleennes : **un scalaire
est canonique quand il BORNE les autres** -- pas quand il les resume.
C'est exactement le cadre d'ICT-15 (IntegratedComplexity, strate 4) qui
a falsifie le "scalaire universel" : les trois scalaires Phi/F/K ne se
reduisent pas l'un a l'autre (Gate 4, tau de Kendall).

La question ICT-15b devient : **existe-t-il un scalaire LOCAL dont une
fonction simple borne les scalaires GLOBAUX du zoo ICT ?**

Statut epistemique : une trajectoire ICT n'est **pas** une fonction
booleenne statique (l'hypercube, le degre polynomial, la structure
produit -- tout cela se perd). Il n'y a **pas** de theoreme a appliquer,
il y a une **conjecture a construire et tester**. Un verdict negatif
serait un resultat en soi.

Ce module operationalise la question :

1. :func:`local_sensitivity` : sensibilite locale ``s_x(f)`` sur le graphe
   de transition Markovien d'une trajectoire ICT -- le nombre de voisins
   ou une fonction d'etat ``f`` bascule.
2. :func:`sensitivity_distribution` : distribution resumee (max,
   moyenne, queue) sur tous les noeuds visites.
3. :func:`huang_conjecture_test` : test de la conjecture type-Huang
   ``s_max(f) >= sqrt(deg_proxy(f))`` ou ``deg_proxy`` est le degre du
   proxy polynomial (degre moyen du voisinage). Renvoie un verdict
   `consistent` / `inconsistent` / `inconclusive` (verdict honnete,
   pas de fabrication -- cf regle G.1 anti-regression).

Numpy uniquement. GPU-free (mandat user 2026-07-04). Toutes les
fonctions sont deterministes (numpy seul, pas d'aléatoire cache).
"""

from __future__ import annotations

from typing import Callable, Dict, Sequence

import numpy as np

from .spectral import transition_graph

__all__ = [
    "local_sensitivity",
    "sensitivity_distribution",
    "huang_conjecture_test",
]


# --------------------------------------------------------------------------- #
#  Sensibilite locale sur le graphe de transition                               #
# --------------------------------------------------------------------------- #
def local_sensitivity(
    states: Sequence,
    n_symbols: int,
    state_function: Callable[[int], int],
    *,
    laplace_smoothing: float = 1e-9,
) -> np.ndarray:
    """Sensibilite locale ``s_x(f)`` pour chaque noeud du graphe.

    Pour chaque etat ``x`` du vocabulaire, on evalue la fonction d'etat
    ``f(x)`` et on compte le nombre de **voisins** ``y`` (au sens du
    graphe de transition) ou ``f(y) != f(x)``. Le voisinage est
    determine par :func:`ict.spectral.transition_graph` (TPM symmetrisee).

    Parametres :
      - ``states`` : sequence d'etats de la trajectoire (memes labels que
        passes a :func:`ict.time_arrow.transition_matrix`).
      - ``n_symbols`` : taille du vocabulaire.
      - ``state_function`` : callable ``int -> int`` definissant la
        fonction d'etat ``f`` (typiquement 0 ou 1 pour les fonctions
        booleennes, mais peut etre a valeurs dans ``{0, ..., m-1}`` pour
        des fonctions multi-valentes -- le basculement est alors defini
        comme ``f(y) != f(x)``).
      - ``laplace_smoothing`` : transmis a la construction du graphe.

    Retourne un vecteur numpy de forme ``(n_symbols,)`` ou
    ``s_x[i] = s_x_i(f)``.
    """
    # Encodage des labels en entiers 0..n_symbols-1. On accepte
    # exactement n_symbols labels distincts ; un depassement (= un
    # 11eme label alors que n_symbols=10) declenche l'erreur.
    label_to_id: Dict[object, int] = {}
    ids: list = []
    for s in states:
        if s not in label_to_id:
            if len(label_to_id) >= n_symbols:
                raise ValueError(
                    f"More unique states (>={n_symbols + 1}) than n_symbols ({n_symbols})"
                )
            label_to_id[s] = len(label_to_id)
        ids.append(label_to_id[s])

    W = transition_graph(ids, n_symbols, laplace_smoothing=laplace_smoothing)

    # Valeurs de f sur tous les noeuds du vocabulaire.
    f_vals = np.array([state_function(i) for i in range(n_symbols)], dtype=int)

    # Pour chaque noeud x : compter les voisins y ou W[x, y] > 0 et f(y) != f(x).
    sensitivity = np.zeros(n_symbols, dtype=int)
    for x in range(n_symbols):
        neighbors = np.where(W[x] > 0)[0]
        f_x = f_vals[x]
        sensitivity[x] = int(np.sum(f_vals[neighbors] != f_x))
    return sensitivity


# --------------------------------------------------------------------------- #
#  Distribution resumee                                                         #
# --------------------------------------------------------------------------- #
def sensitivity_distribution(
    states: Sequence,
    n_symbols: int,
    state_function: Callable[[int], int],
    *,
    laplace_smoothing: float = 1e-9,
) -> Dict[str, float]:
    """Statistiques resumees de la sensibilite locale sur les noeuds visites.

    Retourne un dict avec ``max``, ``mean``, ``std``, ``p95`` (95e
    centile), ``n_visited`` (nombre de noeuds effectivement visites dans
    ``states``, pas forcement tous les ``n_symbols``).
    """
    s = local_sensitivity(states, n_symbols, state_function, laplace_smoothing=laplace_smoothing)

    visited = set()
    for st in states:
        # Encodage rapide (memes regles que local_sensitivity).
        # Note : on ne peut pas reutiliser le label_to_id ici sans le
        # reconstruire, donc on encode separement. Acceptable car
        # ``states`` est borne par la trajectoire (<= 10^5 tokens
        # typiquement).
        visited.add(st)

    visited_ids: list = []
    label_to_id: Dict[object, int] = {}
    for st in visited:
        if st not in label_to_id:
            label_to_id[st] = len(label_to_id)
        visited_ids.append(label_to_id[st])

    s_visited = s[visited_ids] if visited_ids else s
    return {
        "max": float(np.max(s_visited)) if s_visited.size else 0.0,
        "mean": float(np.mean(s_visited)) if s_visited.size else 0.0,
        "std": float(np.std(s_visited)) if s_visited.size else 0.0,
        "p95": float(np.percentile(s_visited, 95)) if s_visited.size else 0.0,
        "n_visited": int(len(visited_ids)),
    }


# --------------------------------------------------------------------------- #
#  Test de la conjecture type-Huang ICT                                        #
# --------------------------------------------------------------------------- #
def huang_conjecture_test(
    states: Sequence,
    n_symbols: int,
    state_function: Callable[[int], int],
    *,
    proxy_degree_fn: Callable[[Sequence, int], float] | None = None,
    laplace_smoothing: float = 1e-9,
) -> Dict[str, object]:
    """Teste la conjecture ``s_max(f) >= sqrt(deg_proxy(f))``.

    La conjecture ICT-15b transposee de Huang 2019 : la sensibilite
    maximale d'une fonction d'etat ``f`` sur le graphe de transition
    Markovien est au moins egale a la racine carree du degre d'un
    "proxy polynomial" -- degre que l'on peut operatoinnaliser comme le
    degre **moyen** du voisinage du graphe (les voisins les plus proches
    dans le graphe jouent le role des axes de l'hypercube).

    Parametres :
      - ``states``, ``n_symbols``, ``state_function`` : cf.
        :func:`local_sensitivity`.
      - ``proxy_degree_fn`` : callable optionnel ``(states, n_symbols)
        -> float`` estimant ``deg_proxy(f)``. Si ``None`` (defaut), on
        utilise le degre moyen du voisinage ``np.mean(W.sum(axis=1))``
        comme proxy -- c'est l'operationalisation **la plus
        conservatrice** (elle borne la sensibilite par le degre local).

    Retourne un dict avec ``s_max``, ``deg_proxy``, ``threshold`` (le
    second membre de l'inegalite), ``ratio`` (``s_max / threshold``),
    ``verdict`` (``"consistent"`` si ``s_max >= threshold``,
    ``"inconsistent"`` sinon, ``"inconclusive"`` si la trajectoire est
    trop courte pour etre significative -- moins de ``n_symbols``
    transitions observees).
    """
    s = local_sensitivity(states, n_symbols, state_function, laplace_smoothing=laplace_smoothing)
    s_max = int(np.max(s))

    if proxy_degree_fn is None:
        # Proxy par defaut : degre moyen du voisinage (= mean degree of W).
        W = transition_graph(states, n_symbols, laplace_smoothing=laplace_smoothing)
        deg_proxy = float(np.mean(W.sum(axis=1)))
    else:
        deg_proxy = float(proxy_degree_fn(states, n_symbols))

    threshold = float(np.sqrt(max(deg_proxy, 0.0)))

    # Garde-fou : trajectoire trop courte -> verdict "inconclusive".
    # Heuristique : si on a observe moins de 2 * n_symbols transitions,
    # la distribution de la sensibilite est sousechantillonnee.
    n_transitions = max(0, len(states) - 1)
    n_obs = len(set(states))
    if n_transitions < 2 * n_symbols or n_obs < 2:
        verdict = "inconclusive"
    elif s_max >= threshold:
        verdict = "consistent"
    else:
        verdict = "inconsistent"

    return {
        "s_max": s_max,
        "deg_proxy": deg_proxy,
        "threshold": threshold,
        "ratio": float(s_max) / threshold if threshold > 0 else float("inf"),
        "n_transitions": n_transitions,
        "n_visited": n_obs,
        "verdict": verdict,
    }
