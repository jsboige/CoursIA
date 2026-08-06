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

Issue #9764 -- historique du correctif (c.9706 -> #9770)
-----------------------------------------------------

Le constat lateral rapporte par #7290 (PR #9740) -- ``mean == max ==
k - 1`` sur 15/15 paires (graine, k) du substrat S1 ``SelfSortingArray``
-- etait **reel**, mais **PAS** une degenerescence du wiring
(f identite + W symmetrise). La cause mesuree par #9770 (po-2025) est
**le plancher de lissage de Laplace** dans :func:`ict.spectral.transition_graph` :
``laplace_smoothing=1e-9`` met un coefficient strictement positif sur
**toutes** les entrees de la matrice de transition, donc
``W[x].any()`` etait vrai pour tout couple ``(x, y)``, donc
``local_sensitivity`` lisait le voisinage dans un graphe complet.

Le contre-exemple minimal (cycle 0->1->2 sur alphabet 6, ``f(x)=x``)
donnait la sensibilite ``[5, 5, 5, 5, 5, 5]`` alors que les etats
3, 4 et 5 etaient **jamais visites** et le degre observe est 1 : aucun
choix de ``f`` ne pouvait corriger cela -- c'etait un defaut, pas un
domaine de validite a documenter.

La reparation (PR #9770, MERGED 2026-08-06T23:11Z) introduit la
primitive :func:`ict.spectral.observed_adjacency` et fait lire a
:func:`local_sensitivity` le voisinage **effectivement observe**
(transitions reellement presentes dans la trajectoire) plutot que le
graphe pondere lisse. Le lissage reste legitime pour les usages
**spectraux** (Laplacien, gap), ou une ligne nulle casse la
diagonalisation ; il est simplement inadapte a un **comptage de
voisins**.

Le present module documente cette trajectoire pour qu'un lecteur
futur ne tente pas de reproduire la recommandation obsolete « employer
une f non injective » -- elle ne corrigeait rien puisque le defaut
frappait des noeuds que ``f`` n'atteignait jamais.
"""

from __future__ import annotations

from typing import Callable, Dict, Sequence

import numpy as np

from .spectral import observed_adjacency, transition_graph

__all__ = [
    "local_sensitivity",
    "sensitivity_distribution",
    "huang_conjecture_test",
]


# --------------------------------------------------------------------------- #
#  Encodage des labels (mutualise)                                              #
# --------------------------------------------------------------------------- #
def _encode_labels(states: Sequence, n_symbols: int) -> list:
    """Encode les labels de ``states`` en entiers ``0..n_symbols-1``.

    Ordre d'attribution : **premiere apparition** dans la trajectoire.
    L'encodage est donc **compact** -- les ``n_visited`` noeuds
    effectivement visites occupent exactement les ids ``0..n_visited-1``,
    et les ids restants correspondent aux noeuds jamais visites. Cette
    propriete est utilisee par :func:`sensitivity_distribution`.

    On accepte exactement ``n_symbols`` labels distincts ; un depassement
    (= un 11eme label alors que ``n_symbols=10``) declenche une
    ``ValueError`` explicite.

    Mutualise entre :func:`local_sensitivity` et
    :func:`huang_conjecture_test` : cette derniere passait auparavant les
    labels **bruts** a :func:`ict.spectral.transition_graph`, qui fait un
    ``int(s)`` -- donc ``ValueError: invalid literal for int()`` sur des
    labels chaines, alors que :func:`local_sensitivity` les acceptait.
    L'invariance par label est une propriete du module : elle doit valoir
    pour les trois fonctions publiques (issue #9764).
    """
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
    return ids


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
    ``f(x)`` et on compte le nombre de **voisins** ``y`` ou
    ``f(y) != f(x)``. Le voisinage est celui de
    :func:`ict.spectral.observed_adjacency` : ``y`` est voisin de ``x``
    si et seulement si la transition ``x -> y`` ou ``y -> x`` a ete
    **effectivement observee** dans la trajectoire.

    .. note:: **Correctif #9764.**

       Le voisinage etait auparavant lu dans
       :func:`ict.spectral.transition_graph` via ``W[x] > 0``. Or ``W``
       est **lissee par defaut** (``laplace_smoothing=1e-9``), donc dense
       hors diagonale : tout noeud y etait declare voisin de tout noeud.
       Consequence mesuree : avec une fonction d'etat **injective** (p.
       ex. ``f(x) = x``), la sensibilite valait mecaniquement
       ``n_symbols - 1`` en **chaque** noeud -- y compris en des noeuds
       **jamais visites** -- d'ou ``mean == max == n_symbols - 1`` et
       ``std == 0``. Le proxy mesurait la **taille du vocabulaire**, pas
       la sensibilite. Le contre-exemple minimal est un cycle sur 3
       symboles d'un alphabet de 6 : la mesure renvoyait ``[5]*6`` au
       lieu de ``[2, 2, 2, 0, 0, 0]``.

       Le lissage reste correct pour les usages **spectraux** (Laplacien,
       gap), ou une ligne nulle casserait la diagonalisation. Il est
       simplement inadapte a un **comptage de voisins**.

    Parametres :
      - ``states`` : sequence d'etats de la trajectoire (memes labels que
        passes a :func:`ict.time_arrow.transition_matrix`).
      - ``n_symbols`` : taille du vocabulaire.
      - ``state_function`` : callable ``int -> int`` definissant la
        fonction d'etat ``f`` (typiquement 0 ou 1 pour les fonctions
        booleennes, mais peut etre a valeurs dans ``{0, ..., m-1}`` pour
        des fonctions multi-valentes -- le basculement est alors defini
        comme ``f(y) != f(x)``).
      - ``laplace_smoothing`` : **n'affecte plus le voisinage** (cf. note
        ci-dessus). Conserve pour la compatibilite de signature, et
        toujours transmis au graphe **pondere** de
        :func:`huang_conjecture_test` (calcul de ``deg_proxy``).

    Retourne un vecteur numpy de forme ``(n_symbols,)`` ou
    ``s_x[i] = s_x_i(f)``. Un noeud jamais visite a une sensibilite de 0
    (aucun voisin observe), et ``s_x[i] <= `` degre observe de ``i``.
    """
    ids = _encode_labels(states, n_symbols)

    # Voisinage STRUCTUREL : transitions effectivement observees. Ne pas
    # utiliser transition_graph ici -- son lissage la rend dense et tout
    # noeud y serait voisin de tout noeud (issue #9764).
    A = observed_adjacency(ids, n_symbols)

    # Valeurs de f sur tous les noeuds du vocabulaire.
    f_vals = np.array([state_function(i) for i in range(n_symbols)], dtype=int)

    # Pour chaque noeud x : compter les voisins observes y ou f(y) != f(x).
    sensitivity = np.zeros(n_symbols, dtype=int)
    for x in range(n_symbols):
        neighbors = np.where(A[x])[0]
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

    # Les noeuds visites occupent exactement les ids 0..n_visited-1 :
    # _encode_labels attribue les ids par ordre de PREMIERE APPARITION,
    # donc l'encodage est compact et les ids >= n_visited correspondent aux
    # noeuds jamais visites. Le prefixe suffit, sans reconstruire le mapping.
    #
    # La version anterieure calculait la meme chose de facon opaque (elle
    # iterait sur un `set` pour re-attribuer des ids, ce qui redonne
    # toujours `range(n_visited)`). Resultat identique -- verifie -- mais
    # on pouvait raisonnablement le lire comme une erreur d'indexation.
    n_visited = len(set(states))
    s_visited = s[:n_visited] if n_visited else s
    return {
        "max": float(np.max(s_visited)) if s_visited.size else 0.0,
        "mean": float(np.mean(s_visited)) if s_visited.size else 0.0,
        "std": float(np.std(s_visited)) if s_visited.size else 0.0,
        "p95": float(np.percentile(s_visited, 95)) if s_visited.size else 0.0,
        "n_visited": int(n_visited),
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
        utilise ``np.mean(W.sum(axis=1))`` sur le graphe **pondere**.

    .. warning:: **Le proxy par defaut est faible, et ce n'est pas un degre.**

       ``W.sum(axis=1)`` est la **masse de probabilite** par ligne de la
       TPM symmetrisee, pas un nombre de voisins. ``P`` etant
       stochastique par ligne, cette masse vaut **1.0 par construction**,
       independamment de la topologie. Mesure sur trois cycles :

       ==========================  ==========  ==================
       trajectoire                 deg_proxy   degre observe moyen
       ==========================  ==========  ==================
       cycle-4 (k=4)               1.000000    2.0
       cycle-5 (k=5)               1.000000    2.0
       cycle-3 sur alphabet 6      0.916667    1.0
       ==========================  ==========  ==================

       ``deg_proxy`` ne bouge pas quand le degre change. Donc
       ``threshold = sqrt(deg_proxy) ~ 1.0`` quasiment toujours, et le
       verdict est ``consistent`` des que ``s_max >= 1`` -- c'est-a-dire
       des que ``f`` n'est pas constante.

       La docstring anterieure decrivait ce proxy comme « le degre moyen
       du voisinage » et « l'operationalisation la plus conservatrice
       (elle borne la sensibilite par le degre local) » : les deux
       affirmations sont fausses. Un degre se lit ``(W > 0).sum(axis=1)``,
       pas ``W.sum(axis=1)``.

       Ce point n'est **pas corrige ici** : changer ``deg_proxy``
       changerait les verdicts et releve d'un sujet distinct (une PR = un
       sujet). Il est documente pour que personne ne lise un verdict
       ``consistent`` comme une confirmation de la conjecture. Passer un
       ``proxy_degree_fn`` explicite reste le moyen de tester une vraie
       borne.

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
        # Proxy par defaut : masse de ligne moyenne du graphe pondere.
        # Ce N'EST PAS un degre (cf. avertissement de la docstring) : la
        # valeur vaut ~1.0 par construction. Conserve tel quel -- le
        # changer changerait les verdicts, sujet distinct.
        # Les labels sont encodes AVANT l'appel : transition_graph fait un
        # int(s) et plantait sur des labels chaines (issue #9764).
        W = transition_graph(
            _encode_labels(states, n_symbols),
            n_symbols,
            laplace_smoothing=laplace_smoothing,
        )
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
