"""
Valeur de Shapley de groupe (valeur de Shapley généralisée)
===========================================================

Évalue un **groupe** de joueurs qui agit comme une seule unité dans un jeu
coopératif à utilité transférable, suivant :

    Flores R., Molina E., Tejada J. (2019). Evaluating groups with the
    generalized Shapley value. 4OR 17(2):141-172.
    doi:10.1007/s10288-018-0380-8

La valeur de groupe est la valeur de Shapley généralisée de Marichal,
Kojadinovic et Fujimoto (2007) : le groupe C est remplacé par un mandataire
unique c dans le jeu fusionné de Lehrer (N_C, v_C), et sa valeur est la
valeur de Shapley de ce mandataire :

    phi_g(C) = sum_{T ⊆ N-C} t!(m-t-1)!/m! * (v(T ∪ C) - v(T)),  m = n - |C| + 1.

Le module fournit :
  - ``merging_game`` : le jeu fusionné (N_C, v_C) comme ``CoalitionGame`` ;
  - ``shapley_group_value`` : formule directe, exacte en ``Fraction`` si demandé ;
  - ``shapley_group_value_monte_carlo`` : estimateur sans biais + erreur-type ;
  - ``connectivity_game`` : jeu de connectivité d'Amer et Gimenez (2004) ;
  - ``GroupValueTable`` : tabulation de v sur les 2^n coalitions et calcul
    vectorisé des valeurs individuelles, de groupe, de la profitabilité, de la
    complémentarité moyenne (définition 3) et du meilleur groupe de taille k.

Convention : les joueurs sont indexés de 0 à n-1, comme dans ``CoalitionGame``.
"""

from __future__ import annotations

from collections import deque
from fractions import Fraction
from itertools import combinations
from math import factorial
from typing import Dict, FrozenSet, Iterable, List, Optional, Sequence, Set, Tuple

import numpy as np

from .coalition_games import CoalitionGame


def _as_group(game: CoalitionGame, group: Iterable[int]) -> FrozenSet[int]:
    """Valide et normalise un groupe de joueurs."""
    g = frozenset(group)
    if not g:
        raise ValueError("Le groupe doit contenir au moins un joueur.")
    if any(i < 0 or i >= game.n_players for i in g):
        raise ValueError(f"Joueur hors de [0, {game.n_players - 1}] dans {sorted(g)}.")
    return g


def _shapley_weight(size: int, n_players: int, exact: bool):
    """Poids s!(n-s-1)!/n! de la formule de Shapley."""
    if exact:
        return Fraction(factorial(size) * factorial(n_players - size - 1), factorial(n_players))
    return factorial(size) * factorial(n_players - size - 1) / factorial(n_players)


def merging_game(game: CoalitionGame, group: Iterable[int]) -> Tuple[CoalitionGame, List[int]]:
    """
    Jeu fusionné de Lehrer (N_C, v_C).

    Les joueurs hors du groupe gardent leur rang relatif (indices 0..m-2) et le
    mandataire du groupe prend l'indice m-1. On a v_C(S) = v(S) si le mandataire
    n'est pas dans S, et v_C(S) = v((S - {c}) ∪ C) sinon.

    Returns:
        (jeu fusionné, correspondance indice réduit -> joueur d'origine) ; la
        correspondance du mandataire vaut -1.
    """
    g = _as_group(game, group)
    rest = [i for i in range(game.n_players) if i not in g]
    proxy = len(rest)

    def v_c(coalition: Set[int]) -> float:
        members = {rest[k] for k in coalition if k != proxy}
        if proxy in coalition:
            members |= g
        return game.value(members)

    names = [game.player_names[i] for i in rest]
    names.append("{" + ", ".join(game.player_names[i] for i in sorted(g)) + "}")
    return CoalitionGame(proxy + 1, v_c, player_names=names), rest + [-1]


def shapley_group_value(game: CoalitionGame, group: Iterable[int], exact: bool = False):
    """
    Valeur de Shapley de groupe phi_g(C), par la formule directe.

    Coût : 2^(n-|C|) évaluations de v, donc réservé aux petits jeux.
    Avec ``exact=True`` les poids sont des ``Fraction`` : le résultat est exact
    dès que v renvoie des entiers ou des ``Fraction``.
    """
    g = _as_group(game, group)
    rest = [i for i in range(game.n_players) if i not in g]
    m = len(rest) + 1
    total = Fraction(0) if exact else 0.0
    for t in range(len(rest) + 1):
        w = _shapley_weight(t, m, exact)
        for tup in combinations(rest, t):
            coalition = set(tup)
            total += w * (game.value(coalition | g) - game.value(coalition))
    return total


def additive_group_value(game: CoalitionGame, group: Iterable[int], exact: bool = False):
    """Valeur additive : somme des valeurs de Shapley individuelles du groupe."""
    g = _as_group(game, group)
    return sum((shapley_group_value(game, {i}, exact=exact) for i in sorted(g)),
               Fraction(0) if exact else 0.0)


def shapley_group_value_monte_carlo(
    game: CoalitionGame,
    group: Iterable[int],
    n_samples: int = 1000,
    seed: Optional[int] = None,
) -> Tuple[float, float]:
    """
    Estimation Monte Carlo de phi_g(C), dans l'esprit de Castro et al. (2009).

    Sous un ordre aléatoire uniforme des m = n-|C|+1 joueurs du jeu fusionné,
    le nombre t de prédécesseurs du mandataire est uniforme sur {0..m-1} et,
    conditionnellement à t, l'ensemble T des prédécesseurs est un t-sous-ensemble
    uniforme de N - C. La moyenne de v(T ∪ C) - v(T) est donc sans biais.

    Returns:
        (estimation, erreur-type de l'estimation)
    """
    if n_samples < 2:
        raise ValueError("n_samples doit valoir au moins 2 pour estimer l'erreur-type.")
    g = _as_group(game, group)
    rest = np.array([i for i in range(game.n_players) if i not in g], dtype=int)
    m = len(rest) + 1
    rng = np.random.default_rng(seed)
    samples = np.empty(n_samples, dtype=float)
    for k in range(n_samples):
        t = int(rng.integers(0, m))
        predecessors = set(rng.permutation(rest)[:t].tolist())
        samples[k] = game.value(predecessors | g) - game.value(predecessors)
    return float(samples.mean()), float(samples.std(ddof=1) / np.sqrt(n_samples))


def connectivity_game(
    n_players: int,
    edges: Iterable[Tuple[int, int]],
    player_names: Optional[List[str]] = None,
) -> CoalitionGame:
    """
    Jeu de connectivité d'Amer et Gimenez (2004) sur un graphe non orienté :
    v(S) = 1 si S induit un sous-graphe connexe et |S| > 1, 0 sinon.
    """
    adjacency: Dict[int, Set[int]] = {i: set() for i in range(n_players)}
    for a, b in edges:
        if a == b:
            continue
        adjacency[a].add(b)
        adjacency[b].add(a)

    def v(coalition: Set[int]) -> int:
        if len(coalition) < 2:
            return 0
        start = next(iter(coalition))
        seen = {start}
        queue = deque([start])
        while queue:
            node = queue.popleft()
            for nxt in adjacency[node]:
                if nxt in coalition and nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        return 1 if len(seen) == len(coalition) else 0

    return CoalitionGame(n_players, v, player_names=player_names)


class GroupValueTable:
    """
    Tabulation de v sur les 2^n coalitions (masques de bits) et calcul vectorisé
    des quantités de Flores, Molina et Tejada.

    Le bit i du masque représente le joueur i. La tabulation coûte 2^n appels à
    la fonction caractéristique ; chaque valeur de groupe coûte ensuite une
    seule passe numpy sur le tableau. Limité à n <= 22.
    """

    MAX_PLAYERS = 22

    def __init__(self, game: CoalitionGame):
        n = game.n_players
        if n > self.MAX_PLAYERS:
            raise ValueError(f"n = {n} > {self.MAX_PLAYERS} : utiliser l'estimateur Monte Carlo.")
        self.game = game
        self.n = n
        self.masks = np.arange(1 << n, dtype=np.int64)
        popcount = np.zeros(1 << n, dtype=np.int64)
        for i in range(n):
            popcount += (self.masks >> i) & 1
        self.popcount = popcount
        self.v = np.array(
            [game.value({i for i in range(n) if (mask >> i) & 1}) for mask in range(1 << n)],
            dtype=float,
        )
        self._weights: Dict[int, np.ndarray] = {}

    # -- utilitaires ---------------------------------------------------------

    def _w(self, n_players: int) -> np.ndarray:
        """Poids de Shapley s!(n-s-1)!/n! indexés par s, pour un jeu à n_players joueurs."""
        if n_players not in self._weights:
            self._weights[n_players] = np.array(
                [_shapley_weight(s, n_players, exact=False) for s in range(n_players)] + [0.0]
            )
        return self._weights[n_players]

    @staticmethod
    def _mask(players: Iterable[int]) -> int:
        mask = 0
        for i in players:
            mask |= 1 << i
        return mask

    def _subsets_avoiding(self, forbidden: int) -> np.ndarray:
        """Masques T tels que T ∩ forbidden = ∅."""
        return self.masks[(self.masks & forbidden) == 0]

    # -- valeurs -------------------------------------------------------------

    def shapley(self) -> np.ndarray:
        """Valeurs de Shapley individuelles phi_i(N, v)."""
        w = self._w(self.n)
        phi = np.empty(self.n)
        for i in range(self.n):
            s = self._subsets_avoiding(1 << i)
            phi[i] = np.sum(w[self.popcount[s]] * (self.v[s | (1 << i)] - self.v[s]))
        return phi

    def group_value(self, group: Iterable[int]) -> float:
        """Valeur de Shapley de groupe phi_g(C; N, v)."""
        c_mask = self._mask(_as_group(self.game, group))
        m = self.n - bin(c_mask).count("1") + 1
        t = self._subsets_avoiding(c_mask)
        return float(np.sum(self._w(m)[self.popcount[t]] * (self.v[t | c_mask] - self.v[t])))

    def additive_value(self, group: Iterable[int], phi: Optional[np.ndarray] = None) -> float:
        """Somme des valeurs de Shapley individuelles des membres du groupe."""
        phi = self.shapley() if phi is None else phi
        return float(sum(phi[i] for i in _as_group(self.game, group)))

    def profitability(self, group: Iterable[int], phi: Optional[np.ndarray] = None) -> float:
        """Profitabilité phi_g(C) - sum_{i in C} phi_i (section 4 de l'article)."""
        return self.group_value(group) - self.additive_value(group, phi)

    def restricted_shapley(self, player: int, removed: Iterable[int]) -> float:
        """phi_i(N - R, v|N-R) : valeur de Shapley de i dans le sous-jeu sans R."""
        r_mask = self._mask(removed)
        if (r_mask >> player) & 1:
            raise ValueError("Le joueur ne peut pas appartenir à l'ensemble retiré.")
        n_sub = self.n - bin(r_mask).count("1")
        s = self._subsets_avoiding(r_mask | (1 << player))
        return float(np.sum(self._w(n_sub)[self.popcount[s]] * (self.v[s | (1 << player)] - self.v[s])))

    def complementarity(self, i: int, j: int) -> float:
        """
        Complémentarité moyenne psi_ij(N, v) (définition 3) :
        somme sur S ⊆ N-{i,j} de s!(n-s-1)!/n! * Delta^2_ij(S).
        """
        return self.group_complementarity({i}, j)

    def group_complementarity(self, group: Iterable[int], i: int) -> float:
        """
        Complémentarité moyenne psi_ci(N_C, v_C) entre le mandataire c du groupe
        et le joueur i dans le jeu fusionné (terme du théorème 2).
        """
        c_mask = self._mask(_as_group(self.game, group))
        if (c_mask >> i) & 1:
            raise ValueError("Le joueur entrant ne doit pas appartenir au groupe.")
        m = self.n - bin(c_mask).count("1") + 1
        bit = 1 << i
        s = self._subsets_avoiding(c_mask | bit)
        delta2 = self.v[s | c_mask | bit] - self.v[s | c_mask] - self.v[s | bit] + self.v[s]
        return float(np.sum(self._w(m)[self.popcount[s]] * delta2))

    # -- recherche du meilleur groupe ---------------------------------------

    def best_groups(self, k: int, top: int = 5) -> List[Tuple[Tuple[int, ...], float]]:
        """Les ``top`` groupes de taille k de plus forte valeur, par énumération exhaustive."""
        ranked = [(grp, self.group_value(grp)) for grp in combinations(range(self.n), k)]
        ranked.sort(key=lambda item: (-item[1], item[0]))
        return ranked[:top]

    def greedy_group(self, k: int) -> List[Tuple[int, float]]:
        """
        Construction gloutonne : à chaque étape, ajoute le joueur qui maximise
        phi_g(C ∪ i). Renvoie la trajectoire (joueur ajouté, valeur du groupe).
        """
        members: List[int] = []
        path: List[Tuple[int, float]] = []
        for _ in range(k):
            candidates = [i for i in range(self.n) if i not in members]
            best = max(candidates, key=lambda i: (self.group_value(members + [i]), -i))
            members.append(best)
            path.append((best, self.group_value(members)))
        return path

    def names(self, group: Sequence[int]) -> List[str]:
        """Noms des joueurs d'un groupe, dans l'ordre donné."""
        return [self.game.player_names[i] for i in group]


__all__ = [
    "merging_game",
    "shapley_group_value",
    "additive_group_value",
    "shapley_group_value_monte_carlo",
    "connectivity_game",
    "GroupValueTable",
]
