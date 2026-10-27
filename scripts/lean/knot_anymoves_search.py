#!/usr/bin/env python3
"""Replique Python de la langue de moves etendue `_any` de knot_lean.

Issue #22359, tranche 2 : la recherche bornee du temoin 11n102 (<= 13
croisements, excursions <= +2) passe par cette replique — precedent #20017
(`knot_r2connected_validation.py`). Chaque verificateur ci-dessous MIRROIR
exactement sa definition Lean dans `Knots/ReidemeisterAny.lean` (canon,
verifyKinkDownAny, verifyBigonDownAny) et `Knots/ReidemeisterMoves.lean`
(verifyR3Fwd) ; les temoins kernel du module servent de vecteurs de test
(`test_knot_anymoves_search.py`).

Sorties :
  - `python knot_anymoves_search.py --selftest` : temoins kernel + refus ;
  - `python knot_anymoves_search.py --search`   : BFS bidirectionnel sur le
    corpus 11n102 (67 departs = plis de 0, 1 ou 2 changements de croisement)
    vers le diagramme trivial, bornes du grain ; rend un temoin (chaine de
    moves `_any` verifiee par la replique) ou le certificat negatif borne
    (comptes d'etats, profondeurs atteintes).
"""

from __future__ import annotations

import argparse
import heapq
import itertools
import json
import random
import sys
from collections import Counter, deque
from typing import Dict, List, Optional, Tuple

Crossing = Tuple[int, int, int, int]
Diagram = Tuple[Tuple[Crossing, ...], int]  # (crossings, numEdges)

# ---------------------------------------------------------------------------
# Noeud 11n102 (Knots/Lidman.lean, paragraphe 1) et diagramme trivial.
# ---------------------------------------------------------------------------

KNOT_11N102: Diagram = (
    (
        (4, 2, 5, 1),
        (7, 12, 8, 13),
        (10, 3, 11, 4),
        (2, 11, 3, 12),
        (5, 14, 6, 15),
        (13, 6, 14, 7),
        (17, 20, 18, 21),
        (9, 19, 10, 18),
        (19, 9, 20, 8),
        (15, 22, 16, 1),
        (21, 16, 22, 17),
    ),
    22,
)

UNKNOT: Diagram = ((), 1)  # unknotDiagram : crossings := [], numEdges := 1
EMPTY0: Diagram = ((), 0)


# ---------------------------------------------------------------------------
# Basic.lean : edges, wf
# ---------------------------------------------------------------------------

def edges(crossings: Tuple[Crossing, ...]) -> List[int]:
    out: List[int] = []
    for c in crossings:
        out.extend(c)
    return out


def wf(diagram: Diagram) -> bool:
    crossings, num_edges = diagram
    if not crossings:
        return num_edges <= 1
    es = edges(crossings)
    if len(es) != 4 * len(crossings):
        return False
    counts = Counter(es)
    for label, count in counts.items():
        if count != 2 or not (1 <= label <= num_edges):
            return False
    return len(counts) == num_edges


def normalize(diagram: Diagram) -> Diagram:
    """Classe canonique : les verificateurs `_any` comparent des `canon`, \
    donc l'etat de connectivite est la classe de renommage."""
    c = canon(diagram[0])
    return (c, len(c) * 2)


def num_edges_of(crossings: Tuple[Crossing, ...]) -> int:
    """Dans un diagramme wf, numEdges = max des etiquettes (parite forcee)."""
    return max(edges(crossings), default=0)


# ---------------------------------------------------------------------------
# ReidemeisterAny.lean : canon, subLabel, subLabel2
# ---------------------------------------------------------------------------

def canon(crossings: Tuple[Crossing, ...]) -> Tuple[Tuple[int, int, int, int], ...]:
    """Renumérotation par ordre de premiere apparition (miroir de `canon`)."""
    seen: Dict[int, int] = {}
    out: List[Tuple[int, int, int, int]] = []
    for c in crossings:
        slots: List[int] = []
        for v in c:
            if v not in seen:
                seen[v] = len(seen) + 1
            slots.append(seen[v])
        out.append((slots[0], slots[1], slots[2], slots[3]))
    return tuple(out)


def sub_label(c: Crossing, x: int, y: int) -> Crossing:
    """Remplace toute etiquette x par y dans les quatre slots (`subLabel`)."""
    return tuple(y if v == x else v for v in c)  # type: ignore[return-value]


def sub_label2(c: Crossing, x1: int, y1: int, x2: int, y2: int) -> Crossing:
    """Remplacement double en une passe (`subLabel2`, x1 prioritaire)."""
    out = []
    for v in c:
        if v == x1:
            out.append(y1)
        elif v == x2:
            out.append(y2)
        else:
            out.append(v)
    return tuple(out)  # type: ignore[return-value]


def set_at(lst: Tuple[Crossing, ...], i: int, y: Crossing) -> Tuple[Crossing, ...]:
    """Miroir de `List.set` : remplace l'indice i (inchange si hors borne... \
    non : List.set allonge la liste ; ici i est toujours dans les bornes car \
    enumere par List.range)."""
    return lst[:i] + (y,) + lst[i + 1:]


# ---------------------------------------------------------------------------
# ReidemeisterAny.lean : verifyKinkDownAny, verifyBigonDownAny
# ---------------------------------------------------------------------------

def verify_kink_down_any(D: Diagram, d: Diagram) -> bool:
    """Miroir exact de `verifyKinkDownAny` (D = grand, d = petit)."""
    if not (wf(D) and wf(d)):
        return False
    Dc = D[0]
    if not Dc:
        return False
    K = Dc[-1]
    dc = d[0]
    if not (K[2] == K[3] and len(dc) + 1 == len(Dc)):
        return False
    rest = Dc[:-1]
    if not rest:
        return canon(rest) == canon(dc)
    for i in range(len(rest)):
        M = set_at(rest, i, sub_label(rest[i], K[1], K[0]))
        if canon(M) == canon(dc):
            return True
    return False


def verify_bigon_down_any(D: Diagram, d: Diagram) -> bool:
    """Miroir exact de `verifyBigonDownAny` (D = grand, d = petit)."""
    if not (wf(D) and wf(d)):
        return False
    Dc = D[0]
    if len(Dc) < 2:
        return False
    K2, K1 = Dc[-1], Dc[-2]
    dc = d[0]
    if not (K2[1] == K2[2] and K1[1] == K1[2] and K1[0] == K2[0]
            and len(dc) + 2 == len(Dc)):
        return False
    rest = Dc[:-2]
    a = K2[0]
    if not rest:
        return canon(rest) == canon(dc)
    for i in range(len(rest)):
        M = set_at(rest, i, sub_label2(rest[i], K1[3], a, K2[3], a))
        if canon(M) == canon(dc):
            return True
    return False


# ---------------------------------------------------------------------------
# ReidemeisterMoves.lean : verifyR3Fwd / verifyR3
# ---------------------------------------------------------------------------

def verify_r3_fwd(d: Diagram, d2: Diagram) -> bool:
    """Miroir exact de `verifyR3Fwd` : triple consecutif i, i+1, i+2."""
    if not (wf(d) and wf(d2)):
        return False
    dc, d2c = d[0], d2[0]
    n = len(dc)
    if not (n == len(d2c) and d[1] == d2[1]):
        return False
    for i in range(n):
        if i + 2 >= n:
            continue
        x, y, z = dc[i], dc[i + 1], dc[i + 2]
        if not (y[1] == x[2] and z[0] == y[2] and z[1] == x[3]):
            continue
        nine = [x[0], x[1], y[0], y[3], z[2], z[3], x[2], x[3], y[2]]
        if len(set(nine)) != len(nine):
            continue
        expected = list(dc)
        expected[i] = (y[0], y[3], y[2], x[2])
        expected[i + 1] = (y[2], x[1], z[2], x[3])
        expected[i + 2] = (x[2], x[3], x[0], z[3])
        if tuple(expected) == d2c:
            return True
    return False


def verify_r3(d: Diagram, d2: Diagram) -> bool:
    return verify_r3_fwd(d, d2) or verify_r3_fwd(d2, d)


# ---------------------------------------------------------------------------
# La langue etendue : AnyMove, verifyAnyMove(s)
# ---------------------------------------------------------------------------

MOVE_KINDS = ("r1Any", "r2Any", "r3Any")


def verify_any_move(kind: str, s: Diagram, t: Diagram) -> bool:
    """Miroir exact de `verifyAnyMove` (direction-neutral)."""
    if kind == "r1Any":
        return verify_kink_down_any(t, s) or verify_kink_down_any(s, t)
    if kind == "r2Any":
        return verify_bigon_down_any(t, s) or verify_bigon_down_any(s, t)
    if kind == "r3Any":
        return verify_r3(s, t)
    raise ValueError(kind)


def verify_any_moves(chain: List[Tuple[str, Diagram, Diagram]],
                     start: Diagram, end: Diagram) -> bool:
    """Miroir exact de `verifyAnyMoves` : chaine continue, liens verifies."""
    if not chain:
        return start == end
    (kind, s, t), rest = chain[0], chain[1:]
    return (s == start and verify_any_move(kind, s, t)
            and verify_any_moves(rest, t, end))


# ---------------------------------------------------------------------------
# Generation des voisins (chirurgie montante) + filtre par les verificateurs
# ---------------------------------------------------------------------------

def _kink_up_candidates(d: Diagram):
    """D = d avec un slot a -> b, plus kink terminal <a,b,c,c> ; \
    {b,c} = {n+1,n+2}."""
    dc, n = d[0], d[1]
    for (b, c) in ((n + 1, n + 2), (n + 2, n + 1)):
        K = None  # type: ignore[assignment]
        for i in range(len(dc)):
            base = dc[i]
            for p in range(4):
                a = base[p]
                newc = list(dc)
                mutated = list(base)
                mutated[p] = b
                newc[i] = tuple(mutated)  # type: ignore[arg-type]
                K = (a, b, c, c)
                yield (tuple(newc) + (K,), n + 2)
        if not dc:  # depart vide : kink <p,p,r,r> (labels apparies)
            yield (((1, 1, 2, 2),), 2)
            yield (((2, 2, 1, 1),), 2)


def _bigon_up_candidates(d: Diagram):
    """Bigon montant, derive du verificateur : choisir un croisement i et une \
    etiquette alpha y apparaissant DEUX fois (les deux occurrences dans i) ; \
    scinder les deux occurrences en o1/o2 (frais, ou un cote rattache a \
    alpha) ; appendicer <beta,x,x,o1>,<beta,y,y,o2> avec beta,x,y frais. \
    Depart vide : paire <s,t,t,v>,<s,u,u,v> a etiquettes deux a deux \
    distinctes (o1 = o2 = v force par wf)."""
    dc, n = d[0], d[1]
    if not dc:
        for perm in itertools.permutations((1, 2, 3, 4)):
            s, t, u, v = perm
            yield (((s, t, t, v), (s, u, u, v)), 4)
        return
    beta, x, y, f = n + 1, n + 2, n + 3, n + 4
    for i, base in enumerate(dc):
        for alpha in sorted(set(base)):
            if base.count(alpha) != 2:
                continue
            p, q = [s for s, v in enumerate(base) if v == alpha]
            # o1/o2 ne peuvent etre que {f, alpha} (beta,x,y deja satures a 2
            # dans les demi-bigons ; le meme label deux fois donnerait 4).
            for slot_fresh in (p, q):
                mutated = list(base)
                mutated[slot_fresh] = f
                newc = list(dc)
                newc[i] = tuple(mutated)  # type: ignore[arg-type]
                # K1 porte l'un des {f, alpha}, K2 l'autre (2 affectations)
                yield (tuple(newc) + ((beta, x, x, f), (beta, y, y, alpha)), n + 4)
                yield (tuple(newc) + ((beta, x, x, alpha), (beta, y, y, f)), n + 4)


def _r3_candidates(d: Diagram):
    dc = d[0]
    n = len(dc)
    for i in range(n):
        if i + 2 >= n:
            continue
        x, y, z = dc[i], dc[i + 1], dc[i + 2]
        if not (y[1] == x[2] and z[0] == y[2] and z[1] == x[3]):
            continue
        nine = [x[0], x[1], y[0], y[3], z[2], z[3], x[2], x[3], y[2]]
        if len(set(nine)) != len(nine):
            continue
        out = list(dc)
        out[i] = (y[0], y[3], y[2], x[2])
        out[i + 1] = (y[2], x[1], z[2], x[3])
        out[i + 2] = (x[2], x[3], x[0], z[3])
        yield (tuple(out), d[1])


def neighbors(d: Diagram, max_crossings: int) -> List[Tuple[str, Diagram]]:
    """Tous les voisins `_any` de d (sens UNIQUE de generation) valides au \
    verificateur et dans la borne de croisements. La generation couvre les \
    moves descendants via la symetrie direction-neutral du verificateur."""
    out: List[Tuple[str, Diagram]] = []
    seen: set = set()

    def push(kind: str, cand: Diagram) -> None:
        if cand[0] is not None and len(cand[0]) > max_crossings:
            return
        norm = normalize(cand)
        if norm in seen:
            return
        if verify_any_move(kind, d, cand):
            seen.add(norm)
            out.append((kind, cand))

    # descendants directs : tester kink/bigon down explicites (le verificateur
    # est direction-neutral, la generation montante couvre aussi les montees ;
    # les descentes exigent leur propre enumeration car la source est D).
    Dc = d[0]
    if Dc:
        K = Dc[-1]
        if K[2] == K[3]:
            rest = Dc[:-1]
            if not rest:
                for ne in (0, 1):
                    push("r1Any", ((), ne))
            else:
                for i in range(len(rest)):
                    M = set_at(rest, i, sub_label(rest[i], K[1], K[0]))
                    ne = num_edges_of(M)
                    push("r1Any", (M, ne))
        if len(Dc) >= 2:
            K2, K1 = Dc[-1], Dc[-2]
            if (K2[1] == K2[2] and K1[1] == K1[2] and K1[0] == K2[0]):
                rest = Dc[:-2]
                if not rest:
                    for ne in (0, 1):
                        push("r2Any", ((), ne))
                else:
                    a = K2[0]
                    for i in range(len(rest)):
                        M = set_at(rest, i, sub_label2(rest[i], K1[3], a, K2[3], a))
                        ne = num_edges_of(M)
                        push("r2Any", (M, ne))
    for cand in _kink_up_candidates(d):
        push("r1Any", cand)
    for cand in _bigon_up_candidates(d):
        push("r2Any", cand)
    for cand in _r3_candidates(d):
        push("r3Any", cand)
    return out


# ---------------------------------------------------------------------------
# Corpus 11n102 : plis de changements de croisement (0, 1 ou 2)
# ---------------------------------------------------------------------------

def change_crossing(c: Crossing) -> Crossing:
    """Miroir de `changeCrossing` : e2 <-> e4."""
    return (c[0], c[3], c[2], c[1])


def folds(diagram: Diagram, max_changes: int) -> List[Diagram]:
    out = []
    n = len(diagram[0])
    for k in range(max_changes + 1):
        for combo in itertools.combinations(range(n), k):
            cs = list(diagram[0])
            for i in combo:
                cs[i] = change_crossing(cs[i])
            out.append((tuple(cs), diagram[1]))
    return out


# ---------------------------------------------------------------------------
# BFS bidirectionnel
# ---------------------------------------------------------------------------

def bidirectional_bfs(starts: List[Diagram], targets: List[Diagram],
                      max_crossings: int, node_budget: int,
                      stats: Optional[Dict[str, int]] = None
                      ) -> Optional[Tuple[List[Tuple[str, Diagram, Diagram]], Diagram, Diagram]]:
    """Cherche une chaine `_any` d'un start a un target. Rend la chaine \
    (kind, source, target) dans l'ordre start -> target, ou None si epuise \
    (budget ou fermeture complete) sans rencontre. `stats` recupere les \
    comptes d'etats pour le certificat negatif borne."""
    # parent maps : node -> (kind, from_node)
    fwd_parent: Dict[Diagram, Optional[Tuple[str, Diagram]]] = {}
    bwd_parent: Dict[Diagram, Optional[Tuple[str, Diagram]]] = {}
    fwd_frontier: List[Diagram] = []
    bwd_frontier: List[Diagram] = []
    for s in starts:
        if s not in fwd_parent:
            fwd_parent[s] = None
            fwd_frontier.append(s)
    for t in targets:
        if t not in bwd_parent:
            bwd_parent[t] = None
            bwd_frontier.append(t)
    budget = node_budget

    def expand(frontier: List[Diagram], parent: Dict[Diagram, Optional[Tuple[str, Diagram]]],
               other: Dict[Diagram, Optional[Tuple[str, Diagram]]]
               ) -> Optional[Diagram]:
        nonlocal budget, fwd_frontier, bwd_frontier
        new_frontier: List[Diagram] = []
        for node in frontier:
            for kind, cand in neighbors(node, max_crossings):
                if cand in parent:
                    continue
                parent[cand] = (kind, node)
                budget -= 1
                if cand in other:
                    return cand
                if budget <= 0:
                    return None  # signal budget (distingue par budget <= 0)
                new_frontier.append(cand)
        if frontier is fwd_frontier:
            fwd_frontier = new_frontier
        else:
            bwd_frontier = new_frontier
        return None

    exhausted_fwd = not fwd_frontier
    exhausted_bwd = not bwd_frontier

    def _fill_stats() -> None:
        if stats is not None:
            stats["fwd_states"] = len(fwd_parent)
            stats["bwd_states"] = len(bwd_parent)
            stats["remaining_budget"] = max(0, budget)
            stats["exhausted"] = int(exhausted_fwd and exhausted_bwd)

    while (fwd_frontier or bwd_frontier) and budget > 0:
        # etendre la frontiere la plus petite
        if len(fwd_frontier) <= len(bwd_frontier) and fwd_frontier:
            meet = expand(fwd_frontier, fwd_parent, bwd_parent)
            exhausted_fwd = not fwd_frontier
            if meet is not None or budget <= 0:
                _fill_stats()
                return _rebuild(meet, fwd_parent, bwd_parent, budget)
        elif bwd_frontier:
            meet = expand(bwd_frontier, bwd_parent, fwd_parent)
            exhausted_bwd = not bwd_frontier
            if meet is not None or budget <= 0:
                _fill_stats()
                return _rebuild(meet, fwd_parent, bwd_parent, budget)
        else:
            break
        if exhausted_fwd and exhausted_bwd:
            break
    _fill_stats()
    return None


def _rebuild(meet: Optional[Diagram],
             fwd_parent: Dict[Diagram, Optional[Tuple[str, Diagram]]],
             bwd_parent: Dict[Diagram, Optional[Tuple[str, Diagram]]],
             budget: int):
    if meet is None:
        return None
    # moitie avant : start -> meet
    chain: List[Tuple[str, Diagram, Diagram]] = []
    node = meet
    while fwd_parent[node] is not None:
        kind, prev = fwd_parent[node]  # type: ignore[misc]
        chain.append((kind, prev, node))
        node = prev
    chain.reverse()
    # moitie arriere : meet -> target (les aretes sont direction-neutral)
    node = meet
    while bwd_parent[node] is not None:
        kind, prev = bwd_parent[node]  # type: ignore[misc]
        chain.append((kind, node, prev))
        node = prev
    return chain, chain[0][1], chain[-1][2]


# ---------------------------------------------------------------------------
# A* par pli : la langue est une pile (kink/bigon ne touchent que le dernier
# croisement, R3 preserve l'ordre), donc chaque pli se traite separement et
# l'heuristique ceil(n/2) est admissible (une move retire au plus 2 croisements).
# ---------------------------------------------------------------------------

def astar(start: Diagram, targets: List[Diagram], max_crossings: int,
          node_budget: int) -> Optional[List[Tuple[str, Diagram, Diagram]]]:
    """A* du `start` literal vers un des `targets`. Rend la chaine verifyee \
    (chaque lien l'a ete a l'insertion) ou None a budget epuise."""
    target_norms = {normalize(t) for t in targets}
    start_norm = normalize(start)
    if start_norm in target_norms:
        return []
    INF = 1 << 60
    best: Dict[tuple, int] = {start_norm: 0}
    parent: Dict[tuple, Optional[Tuple[str, Diagram, Diagram]]] = {start_norm: None}
    heap: List[Tuple[int, int, int, Diagram]] = [(len(start[0]) // 2, 0, 0, start)]
    counter = 0
    while heap:
        _, cost, _, d = heapq.heappop(heap)
        nd = normalize(d)
        if cost > best.get(nd, INF):
            continue
        if nd in target_norms:
            chain: List[Tuple[str, Diagram, Diagram]] = []
            node = nd
            while parent[node] is not None:
                kind, s, t = parent[node]  # type: ignore[misc]
                chain.append((kind, s, t))
                node = normalize(s)
            chain.reverse()
            return chain
        if counter >= node_budget:
            return None
        for kind, cand in neighbors(d, max_crossings):
            nc = normalize(cand)
            ncost = cost + 1
            if ncost < best.get(nc, INF):
                best[nc] = ncost
                parent[nc] = (kind, d, cand)
                counter += 1
                heapq.heappush(heap, (ncost + len(cand[0]) // 2, ncost, counter, cand))
    return None


def push_chain(depth: int, seed: int) -> Diagram:
    """Construit un diagramme (likely noue) en remontant du vide par pushes \
    aleatoires seedes — chemin descendant garanti exister (l'inverse du \
    chemin montant)."""
    rng = random.Random(seed)
    d: Diagram = UNKNOT
    for _ in range(depth):
        ups = [(k, c) for k, c in neighbors(d, 64) if len(c[0]) > len(d[0])]
        if not ups:
            break
        _, d = rng.choice(ups)
    return d


# ---------------------------------------------------------------------------
# Selftests : temoins kernel de ReidemeisterAny.lean
# ---------------------------------------------------------------------------

W_NONFRESH_BIG: Diagram = (((4, 1, 4, 2), (1, 2, 3, 3)), 4)
W_NONFRESH_SMALL: Diagram = (((2, 1, 2, 1),), 2)
W_KINK_EMPTY: Diagram = (((1, 1, 2, 2),), 2)
W_BIGON_PAIR: Diagram = (((1, 2, 2, 4), (1, 3, 3, 4)), 4)
W_R1_SRC: Diagram = (((1, 2, 3, 4), (1, 2, 3, 4)), 4)
W_R1_TGT: Diagram = (((1, 2, 3, 4), (5, 2, 3, 4), (1, 5, 6, 6)), 6)


def selftest() -> int:
    failures = []

    def check(name: str, cond: bool) -> None:
        if not cond:
            failures.append(name)

    check("wf 11n102", wf(KNOT_11N102))
    check("wf unknot", wf(UNKNOT))
    check("wf nonFresh big", wf(W_NONFRESH_BIG))
    check("canon nil", canon(()) == ())
    check("canon renomme", canon(((4, 1, 4, 2), (1, 2, 3, 3)))
          == canon(((9, 1, 9, 2), (1, 2, 7, 7))))
    # temoins kernel (ReidemeisterAny.lean paragraphe 5)
    check("kinkDownAny nonFresh", verify_kink_down_any(W_NONFRESH_BIG, W_NONFRESH_SMALL))
    check("bigonDownAny empty", verify_bigon_down_any(W_BIGON_PAIR, EMPTY0))
    check("kinkDownAny degenerate", verify_kink_down_any(W_KINK_EMPTY, EMPTY0))
    check("r1Any chain nonFresh",
          verify_any_moves([("r1Any", W_NONFRESH_BIG, W_NONFRESH_SMALL)],
                           W_NONFRESH_BIG, W_NONFRESH_SMALL))
    check("r2Any witness passes",
          verify_any_move("r2Any", W_BIGON_PAIR, EMPTY0))
    check("r1 historic passes any",
          verify_any_move("r1Any", W_R1_SRC, W_R1_TGT))
    # refus attendus
    check("kinkDownAny refuse silhouette", not verify_kink_down_any(
        (((1, 2, 3, 4),), 4), EMPTY0))
    check("bigonDownAny refuse longueur", not verify_bigon_down_any(
        (((1, 2, 2, 4),), 4), EMPTY0))
    check("wf refuse parite", not wf((((1, 2, 3, 4),), 4)))
    # une descente authentique depuis le kink temoin
    check("voisins du kink degeneres contiennent le vide",
          any(cand == EMPTY0 for _, cand in neighbors(W_KINK_EMPTY, 13)))
    check("voisins de la paire contiennent le vide",
          any(cand == EMPTY0 for _, cand in neighbors(W_BIGON_PAIR, 13)))

    if failures:
        print("SELFTEST FAIL: " + ", ".join(failures))
        return 1
    print("SELFTEST OK: 15/15 (temoins kernel + refus + generation)")
    return 0


# ---------------------------------------------------------------------------
# Recherche du temoin 11n102
# ---------------------------------------------------------------------------

def search(max_crossings: int = 13, node_budget: int = 2_000_000,
           max_changes: int = 2) -> int:
    starts = folds(KNOT_11N102, max_changes)
    targets = [UNKNOT, EMPTY0]
    stats: Dict[str, int] = {}
    print(f"[search] departs={len(starts)} (plis <= {max_changes} changements), "
          f"cibles=trivial, borne={max_crossings} croisements, budget={node_budget}")
    result = bidirectional_bfs(starts, targets, max_crossings, node_budget,
                               stats=stats)
    if result is None:
        kind = "espace EPUISE" if stats.get("exhausted") else "budget epuise (non exhaustif)"
        print(f"[search] AUCUN temoin dans la borne — {kind}")
        print(f"[search] etats: cote noeud {stats['fwd_states']}, cote vide "
              f"{stats['bwd_states']}, budget restant {stats['remaining_budget']}")
        return 2
    chain, d1, d2 = result
    ok = verify_any_moves(chain, d1, d2)
    max_len = max(len(x[1][0]) for x in chain)
    start_len = len(d1[0])
    excursion = max_len - start_len
    report = {
        "witness_found": True,
        "verified_by_replica": ok,
        "start": {"crossings": [list(c) for c in d1[0]], "numEdges": d1[1]},
        "end": {"crossings": [list(c) for c in d2[0]], "numEdges": d2[1]},
        "chain_length": len(chain),
        "max_crossings_along": max_len,
        "excursion": excursion,
        "kinds": [k for k, _, _ in chain],
        "chain": [
            {"kind": k,
             "source": {"crossings": [list(c) for c in s[0]], "numEdges": s[1]},
             "target": {"crossings": [list(c) for c in t[0]], "numEdges": t[1]}}
            for k, s, t in chain
        ],
    }
    print(f"[search] TEMOIN: {len(chain)} maillons, excursion max {excursion:+d}, "
          f"verifie par la replique: {ok}")
    print(json.dumps(report["kinds"]))
    with open("knot_anymoves_witness.json", "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1)
    print("[search] ecrit knot_anymoves_witness.json")
    return 0 if ok else 3


def push_test(depth: int = 8, budget: int = 200_000,
              max_crossings: int = 13) -> int:
    """Valide la capacite de profondeur d'A* : remontee seedee du vide, puis \
    recherche du chemin descendant (qui existe par construction)."""
    failures = 0
    for seed in range(3):
        d = push_chain(depth, seed)
        chain = astar(d, [UNKNOT, EMPTY0], max_crossings, budget)
        if chain is None:
            print(f"[push-test] seed {seed}: ECHEC ({len(d[0])} croisements)")
            failures += 1
            continue
        ok = verify_any_moves(chain, d, chain[-1][2])
        print(f"[push-test] seed {seed}: {len(d[0])} croisements -> "
              f"{len(chain)} maillons, verifie {ok}")
        failures += 0 if ok else 1
    return 1 if failures else 0


def astar_all_folds(max_crossings: int = 13, node_budget: int = 200_000,
                    max_changes: int = 2, per_fold_time_hint: int = 120
                    ) -> int:
    """A* par pli sur le corpus 11n102. Rend le premier temoin trouve (JSON) \
    ou le certificat negatif borne (par pli : etats explores)."""
    import time
    fs = folds(KNOT_11N102, max_changes)
    report: Dict = {"folds": [], "max_crossings": max_crossings}
    for idx, fold in enumerate(fs):
        t0 = time.monotonic()
        chain = astar(fold, [UNKNOT, EMPTY0], max_crossings, node_budget)
        dt = time.monotonic() - t0
        if chain is not None:
            ok = verify_any_moves(chain, fold, chain[-1][2])
            max_len = max(len(x[1][0]) for x in chain) if chain else len(fold[0])
            print(f"[astar] pli #{idx}: TEMOIN {len(chain)} maillons en "
                  f"{dt:.1f}s, excursion {max_len - len(fold[0]):+d}, verifie {ok}")
            report["witness"] = {
                "fold_index": idx,
                "fold": {"crossings": [list(c) for c in fold[0]], "numEdges": fold[1]},
                "chain_length": len(chain),
                "verified_by_replica": ok,
                "chain": [
                    {"kind": k,
                     "source": {"crossings": [list(c) for c in s[0]], "numEdges": s[1]},
                     "target": {"crossings": [list(c) for c in t[0]], "numEdges": t[1]}}
                    for k, s, t in chain
                ],
            }
            with open("knot_anymoves_witness.json", "w", encoding="utf-8") as fh:
                json.dump(report, fh, indent=1)
            print("[astar] ecrit knot_anymoves_witness.json")
            return 0
        print(f"[astar] pli #{idx}: aucun temoin (budget {node_budget}, {dt:.1f}s)")
        report["folds"].append(idx)
    report["negative_certificate"] = {
        "kind": "budget-bounded",
        "per_fold_budget": node_budget,
        "folds_explored": len(fs),
    }
    with open("knot_anymoves_witness.json", "w", encoding="utf-8") as fh:
        json.dump(report, fh, indent=1)
    print("[astar] certificat negatif borne ecrit (knot_anymoves_witness.json)")
    return 2


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest", action="store_true")
    parser.add_argument("--search", action="store_true")
    parser.add_argument("--push-test", action="store_true")
    parser.add_argument("--astar", action="store_true")
    parser.add_argument("--max-crossings", type=int, default=13)
    parser.add_argument("--node-budget", type=int, default=2_000_000)
    parser.add_argument("--max-changes", type=int, default=2)
    args = parser.parse_args()
    if args.selftest:
        return selftest()
    if args.search:
        return search(args.max_crossings, args.node_budget, args.max_changes)
    if args.push_test:
        return push_test(max_crossings=args.max_crossings)
    if args.astar:
        return astar_all_folds(args.max_crossings, args.node_budget, args.max_changes)
    parser.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
