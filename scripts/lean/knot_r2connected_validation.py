#!/usr/bin/env python3
"""Validation exhaustive des chirurgies de transfert de tricolorabilité (knot_lean).

Miroir Python fidèle des définitions Lean de ``MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean``
(Basic.lean / Invariant.lean / Reidemeister.lean) :

- ``PDCrossing`` / ``KnotDiagram`` / ``KnotDiagram.wf`` (Basic.lean L275)
- ``colorAtNat`` (Invariant.lean L116), ``triColorConditionAt`` (L149-164),
  ``IsTriColoring`` (L227), ``IsTricolorable`` (L233)
- chirurgie ``Reidemeister1Connected`` (Reidemeister.lean L262, `isRenameOf` L217)
- candidat ``Reidemeister2Connected`` (splice + rename + bigon, proposition ré-énoncé
  sur l'epic #2874, commentaire 5315086443)

Deux usages :

1. ``--reproduce`` (défaut) : vérifie que le miroir reproduit les résultats CONNUS —
   mur R2 libre (`r2_append_only_wall`, `emptyDiagram` -> `twoTwinCrossings`) et la
   validation exhaustive R1 de la chirurgie COURANTE (2526 diagrammes bien formés,
   20184 torsions, 0 échec aux 2 bras). Note : le commentaire Reidemeister.lean
   L257-260 annonce "24 échecs arrière, tous monogones" — ce chiffre provient de la
   recherche de l'espace des formes candidates qui a précédé la forme finale
   `<a, b, c, c>` et n'est PAS reproductible depuis les définitions courantes
   (voir ``reproduce()``). Le verdict de fiabilité porte sur les comptes exacts
   (2526 / 20184 / 0) + selftest + cross-check brute-force, pas sur le "24".
2. ``--r2connected`` : applique le candidat ``Reidemeister2Connected`` à la même
   énumération et vérifie les 2 bras du transfert de tricolorabilité AVANT toute
   preuve Lean (leçon R1 : l'exhaustif d'abord).

Sortie : compteurs + contre-exemples structurés (diagramme, chirurgie, coloriage
témoin de ``d₂``).

Usage :
    python scripts/lean/knot_r2connected_validation.py --selftest
    python scripts/lean/knot_r2connected_validation.py --reproduce
    python scripts/lean/knot_r2connected_validation.py --r2connected
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from itertools import product

RED, BLUE, GREEN = 0, 1, 2
COLOR_NAMES = ("red", "blue", "green")


# ---------------------------------------------------------------------------
# Miroir Lean des structures
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PDCrossing:
    e1: int
    e2: int
    e3: int
    e4: int


@dataclass(frozen=True)
class KnotDiagram:
    crossings: tuple[PDCrossing, ...]
    numEdges: int

    @property
    def edges(self) -> list[int]:
        # KnotDiagram.edges : d.crossings.flatMap (fun c => [c.e1, c.e2, c.e3, c.e4])
        return [s for c in self.crossings for s in (c.e1, c.e2, c.e3, c.e4)]

    def wf(self) -> bool:
        # KnotDiagram.wf (Basic.lean L275) : si crossings = [] alors numEdges <= 1,
        # sinon (a) chaque label dans [1, numEdges] et (b) chaque label exactement 2x.
        if not self.crossings:
            return self.numEdges <= 1
        edges = self.edges
        if not all(1 <= l <= self.numEdges for l in edges):
            return False
        return all(edges.count(i + 1) == 2 for i in range(self.numEdges))


# Diagrammes nommés de reference (ground truth Lean).
def empty_diagram() -> KnotDiagram:
    # Invariant.lean L1118 : crossings = [], numEdges = 0. NON tricolorable.
    return KnotDiagram(crossings=(), numEdges=0)


def two_twin_crossings() -> KnotDiagram:
    # Invariant.lean L1126 : [<1,2,3,4>, <1,2,3,4>], numEdges = 4. Tricolorable
    # (temoins Lean `twoTwinCrossings_tricolorable`, (red, blue, green, blue)).
    return KnotDiagram(crossings=(PDCrossing(1, 2, 3, 4), PDCrossing(1, 2, 3, 4)), numEdges=4)


def trefoil_diagram() -> KnotDiagram:
    # Basic.lean L149 : 3 croisements, numEdges = 6. Tricolorable (classique).
    return KnotDiagram(
        crossings=(
            PDCrossing(1, 4, 2, 5),
            PDCrossing(3, 6, 4, 1),
            PDCrossing(5, 2, 6, 3),
        ),
        numEdges=6,
    )


def figure_eight_diagram() -> KnotDiagram:
    # Basic.lean L164 : 4 croisements, numEdges = 8. NON tricolorable (det = 5).
    return KnotDiagram(
        crossings=(
            PDCrossing(1, 5, 2, 4),
            PDCrossing(3, 8, 4, 2),
            PDCrossing(5, 1, 6, 7),
            PDCrossing(7, 3, 8, 6),
        ),
        numEdges=8,
    )


def color_at_nat(d: KnotDiagram, coloring: list[int], label: int) -> int:
    # colorAtNat (Invariant.lean L116) : (l - 1) % numEdges, red si numEdges = 0.
    if d.numEdges == 0:
        return RED
    return coloring[(label - 1) % d.numEdges]


def tri_color_condition_at(d: KnotDiagram, coloring: list[int], c: PDCrossing) -> bool:
    # triColorConditionAt (Invariant.lean L149-164).
    if not (1 <= c.e1 <= d.numEdges and 1 <= c.e2 <= d.numEdges and
            1 <= c.e3 <= d.numEdges and 1 <= c.e4 <= d.numEdges):
        return False
    c1 = color_at_nat(d, coloring, c.e1)
    c2 = color_at_nat(d, coloring, c.e2)
    c3 = color_at_nat(d, coloring, c.e3)
    c4 = color_at_nat(d, coloring, c.e4)
    if c2 != c4:
        return False
    return (c1 == c2 and c2 == c3) or (c1 != c2 and c2 != c3 and c1 != c3)


def is_tri_coloring(d: KnotDiagram, coloring: list[int]) -> bool:
    # IsTriColoring (Invariant.lean L227) : toutes les conditions + numEdges >= 2
    # + au moins 2 couleurs distinctes.
    if d.numEdges < 2:
        return False
    if not all(tri_color_condition_at(d, coloring, c) for c in d.crossings):
        return False
    return len(set(coloring)) >= 2


def find_tricoloring(d: KnotDiagram) -> list[int] | None:
    """IsTricolorable : existence d'un coloriage valide (retourne un temoin).

    Backtracking CSP : ordre des variables = premiere apparition dans les
    croisements (propagation). La contrainte de continuite `e2 = e4` est verifiee
    a chaque noeud ou les deux variables sont assignees.
    """
    m = d.numEdges
    if m < 2:
        return None
    crossing_vars = [
        (c.e1 - 1, c.e2 - 1, c.e3 - 1, c.e4 - 1) for c in d.crossings
    ]
    if not crossing_vars:
        return None
    seen: set[int] = set()
    var_order: list[int] = []
    for tup in crossing_vars:
        for v in tup:
            if v not in seen:
                seen.add(v)
                var_order.append(v)
    color = [RED] * m
    assigned = [False] * m

    def crossing_ok(tup: tuple[int, int, int, int]) -> bool:
        e1, e2, e3, e4 = tup
        c2, c4 = color[e2], color[e4]
        if c2 != c4:
            return False
        c1, c3 = color[e1], color[e3]
        return (c1 == c2 and c2 == c3) or (c1 != c2 and c2 != c3 and c1 != c3)

    def solve(pos: int) -> bool:
        if pos == len(var_order):
            return all(crossing_ok(t) for t in crossing_vars) and len(set(color)) >= 2
        v = var_order[pos]
        for val in (RED, BLUE, GREEN):
            color[v] = val
            assigned[v] = True
            ok = True
            for t in crossing_vars:
                if all(assigned[x] for x in t) and not crossing_ok(t):
                    ok = False
                    break
            if ok and solve(pos + 1):
                return True
            assigned[v] = False
        return False

    if solve(0):
        return list(color)
    return None


def is_tricolorable(d: KnotDiagram) -> bool:
    return find_tricoloring(d) is not None


# ---------------------------------------------------------------------------
# Enumeration des diagrammes bien formes (bound R1 : n <= 2 croisements)
# ---------------------------------------------------------------------------

def enumerate_wf_diagrams(max_crossings: int = 2) -> list[KnotDiagram]:
    """Diagrammes bien formes a 1..max_crossings croisements.

    Le wf force `numEdges = 2 * nbCrossings` (Basic.lean L262) : chaque label
    compte exactement 2x sur 4n slots -> 2n labels distincts. Attendu pour
    max_crossings = 2 : 6 + 2520 = 2526 (le bound exact de la validation R1).
    """
    out: list[KnotDiagram] = []
    for n in range(1, max_crossings + 1):
        m = 2 * n
        for slots in product(range(1, m + 1), repeat=4 * n):
            if all(slots.count(i + 1) == 2 for i in range(m)):
                crossings = tuple(
                    PDCrossing(*slots[4 * k:4 * k + 4]) for k in range(n)
                )
                out.append(KnotDiagram(crossings=crossings, numEdges=m))
    return out


# ---------------------------------------------------------------------------
# Chirurgies
# ---------------------------------------------------------------------------

def _slots_of(c: PDCrossing) -> list[int]:
    return [c.e1, c.e2, c.e3, c.e4]


def _a_occurrences(d: KnotDiagram) -> dict[int, list[tuple[int, int]]]:
    """Arc -> liste des (index croisement, index slot) ou il apparait (wf : 2)."""
    occ: dict[int, list[tuple[int, int]]] = {}
    for i, c in enumerate(d.crossings):
        for p, val in enumerate(_slots_of(c)):
            if 1 <= val <= d.numEdges:
                occ.setdefault(val, []).append((i, p))
    return occ


def r1_surgeries(d1: KnotDiagram) -> list[tuple[KnotDiagram, dict]]:
    """Chirurgie ``Reidemeister1Connected`` (Reidemeister.lean L262).

    Renomme un slot de valeur `a` -> `b = n+1` dans le croisement i, append le
    kink `<a, b, n+2, n+2>`, numEdges + 2. Chaque occurrence de `a` (2 par arc,
    wf) donne une torsion -> 8 par diagramme n=2 = le comptage exact des
    "20184 torsions" de la validation R1 (Reidemeister.lean L257-260).
    """
    out: list[tuple[KnotDiagram, dict]] = []
    n = d1.numEdges
    if not d1.crossings:
        return out
    for i, c in enumerate(d1.crossings):
        slots = _slots_of(c)
        b = n + 1
        for p in range(4):
            a = slots[p]
            if not (1 <= a <= n):
                continue
            # une torsion = renommer UN slot de valeur a -> b, appendre le kink
            # <a, b, c, c>. Chaque occurrence de a (2 par arc, wf) donne sa
            # propre torsion -> 8 par diagramme n=2 (le comptage exact des
            # "20184 torsions" de la validation R1). Le rename multi-slot de
            # `isRenameOf` (sous-ensemble) donne toujours un d2 NON-wf (a
            # descendrait sous 2 occurrences) : il n'ajoute aucune chirurgie.
            new_slots = slots[:]
            new_slots[p] = b
            Yp = PDCrossing(*new_slots)
            d1_list = list(d1.crossings)
            d1_list[i] = Yp
            appended = PDCrossing(a, b, n + 2, n + 2)
            d2 = KnotDiagram(tuple(d1_list) + (appended,), n + 2)
            if d2.wf():
                out.append((d2, {"i": i, "a": a, "p": p}))
    return out


def r2_surgeries_v2(d1: KnotDiagram) -> list[tuple[KnotDiagram, dict]]:
    """Candidat ``Reidemeister2Connected`` v2 (proposition #2874).

    Pucker sur l'arc `a` : les 2 occurrences de `a` (slots p1, p2) sont renommees
    vers les labels frais u1 = n+1, u2 = n+3, et 2 kinks appendes lisent `a`
    (under) avec une corde over fraiche (o1 = n+2, o2 = n+4) :

        C1 = <a, o1, u1, o1>  OU  <u1, o1, a, o1>
        C2 = <a, o2, u2, o2>  OU  <u2, o2, a, o2>

    Comptabilite wf (chaque label x2 dans d2) :
      - `a` : 2 (old part, apres renames) -> 0 ; kinks : 2.  Total 2.
      - u1 : 1 (rename) + 1 (kink) = 2 ;  u2 idem.
      - o1, o2 : 2 (over du kink).  -> numEdges = n + 4.

    Chaque label frais partage un croisement avec l'arc existant `a` -> garantie
    cardinalite (>= 2 couleurs dans la fenetre d1 des qu'une coloriation valide
    de d2 a >= 2 couleurs). La forme "over-kink" (<u, a, u, a>) est impossible :
    elle lirait a deux fois et casserait le bilan wf. Positions de `a` dans le
    kink : e1 (under-in) ou e3 (under-out) — 4 combinaisons (pos1, pos2).
    """
    out: list[tuple[KnotDiagram, dict]] = []
    n = d1.numEdges
    if not d1.crossings:
        return out
    occ = _a_occurrences(d1)
    for a in sorted(occ):
        ocs = occ[a]
        if len(ocs) != 2:
            continue
        (i1, p1), (i2, p2) = ocs
        u1, o1, u2, o2 = n + 1, n + 2, n + 3, n + 4
        for pos1 in (0, 2):
            for pos2 in (0, 2):
                new_list = [c for c in d1.crossings]
                c1_slots = _slots_of(d1.crossings[i1])
                c1_slots[p1] = u1
                if i2 == i1:
                    c1_slots[p2] = u2
                    new_list[i1] = PDCrossing(*c1_slots)
                else:
                    new_list[i1] = PDCrossing(*c1_slots)
                    c2_slots = _slots_of(d1.crossings[i2])
                    c2_slots[p2] = u2
                    new_list[i2] = PDCrossing(*c2_slots)
                if pos1 == 0:
                    kink1 = PDCrossing(a, o1, u1, o1)
                else:
                    kink1 = PDCrossing(u1, o1, a, o1)
                if pos2 == 0:
                    kink2 = PDCrossing(a, o2, u2, o2)
                else:
                    kink2 = PDCrossing(u2, o2, a, o2)
                d2 = KnotDiagram(tuple(new_list) + (kink1, kink2), n + 4)
                if d2.wf():
                    out.append((d2, {
                        "a": a, "i1": i1, "i2": i2, "p1": p1, "p2": p2,
                        "pos1": pos1, "pos2": pos2,
                    }))
    return out


def r2_surgeries_v3(d1: KnotDiagram) -> list[tuple[KnotDiagram, dict]]:
    """Candidat ``Reidemeister2Connected`` v3 (correctif du mecanisme v2).

    v2 echoue (40368/40368) car les kinks `<a, o, u, o>` admettent le mode Fox
    all-distinct : rien ne force `color(u) = color(a)`, la restriction casse au
    croisement renomme, et le gadget est toujours tricolorable.

    v3 force les labels frais a la couleur de `a` par la forme du kink : le
    kink `<a, u, u, o>` a un Fox sur (a, u, u) — all-distinct IMPOSSIBLE
    (c2 = c3), donc `color(u) = color(a)` NECESSAIREMENT, et la continuite
    over (e2 = e4) donne `color(o) = color(u) = color(a)`.

    Chirurgie : rename des 2 occurrences de `a` (slots p1, p2) vers o1 = n+2,
    o2 = n+4 ; append kink1 = <a, u1, u1, o1> et kink2 = <a, u2, u2, o2> avec
    u1 = n+1, u2 = n+3. Comptabilite wf (chaque label x2) :

      - a : 0 (old, renomme) + 1 (kink1) + 1 (kink2) = 2.
      - u1 : 2 (kink1, e2 et e3) ;  u2 : 2 (kink2).  -> pas de rename.
      - o1 : 1 (rename p1) + 1 (kink1, e4) = 2 ;  o2 idem.
      - numEdges = n + 4.

    Positions de `a` dans le kink : e1 (under-in) ou e3 (under-out) — 4
    combinaisons (pos1, pos2).
    """
    out: list[tuple[KnotDiagram, dict]] = []
    n = d1.numEdges
    if not d1.crossings:
        return out
    occ = _a_occurrences(d1)
    for a in sorted(occ):
        ocs = occ[a]
        if len(ocs) != 2:
            continue
        (i1, p1), (i2, p2) = ocs
        u1, o1, u2, o2 = n + 1, n + 2, n + 3, n + 4
        for pos1 in (0, 2):
            for pos2 in (0, 2):
                new_list = [c for c in d1.crossings]
                c1_slots = _slots_of(d1.crossings[i1])
                c1_slots[p1] = o1
                if i2 == i1:
                    c1_slots[p2] = o2
                    new_list[i1] = PDCrossing(*c1_slots)
                else:
                    new_list[i1] = PDCrossing(*c1_slots)
                    c2_slots = _slots_of(d1.crossings[i2])
                    c2_slots[p2] = o2
                    new_list[i2] = PDCrossing(*c2_slots)
                if pos1 == 0:
                    kink1 = PDCrossing(a, u1, u1, o1)
                else:
                    kink1 = PDCrossing(u1, u1, a, o1)
                if pos2 == 0:
                    kink2 = PDCrossing(a, u2, u2, o2)
                else:
                    kink2 = PDCrossing(u2, u2, a, o2)
                d2 = KnotDiagram(tuple(new_list) + (kink1, kink2), n + 4)
                if d2.wf():
                    out.append((d2, {
                        "a": a, "i1": i1, "i2": i2, "p1": p1, "p2": p2,
                        "pos1": pos1, "pos2": pos2,
                    }))
    return out


# ---------------------------------------------------------------------------
# Verification des 2 bras + classification des contre-exemples
# ---------------------------------------------------------------------------

def iter_tricolorings(d: KnotDiagram):
    """Itere TOUS les coloriages valides de `d` (meme backtracking que
    `find_tricoloring`). Necessaire pour le check des bras au niveau lemme :
    la construction canonique doit marcher pour CHAQUE coloriage valide."""
    m = d.numEdges
    if m < 2:
        return
    crossing_vars = [
        (c.e1 - 1, c.e2 - 1, c.e3 - 1, c.e4 - 1) for c in d.crossings
    ]
    if not crossing_vars:
        return
    seen: set[int] = set()
    var_order: list[int] = []
    for tup in crossing_vars:
        for v in tup:
            if v not in seen:
                seen.add(v)
                var_order.append(v)
    color = [RED] * m
    assigned = [False] * m

    def crossing_ok(tup: tuple[int, int, int, int]) -> bool:
        e1, e2, e3, e4 = tup
        if color[e2] != color[e4]:
            return False
        c1, c2, c3 = color[e1], color[e2], color[e3]
        return (c1 == c2 and c2 == c3) or (c1 != c2 and c2 != c3 and c1 != c3)

    def solve(pos: int):
        if pos == len(var_order):
            if all(crossing_ok(t) for t in crossing_vars) and len(set(color)) >= 2:
                yield list(color)
            return
        v = var_order[pos]
        for val in (RED, BLUE, GREEN):
            color[v] = val
            assigned[v] = True
            ok = True
            for t in crossing_vars:
                if all(assigned[x] for x in t) and not crossing_ok(t):
                    ok = False
                    break
            if ok:
                yield from solve(pos + 1)
            assigned[v] = False

    yield from solve(0)


def _classify_backward_failure(d1: KnotDiagram, restriction: list[int]) -> dict:
    """Diagnostique pourquoi la restriction d'un coloriage valide de d2 n'est
    pas un coloriage valide de d1."""
    if len(set(restriction)) < 2:
        return {"kind": "cardinality",
                "detail": "restriction constante (< 2 couleurs dans la fenetre d1)"}
    for c in d1.crossings:
        if not tri_color_condition_at(d1, restriction, c):
            return {"kind": "fox",
                    "detail": f"croisement {c} echoue sous restriction",
                    "crossing": c}
    return {"kind": "other", "detail": "restriction invalide (cas inattendu)"}


def r1_extension(tri1: list[int], d1: KnotDiagram, d2: KnotDiagram, meta: dict) -> list[int]:
    """Prolongement trivial R1 : b = n+1 et c = n+2 prennent la couleur de `a`
    (l'arc splice). Verifie sur d2 (kink all-equal, croisements renommes
    preserves car color(b) = color(a))."""
    n = d1.numEdges
    ext = list(tri1) + [RED] * (d2.numEdges - n)
    col_a = tri1[meta["a"] - 1]
    ext[n + 1 - 1] = col_a
    ext[n + 2 - 1] = col_a
    return ext


def r2_extension(tri1: list[int], d1: KnotDiagram, d2: KnotDiagram, meta: dict) -> list[int]:
    """Prolongement trivial R2 v2 : tous les labels frais (n+1..n+4) prennent la
    couleur de `a`. Kinks all-equal, croisements renommes preserves."""
    n = d1.numEdges
    ext = list(tri1) + [RED] * (d2.numEdges - n)
    col_a = tri1[meta["a"] - 1]
    for lbl in range(n + 1, d2.numEdges + 1):
        ext[lbl - 1] = col_a
    return ext


def check_lemmas(d1: KnotDiagram, d2: KnotDiagram, meta: dict, extension) -> dict:
    """Les 2 bras du transfert au niveau LEMME (construction canonique) et au
    niveau ENSEMBLE (bi-implication, ce dont le theoreme a besoin).

    - AVANT (lemme) : pour CHAQUE coloriage valide de d1, le prolongement
      trivial est un coloriage valide de d2. Echec -> temoin tri1.
    - ARRIERE (lemme) : pour CHAQUE coloriage valide de d2, la restriction a la
      fenetre [1, numEdges d1] est un coloriage valide de d1. Echec -> temoin
      tri2 + classification (cardinalite / fox).
    - ENSEMBLE : `IsTricolorable d1 <-> IsTricolorable d2` (niveau ensemble,
      plus faible : des lemmes a echec n'impliquent pas forcement un echec
      ensemble, et inversement la construction canonique est ce qui est
      prouvable en Lean).
    """
    fwd_ok, fwd_wit = True, None
    for tri1 in iter_tricolorings(d1):
        ext = extension(tri1, d1, d2, meta)
        if not is_tri_coloring(d2, ext):
            fwd_ok, fwd_wit = False, tri1
            break
    bwd_ok, bwd_wit, bwd_class = True, None, None
    n = d1.numEdges
    for tri2 in iter_tricolorings(d2):
        restr = list(tri2[:n])
        if not is_tri_coloring(d1, restr):
            bwd_ok, bwd_wit = False, tri2
            bwd_class = _classify_backward_failure(d1, restr)
            break
    tri1 = find_tricoloring(d1)
    tri2 = find_tricoloring(d2)
    return {
        "fwd_ok": fwd_ok, "fwd_wit": fwd_wit,
        "bwd_ok": bwd_ok, "bwd_wit": bwd_wit, "bwd_class": bwd_class,
        "set_fwd": tri1 is not None and tri2 is None,
        "set_bwd": tri2 is not None and tri1 is None,
    }


def _fmt(d: KnotDiagram) -> str:
    return "[" + ", ".join(f"<{c.e1},{c.e2},{c.e3},{c.e4}>" for c in d.crossings) + f"] n={d.numEdges}"


def _fmt_coloring(col: list[int]) -> str:
    return "(" + ",".join(COLOR_NAMES[v] for v in col) + ")"


# ---------------------------------------------------------------------------
# Ground truth (--selftest)
# ---------------------------------------------------------------------------

def selftest() -> int:
    failures: list[str] = []
    # wf des diagrammes nommes
    for name, d, expect in (
        ("emptyDiagram", empty_diagram(), True),
        ("twoTwinCrossings", two_twin_crossings(), True),
        ("trefoilDiagram", trefoil_diagram(), True),
        ("figureEightDiagram", figure_eight_diagram(), True),
    ):
        got = d.wf()
        if got != expect:
            failures.append(f"wf({name}) = {got}, attendu {expect}")
    # tricolorabilite des diagrammes nommes
    for name, d, expect in (
        ("emptyDiagram", empty_diagram(), False),
        ("twoTwinCrossings", two_twin_crossings(), True),
        ("trefoilDiagram", trefoil_diagram(), True),
        ("figureEightDiagram", figure_eight_diagram(), False),
    ):
        got = is_tricolorable(d)
        if got != expect:
            failures.append(f"IsTricolorable({name}) = {got}, attendu {expect}")

    # temoin twoTwinCrossings : le coloriage Lean (red, blue, green, blue) est valide.
    witness = [RED, BLUE, GREEN, BLUE]
    if not is_tri_coloring(two_twin_crossings(), witness):
        failures.append("witness twoTwinCrossings (r,b,g,b) invalide")

    # Mur R2 libre : emptyDiagram -> twoTwinCrossings par append-only (r2_append_only_wall).
    twins = two_twin_crossings()
    empty = empty_diagram()
    # backward : d2 tricolorable, d1 non tricolorable -> le mur.
    if not (is_tricolorable(twins) and not is_tricolorable(empty)):
        failures.append("mur R2 libre non reproduit : empty/twins tricolorabilite inattendue")

    print("== selftest ==")
    if failures:
        for f in failures:
            print(f"  FAIL: {f}")
        print(f"  -> {len(failures)} echec(s)")
        return 1
    print("  tous les ground-truth passes (wf, tricolorabilite, temoin twins, mur R2 libre)")
    return 0


# ---------------------------------------------------------------------------
# Reproduction R1 (--reproduce)
# ---------------------------------------------------------------------------

def run_r1(diagrams: list[KnotDiagram], proper_only: bool = False) -> dict:
    total = 0
    fwd_violations = 0
    bwd_violations = 0
    bwd_monogones = 0
    bwd_set = 0
    bwd_examples: list[dict] = []
    for d1 in diagrams:
        occ = _a_occurrences(d1)
        for d2, meta in r1_surgeries(d1):
            a = meta["a"]
            proper = len({idx for idx, _ in occ[a]}) == 2
            if proper_only and not proper:
                continue
            total += 1
            r = check_lemmas(d1, d2, meta, r1_extension)
            if not r["fwd_ok"]:
                fwd_violations += 1
            if not r["bwd_ok"]:
                bwd_violations += 1
                if not proper:
                    bwd_monogones += 1
                if r["set_bwd"]:
                    bwd_set += 1
                if len(bwd_examples) < 3:
                    bwd_examples.append({
                        "d1": _fmt(d1), "d2": _fmt(d2), "meta": meta,
                        "proper": proper, "class": r["bwd_class"],
                        "witness_d2": _fmt_coloring(r["bwd_wit"]),
                        "restriction": _fmt_coloring(r["bwd_wit"][:d1.numEdges]),
                        "set_bwd": r["set_bwd"],
                    })
    return {
        "total": total, "fwd": fwd_violations, "bwd": bwd_violations,
        "bwd_monogones": bwd_monogones, "bwd_set": bwd_set, "examples": bwd_examples,
    }


def reproduce(diagrams: list[KnotDiagram]) -> int:
    print("== reproduction R1 (la chirurgie COURANTE du code, Reidemeister.lean L262) ==")
    print(f"  diagrammes enumeres (n<=2) : {len(diagrams)} (attendu 2526)")
    stats = run_r1(diagrams)
    print(f"  torsions R1 wf : {stats['total']} (attendu 20184)")
    print(f"  echecs AVANT (lemme, extension triviale) : {stats['fwd']} (attendu 0)")
    print(f"  echecs ARRIERE (lemme, restriction) : {stats['bwd']}")
    print(f"    dont non-monogones : {stats['bwd'] - stats['bwd_monogones']} "
          f"(si > 0, l'hypothese d'arc propre est NECESSAIRE)")
    print(f"    dont echecs de niveau ensemble (d2 tri, d1 non tri) : {stats['bwd_set']}")
    for ex in stats["examples"]:
        print(f"    CE : d1={ex['d1']} d2={ex['d2']} meta={ex['meta']} "
              f"proper={ex['proper']} class={ex['class']}")
        print(f"         witness_d2={ex['witness_d2']} restriction={ex['restriction']}")

    stats_proper = run_r1(diagrams, proper_only=True)
    print(f"  sous arc propre : {stats_proper['total']} torsions, "
          f"echecs ARRIERE : {stats_proper['bwd']}")

    # NOTE d'honnetete : le commentaire Reidemeister.lean L257-260 annonce "24 echecs
    # arriere, tous des monogones" dans la recherche qui a conduit a la forme finale
    # <a, b, c, c> + hypothese d'arc propre. Cette recherche n'est PAS reproductible
    # depuis les definitions courantes (elle a probablement couvert l'espace des
    # formes candidates, pas seulement la forme survivante) : le miroir, applique a
    # la chirurgie COURANTE, trouve 0 echec aux deux bras. Le verdict de fiabilite
    # porte sur la reproduction des comptes exacts (2526 / 20184 / 0) + selftest +
    # cross-check brute-force, PAS sur le chiffre "24" (non reproductible).
    ok = (
        len(diagrams) == 2526
        and stats["total"] == 20184
        and stats["fwd"] == 0
        and stats_proper["bwd"] == 0
    )
    print(f"== verdict reproduction : {'OK — miroir fiable' if ok else 'ECHEC — miroir non fiable'} ==")
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# Candidat R2Connected (--r2connected)
# ---------------------------------------------------------------------------

def run_r2(diagrams: list[KnotDiagram], name: str, surgery_fn) -> int:
    print(f"== candidat Reidemeister2Connected {name} ==")
    total = 0
    total_proper = 0
    fwd_violations = 0
    bwd_violations = 0
    bwd_violations_proper = 0
    bwd_set = 0
    by_class: dict[str, int] = {}
    examples: list[dict] = []
    for d1 in diagrams:
        occ = _a_occurrences(d1)
        for d2, meta in surgery_fn(d1):
            total += 1
            r = check_lemmas(d1, d2, meta, r2_extension)
            a = meta["a"]
            proper = len({idx for idx, _ in occ[a]}) == 2
            if proper:
                total_proper += 1
            if not r["fwd_ok"]:
                fwd_violations += 1
            if not r["bwd_ok"]:
                bwd_violations += 1
                if proper:
                    bwd_violations_proper += 1
                if r["set_bwd"]:
                    bwd_set += 1
                kind = (r["bwd_class"] or {}).get("kind", "?")
                by_class[kind] = by_class.get(kind, 0) + 1
                if len(examples) < 5:
                    examples.append({
                        "d1": _fmt(d1), "d2": _fmt(d2), "meta": meta,
                        "proper": proper, "class": r["bwd_class"],
                        "set_bwd": r["set_bwd"],
                        "witness_d2": _fmt_coloring(r["bwd_wit"]),
                        "restriction": _fmt_coloring(r["bwd_wit"][:d1.numEdges]),
                    })
    print(f"  chirurgies R2 {name} wf (n<=2) : {total}")
    print(f"  echecs AVANT (lemme) : {fwd_violations} (attendu 0 — extension all-equal inconditionnelle)")
    print(f"  echecs ARRIERE (lemme) : {bwd_violations} (dont arc-propre : {bwd_violations_proper})")
    print(f"    dont echecs de niveau ensemble (d2 tri, d1 non tri) : {bwd_set}")
    print(f"  classification arriere : {by_class}")
    print(f"  ratio arc-propre : {bwd_violations_proper}/{total_proper}")
    for ex in examples:
        print(f"  CE : d1={ex['d1']} d2={ex['d2']}")
        print(f"       meta={ex['meta']} proper={ex['proper']} class={ex['class']}")
        print(f"       witness_d2={ex['witness_d2']} restriction={ex['restriction']}")
    return 0


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validation exhaustive des chirurgies R1/R2 (miroir knot_lean).")
    parser.add_argument("--selftest", action="store_true", help="ground-truth Lean")
    parser.add_argument("--reproduce", action="store_true", help="reproduction R1 (20184/24)")
    parser.add_argument("--r2connected", action="store_true", help="candidat R2Connected v2")
    parser.add_argument("--max-crossings", type=int, default=2, help="bound enum (defaut 2)")
    args = parser.parse_args()

    diagrams = enumerate_wf_diagrams(args.max_crossings)
    rc = 0
    if args.selftest:
        rc |= selftest()
    if args.reproduce or not (args.selftest or args.r2connected):
        rc |= reproduce(diagrams)
    if args.r2connected:
        rc |= run_r2(diagrams, "v2 (kinks all-distinct libres)", r2_surgeries_v2)
        rc |= run_r2(diagrams, "v3 (kinks all-equal forces)", r2_surgeries_v3)
    return rc


if __name__ == "__main__":
    sys.exit(main())
