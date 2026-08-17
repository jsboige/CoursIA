#!/usr/bin/env python3
"""Validation exhaustive des chirurgies R3 de transfert de tricolorabilite (knot_lean).

Miroir Python fidele des definitions Lean de ``MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean``
(meme socle que ``knot_r2connected_validation.py`` -- PR #11467, non encore mergee ;
les ~100 lignes de framework communes sont dupliquees ici volontairement : script
preuve autonome, refactor en module commun post-merge).

Deux questions, deux parties :

**Partie A -- le scaffold EXISTANT ``Reidemeister3Determined`` (Reidemeister.lean
main, `isSlotPermOf`).** La chirurgie courante renumerote UN croisement par une
permutation quelconque de ses 4 slots (24 perms). Question laissee ouverte par le
commentaire Lean ("quelles permutations de slots correspondent a de veritables
glissements R3 ... travail futur") : quelles perms preservent la tricolorabilite
aux DEUX bras ? Verdict attendu (analyse + verifie par brute force) : seulement le
sous-groupe de Klein V4 = {identite, swap e1<->e3, swap e2<->e4, les deux} -- car
la condition bornee est (c2 = c4) ^ Fox(c1,c2,c3), Fox est symetrique en ses trois
arguments, donc la condition ne depend que de la paire non-ordonnee {slot2, slot4}
et du triple non-ordonne {slot1, slot2, slot3}. Les 20 autres perms ont des
contre-exemples concrets (numerotes).

**Partie B -- caracterisation COMPLETE des redistributions 2-croisements
(famille AUXILIAIRE, pas le R3 classique).** Une redistribution 2-croisements
reecrit DEUX croisements en reutilisant les MEMES 8 slots (meme multi-ensemble
de labels -> numEdges, wf, autres croisements inchanges). NB honnete : le R3
CLASSIQUE est un move a TROIS croisements (triangle) -- la partie C ; la
famille 2-croisements caracterisee ici est une famille de re-arrangements de
labels plus faible (elle inclut les flips V4 mono-croisement de la partie A).
Le temoin "ouvert sigma1*sigma2 -> sigma2*sigma1" (2 croisements) echoue
(SCENARIO NEGATIF attendu : ce n'est pas un move d'isotopie -- permutations de
brins differentes). Theoreme de reduction (cle de la completude, mutatis
mutandis pour la partie C) : le transfert bi-directionnel sur TOUS les
contextes equivaut a l'EGALITE des ensembles de solutions de la paire :

    transfert (d1 -> d2 et d2 -> d1, pour tout contexte)  <=>  Sat(X, Y) = Sat(X', Y')

ou Sat(P) = {affectations de couleurs aux labels de la paire satisfaisant les
conditions aux 2 croisements}. En effet les autres croisements et la contrainte
">= 2 couleurs" ne voient que le coloriage, identique des deux cotes ; le bras
avant (resp. arriere) pour tout contexte est exactement l'inclusion Sat(P1) <=
Sat(P2) (resp. >=). On enumere donc TOUTES les partitions canoniques des 8
positions en blocs de taille <= 2 (764 partitions = involutions de S8), on
calcule Sat de chacune par force brute (3^L, L <= 8), et on regroupe par
egalite (avec meme multi-ensemble de tailles). Toute paire de patterns
distincts d'un meme groupe = une redistribution transferante VALIDE ; tout le
reste = echec garanti quelque part. Complete par construction.

**Partie C -- le triangle classique R3 (TROIS croisements).** L'espace : 12
slots, 6 arcs de bord (singletons) + 3 arcs internes (paires connectant deux
croisements differents, graphe triangle). Candidat derive a la main
(convention : brin de dessus en position superieure en sortie ; les deux mots
sont le demi-tour de Garside Delta, 2 croisements par brin de chaque cote) :

    sigma1*sigma2*sigma1 : X1 = <a2,a1,g1,g2>  X2 = <a3,g1,g3,b3>  X3 = <g3,g2,b2,b1>
    sigma2*sigma1*sigma2 : Y1 = <a3,a2,h1,h2>  Y2 = <h1,a1,h3,h4>  Y3 = <h2,h4,b2,b3>

(h3 = b1 : le brin haut sort directement apres sigma1'). Chemins de brins
verifyes : a1-g2-b1 / a2-g1-b3 / a3-g3-b2 d'un cote ; a1-h4-b3 / a2-h2-b2 /
a3-h1-b1 de l'autre. VERDICT (verifie) : il existe EXACTEMENT 2 bijections
preservant les tailles (sur 4320 candidates) sous lesquelles Sat(sigma1*
sigma2*sigma1) = Sat(sigma2*sigma1*sigma2) : correspondance interne UNIQUE
g1=(2,5)->(3,8), g2=(3,9)->(7,9), g3=(6,8)->(2,4), bord = 4-cycle a2->b2,
b2->b1, b3->a2, a3 fixe, et {a1, b1} interchangeables (les 2 bijections ne
differant que par cet echange). La chirurgie induite par cette bijection est
le candidat d'enonce Lean Reidemeister3Connected (grain suivant). NEGATIFS
honnêtes : (i) la version "geometrique" (identite des 6 arcs de bord) n'a PAS
Sat egal -- sur NOTRE derivation manuelle des slots, la correspondence doit
permutter 4 des 6 arcs de bord (probable convention over/under dans la
derivation ; l'enonce Lean prendra la bijection trouvee comme definition du
move, sans pretendre au glissement classique) ; (ii) aucun partenaire non
trivial a transport IDENTITE parmi les 15 appariements internes (bord fixe).
Verification concrete : 300 diagrammes wf aleatoires n=5 realisant le
triangle ouvert, chirurgie appliquee, 0 echec attendu. En complement,
fermeture complete : les 10395 appariements parfaits du trefle (n=3)
classes par Sat -- indicatif (le niveau ferme conflate arcs de bord et
internes ; 90 membres dans la classe du trefle).

Temoins concrets : fermeture du braid pur sigma1*sigma2 sur 3 brins
d1 = [<2,1,3,1>, <4,3,4,2>] (wf) et son partenaire sigma2*sigma1 trouve par la
recherche, verifie concretement. Validation concrete additionnelle : toutes les
redistributions valides appliquees a tous les diagrammes wf n <= 2 (+ trefoil n=3),
0 echec attendu.

Sortie : compteurs + verdict + contre-exemples structures.

Usage :
    python scripts/lean/knot_r3connected_validation.py --selftest
    python scripts/lean/knot_r3connected_validation.py --reproduce
    python scripts/lean/knot_r3connected_validation.py --perms
    python scripts/lean/knot_r3connected_validation.py --r3search
    python scripts/lean/knot_r3connected_validation.py --concrete
    python scripts/lean/knot_r3connected_validation.py            # tout
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from itertools import permutations, product

RED, BLUE, GREEN = 0, 1, 2


# ---------------------------------------------------------------------------
# Miroir Lean des structures (identique a knot_r2connected_validation.py)
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
        return [s for c in self.crossings for s in (c.e1, c.e2, c.e3, c.e4)]

    def wf(self) -> bool:
        if not self.crossings:
            return self.numEdges <= 1
        edges = self.edges
        if not all(1 <= l <= self.numEdges for l in edges):
            return False
        return all(edges.count(i + 1) == 2 for i in range(self.numEdges))


def empty_diagram() -> KnotDiagram:
    return KnotDiagram(crossings=(), numEdges=0)


def two_twin_crossings() -> KnotDiagram:
    return KnotDiagram(crossings=(PDCrossing(1, 2, 3, 4), PDCrossing(1, 2, 3, 4)), numEdges=4)


def trefoil_diagram() -> KnotDiagram:
    return KnotDiagram(
        crossings=(
            PDCrossing(1, 4, 2, 5),
            PDCrossing(3, 6, 4, 1),
            PDCrossing(5, 2, 6, 3),
        ),
        numEdges=6,
    )


def figure_eight_diagram() -> KnotDiagram:
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
    if d.numEdges == 0:
        return RED
    return coloring[(label - 1) % d.numEdges]


def cond_colors(c1: int, c2: int, c3: int, c4: int) -> bool:
    # triColorConditionAt sans la conjonction de bornes (les bornes sont une
    # propriete des labels, pas des couleurs -- voir en-tete Partie B).
    if c2 != c4:
        return False
    return (c1 == c2 and c2 == c3) or (c1 != c2 and c2 != c3 and c1 != c3)


def tri_color_condition_at(d: KnotDiagram, coloring: list[int], c: PDCrossing) -> bool:
    if not (1 <= c.e1 <= d.numEdges and 1 <= c.e2 <= d.numEdges and
            1 <= c.e3 <= d.numEdges and 1 <= c.e4 <= d.numEdges):
        return False
    return cond_colors(
        color_at_nat(d, coloring, c.e1), color_at_nat(d, coloring, c.e2),
        color_at_nat(d, coloring, c.e3), color_at_nat(d, coloring, c.e4))


def is_tricolorable(d: KnotDiagram) -> bool:
    # Brute force 3^m : suffisant pour m <= 8 (toutes nos cibles).
    m = d.numEdges
    if m < 2 or not d.crossings:
        return False
    for coloring in product(range(3), repeat=m):
        if len(set(coloring)) < 2:
            continue
        if all(tri_color_condition_at(d, list(coloring), c) for c in d.crossings):
            return True
    return False


def enumerate_wf_diagrams(max_crossings: int = 2) -> list[KnotDiagram]:
    out: list[KnotDiagram] = []
    for n in range(1, max_crossings + 1):
        m = 2 * n
        for slots in product(range(1, m + 1), repeat=4 * n):
            if all(slots.count(i + 1) == 2 for i in range(m)):
                crossings = tuple(PDCrossing(*slots[4 * k:4 * k + 4]) for k in range(n))
                out.append(KnotDiagram(crossings=crossings, numEdges=m))
    return out


def _slots_of(c: PDCrossing) -> list[int]:
    return [c.e1, c.e2, c.e3, c.e4]


def r1_surgeries(d1: KnotDiagram) -> list[tuple[KnotDiagram, dict]]:
    # Copie verbatim de knot_r2connected_validation.py (comptage exact 20184).
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
            new_slots = slots[:]
            new_slots[p] = b
            d1_list = list(d1.crossings)
            d1_list[i] = PDCrossing(*new_slots)
            appended = PDCrossing(a, b, n + 2, n + 2)
            d2 = KnotDiagram(tuple(d1_list) + (appended,), n + 2)
            if d2.wf():
                out.append((d2, {"i": i, "a": a, "p": p}))
    return out


# ---------------------------------------------------------------------------
# Partie A -- permutations de slots mono-croisement (scaffold Reidemeister3Determined)
# ---------------------------------------------------------------------------

# Sous-groupe de Klein V4 en encodage "image" : nouveau = (s[p0], s[p1], s[p2], s[p3]).
# swap e1<->e3 : (2,1,0,3) ; swap e2<->e4 : (0,3,2,1) ; compose : (2,3,0,1).
V4_PERMS = {
    "identite": (0, 1, 2, 3),
    "swap_e1_e3": (2, 1, 0, 3),
    "swap_e2_e4": (0, 3, 2, 1),
    "swap_e1_e3_e2_e4": (2, 3, 0, 1),
}


def apply_perm(c: PDCrossing, p: tuple[int, int, int, int]) -> PDCrossing:
    s = _slots_of(c)
    return PDCrossing(s[p[0]], s[p[1]], s[p[2]], s[p[3]])


def run_perms(diagrams: list[KnotDiagram]) -> int:
    print("== Partie A : Reidemeister3Determined (permutation de slots, 24 perms) ==")
    all_perms = list(permutations(range(4)))
    failures: dict[tuple, list[tuple]] = {p: [] for p in all_perms}
    total_surgeries = 0
    for d1 in diagrams:
        for i, c in enumerate(d1.crossings):
            for p in all_perms:
                if p == (0, 1, 2, 3):
                    continue  # identite : d2 = d1, trivial
                d2_list = list(d1.crossings)
                d2_list[i] = apply_perm(c, p)
                d2 = KnotDiagram(tuple(d2_list), d1.numEdges)
                total_surgeries += 1
                assert d2.wf(), f"wf casse par perm {p} sur {d1}"
                t1, t2 = is_tricolorable(d1), is_tricolorable(d2)
                if t1 != t2:
                    failures[p].append((d1, i, t1, d2, t2))
    survivors = [p for p in all_perms if not failures[p]]
    print(f"   chirurgies testees (hors identite) : {total_surgeries}")
    print(f"   perms universellement valides (0 echec) : {len(survivors)}")
    expected = sorted(V4_PERMS.values())
    ok = sorted(survivors) == expected
    print(f"   == V4 attendu {{id, (e1 e3), (e2 e4), compose}} : {'CONFORME' if ok else 'ECART'}")
    if not ok:
        for p in sorted(survivors):
            print(f"     survivant inattendu : {p}")
    # 3 contre-exemples concrets pour des perms echouantes.
    shown = 0
    for p in all_perms:
        if failures[p] and shown < 3:
            d1, i, t1, d2, t2 = failures[p][0]
            print(f"   contre-exemple perm {p} : d1={_fmt(d1)} tri={t1} "
                  f"-> d2={_fmt(d2)} tri={t2} (croisement {i})")
            shown += 1
    return 0 if ok else 1


# ---------------------------------------------------------------------------
# Partie B -- caracterisation complete des redistributions 2-croisements
# ---------------------------------------------------------------------------

def all_partitions_8() -> list[tuple]:
    """Partitions des positions 0..7 en blocs de taille <= 2 (involutions de S8,
    attendu : 764). Un label de diagramme wf apparait <= 2x dans une paire."""
    results: set[tuple] = set()

    def rec(remaining: list[int], blocks: list[tuple]) -> None:
        if not remaining:
            results.add(tuple(sorted(tuple(sorted(b)) for b in blocks)))
            return
        p = min(remaining)
        rest = [x for x in remaining if x != p]
        rec(rest, blocks + [(p,)])
        for q in rest:
            rec([x for x in rest if x != q], blocks + [(p, q)])

    rec(list(range(8)), [])
    return sorted(results)


def var_order(blocks: tuple) -> list[tuple]:
    # Ordre canonique des variables : tailles decroissantes puis premiere
    # position croissante. C'est la correspondance label <-> variable utilisee
    # pour comparer deux patterns (et pour la realisation concrete).
    return sorted(blocks, key=lambda b: (-len(b), min(b)))


def pattern_sat(blocks: tuple) -> tuple[bool, ...]:
    """Sat(P) : bit par affectation de couleurs aux labels (ordre canonique des
    variables), position 0..3 = slots du croisement X, 4..7 = slots de Y.

    Les bornes 1 <= e_k <= numEdges sont une propriete des LABELS, conservee par
    toute redistribution reutilisant les memes labels : elles sont vraies dans
    d2 si elles l'etaient dans d1, donc n'entrent pas dans la comparaison."""
    order = var_order(blocks)
    pos2var = {p: k for k, b in enumerate(order) for p in b}
    L = len(order)
    bits = []
    for assign in product(range(3), repeat=L):
        col = [assign[pos2var[p]] for p in range(8)]
        bits.append(cond_colors(col[0], col[1], col[2], col[3])
                    and cond_colors(col[4], col[5], col[6], col[7]))
    return tuple(bits)


def size_key(blocks: tuple) -> tuple:
    return tuple(sorted(len(b) for b in blocks))


def build_groups() -> dict[tuple, list[tuple]]:
    patterns = all_partitions_8()
    groups: dict[tuple, list[tuple]] = {}
    for pat in patterns:
        groups.setdefault((size_key(pat), pattern_sat(pat)), []).append(pat)
    return groups


def run_r3search(groups: dict[tuple, list[tuple]]) -> int:
    print("== Partie B : caracterisation complete des redistributions 2-croisements ==")
    n_patterns = sum(len(v) for v in groups.values())
    print(f"   partitions enumeratees (blocs <= 2, involutions S8) : {n_patterns}")
    multi = {k: v for k, v in groups.items() if len(v) > 1}
    n_pairs = sum(len(v) * (len(v) - 1) for v in multi.values())
    print(f"   classes d'equivalence Sat : {len(groups)}, dont {len(multi)} non-triviales")
    # Separation vacu / substantiel : une classe de Sat VIDE ne transfere que
    # trivialement (paire insatisfiable des deux cotes -> tri faux partout).
    vac_multi = {k: v for k, v in multi.items() if not any(k[1])}
    vac_pairs = sum(len(v) * (len(v) - 1) for v in vac_multi.values())
    sub_pairs = n_pairs - vac_pairs
    sub_patterns = sum(len(v) for k, v in multi.items() if any(k[1]))
    print(f"   paires non-triviales VACUES (Sat vide, transfert trivial) : {vac_pairs}")
    print(f"   paires non-triviales SUBSTANTIELLES (Sat non vide) : {sub_pairs} "
          f"(sur {sub_patterns} patterns en classes multi-substantielles)")
    print(f"   redistributions transferantes non-triviales (paires ordonnees) : {n_pairs}")
    # Le fermé sigma1*sigma2 : attendu dans une classe non-triviale SUBSTANTIELLE.
    sig1sig2 = tuple(sorted([(1, 3), (0, 7), (2, 5), (4, 6)]))
    for key, members in groups.items():
        if sig1sig2 in members:
            sat_nonempty = sum(1 for b in key[1] if b)
            print(f"   fermeture sigma1*sigma2 (blocs {{1,3}},{{0,7}},{{2,5}},{{4,6}}) : "
                  f"{len(members)} patterns dans sa classe Sat "
                  f"({sat_nonempty}/{len(key[1])} affectations satisfaisantes)")
            if len(members) < 2 or sat_nonempty == 0:
                print("   ANOMALIE : classe triviale ou vacue pour sigma1*sigma2")
                return 1
            break
    else:
        print("   ANOMALIE : fermeture sigma1*sigma2 introuvable")
        return 1
    return 0


# ---------------------------------------------------------------------------
# Realisation concrete d'une redistribution valide
# ---------------------------------------------------------------------------

def pair_pattern(d: KnotDiagram, i: int, j: int) -> tuple:
    """Partition canonique des 8 positions de la paire (i, j) par label."""
    labels = _slots_of(d.crossings[i]) + _slots_of(d.crossings[j])
    by_label: dict[int, list[int]] = {}
    for pos, lab in enumerate(labels):
        by_label.setdefault(lab, []).append(pos)
    return tuple(sorted(tuple(sorted(v)) for v in by_label.values()))


def redistribute(d: KnotDiagram, i: int, j: int, p1: tuple, p2: tuple) -> KnotDiagram:
    """Concretise la redistribution p1 -> p2 sur la paire (i, j) : la k-ieme
    variable canonique de p1 (un label concret) occupe les positions de la
    k-ieme variable canonique de p2 (correspondance utilisee dans la preuve
    d'egalite Sat)."""
    labels = _slots_of(d.crossings[i]) + _slots_of(d.crossings[j])
    o1, o2 = var_order(p1), var_order(p2)
    label_of_var = [labels[min(b)] for b in o1]  # un label par bloc de p1
    pos2var2 = {p: k for k, b in enumerate(o2) for p in b}
    new8 = [label_of_var[pos2var2[p]] for p in range(8)]
    new_list = list(d.crossings)
    new_list[i] = PDCrossing(*new8[0:4])
    new_list[j] = PDCrossing(*new8[4:8])
    return KnotDiagram(tuple(new_list), d.numEdges)


def run_concrete(diagrams: list[KnotDiagram], groups: dict[tuple, list[tuple]]) -> int:
    print("== Validation concrete : redistributions valides sur tous les diagrammes ==")
    partners: dict[tuple, list[tuple]] = {}
    for members in groups.values():
        for p1 in members:
            partners.setdefault(p1, []).extend(p2 for p2 in members if p2 != p1)
    total = 0
    failures = 0
    targets = diagrams + [trefoil_diagram(), figure_eight_diagram()]
    for d1 in targets:
        n = len(d1.crossings)
        if n < 2:
            continue
        for i in range(n):
            for j in range(i + 1, n):
                p1 = pair_pattern(d1, i, j)
                for p2 in partners.get(p1, []):
                    d2 = redistribute(d1, i, j, p1, p2)
                    total += 1
                    if not d2.wf():
                        print(f"   ECHEC wf : {_fmt(d1)} ({i},{j}) {p1} -> {p2}")
                        failures += 1
                        continue
                    if is_tricolorable(d1) != is_tricolorable(d2):
                        print(f"   ECHEC bras : {_fmt(d1)} ({i},{j}) {p1} -> {p2} "
                              f"=> {_fmt(d2)}")
                        failures += 1
    print(f"   redistributions concretes testees : {total}, echecs : {failures}")
    return 0 if failures == 0 else 1


def run_braid_witness(groups: dict[tuple, list[tuple]]) -> int:
    print("== Temoin braid : fermeture sigma1*sigma2 <-> partenaire recherche ==")
    d1 = KnotDiagram((PDCrossing(2, 1, 3, 1), PDCrossing(4, 3, 4, 2)), 4)
    assert d1.wf(), "fermeture sigma1*sigma2 doit etre wf"
    p1 = pair_pattern(d1, 0, 1)
    found = False
    for members in groups.values():
        if p1 in members:
            found = True
            others = [p for p in members if p != p1]
            print(f"   d1 = {_fmt(d1)} tricolorable={is_tricolorable(d1)}")
            checked = 0
            for p2 in others:
                d2 = redistribute(d1, 0, 1, p1, p2)
                assert d2.wf()
                checked += 1
                if is_tricolorable(d1) != is_tricolorable(d2):
                    print(f"   ECHEC temoin : {p2} => {_fmt(d2)}")
                    return 1
            print(f"   partenaires verifies : {checked}, tous les 2 bras OK")
            break
    if not found:
        print("   ANOMALIE : pattern sigma1*sigma2 absent des groupes")
        return 1
    # Partenaire classique derive a la main : fermeture du braid sigma2*sigma1.
    # Convention (brin du dessus gagne la position superieure en sortie) :
    #   sigma2' = <c, b, k, c>  (brins 2,3 ; brin 2 dessus ; k = arc interne)
    #   sigma1' = <k, a, b, a>  (brins 1,3 deplaces ; brin 1 dessus)
    # avec a=1, b=2, c=4, k=3 -> d2 = [<4,2,3,4>, <3,1,2,1>].
    d2 = KnotDiagram((PDCrossing(4, 2, 3, 4), PDCrossing(3, 1, 2, 1)), 4)
    assert d2.wf(), "fermeture sigma2*sigma1 derivee doit etre wf"
    p2_hand = pair_pattern(d2, 0, 1)
    same_class = any(p2_hand in members for members in groups.values() if p1 in members)
    arms_ok = is_tricolorable(d1) == is_tricolorable(d2)
    print(f"   partenaire classique derive sigma2*sigma1 : {_fmt(d2)}")
    print(f"     pattern {p2_hand}, meme classe Sat que sigma1*sigma2 : {same_class}")
    print(f"     bras concrets : tri(d1)={is_tricolorable(d1)} tri(d2)={is_tricolorable(d2)} "
          f"-> {'OK' if arms_ok else 'ECHEC'}")
    # Tangle OUVERT sigma1*sigma2 <-> sigma2*sigma1 (2 croisements, 6 arcs de
    # bord + 1 arc interne g). Positions 0..7 = (b,a,g,a',c,g,c',b') vs
    # (c,b,g,b',g,a,c',a'). DECOUVERTE : Sat NON egaux -- ce n'est PAS un move
    # d'isotopie ; le R3 classique est un move a 3 croisements (Partie C).
    # SCENARIO NEGATIF attendu : open_ok doit etre False.
    p1_open = tuple(sorted([(1,), (3,), (0,), (7,), (4,), (6,), (2, 5)]))
    p2_open = tuple(sorted([(5,), (7,), (1,), (3,), (0,), (6,), (2, 4)]))
    open_ok = pattern_sat(p1_open) == pattern_sat(p2_open)
    print(f"   tangle OUVERT sigma1*sigma2 -> sigma2*sigma1 (2 croisements) : "
          f"Sat egaux = {open_ok} -- scenario NEGATIF attendu "
          f"({'confirme' if not open_ok else 'ANOMALIE : inattendu'})")
    return 0 if (same_class and arms_ok and not open_ok) else 1


# ---------------------------------------------------------------------------
# Partie C -- le triangle classique R3 (3 croisements)
# ---------------------------------------------------------------------------

# Positions 0..3 = X1, 4..7 = X2, 8..11 = X3 (sigma1*sigma2*sigma1).
# X1=<a2,a1,g1,g2> X2=<a3,g1,g3,b3> X3=<g3,g2,b2,b1>
P1_TRIANGLE = tuple(sorted([(0,), (1,), (4,), (7,), (10,), (11,),
                            (2, 5), (3, 9), (6, 8)]))
# Positions 0..3 = Y1, 4..7 = Y2, 8..11 = Y3 (sigma2*sigma1*sigma2).
# Y1=<a3,a2,h1,h2> Y2=<h1,a1,h3,h4> Y3=<h2,h4,b2,b3> avec h3=b1
P2_TRIANGLE = tuple(sorted([(0,), (1,), (5,), (6,), (10,), (11,),
                            (2, 4), (3, 8), (7, 9)]))


def pattern_sat_set(blocks: tuple) -> frozenset:
    """Sat comme ensemble de tuples (valeurs par variable canonique), pour la
    comparaison sous bijection arbitraire des variables."""
    order = var_order(blocks)
    pos2var = {p: k for k, b in enumerate(order) for p in b}
    out = []
    for assign in product(range(3), repeat=len(order)):
        col = [assign[pos2var[p]] for p in range(12)]
        if (cond_colors(col[0], col[1], col[2], col[3])
                and cond_colors(col[4], col[5], col[6], col[7])
                and cond_colors(col[8], col[9], col[10], col[11])):
            out.append(assign)
    return frozenset(out)


def sat_isomorphisms(p1: tuple, p2: tuple, n_slots: int = 12,
                     preset: dict | None = None):
    """Generateur des bijections des blocs preservant les tailles sous
    lesquelles Sat(p1) transporte exactement sur Sat(p2) (egalite des
    ensembles de solutions = transfert bi-directionnel pour tout contexte).
    ``preset`` force des mappings bloc -> bloc (indices ordre canonique)."""
    o1, o2 = var_order(p1), var_order(p2)
    if tuple(sorted(len(b) for b in o1)) != tuple(sorted(len(b) for b in o2)):
        return
    sat1, sat2 = pattern_sat_set(p1), pattern_sat_set(p2)
    if len(sat1) != len(sat2):
        return
    idx1_by_size: dict[int, list[int]] = {}
    idx2_by_size: dict[int, list[int]] = {}
    for k, b in enumerate(o1):
        idx1_by_size.setdefault(len(b), []).append(k)
    for k, b in enumerate(o2):
        idx2_by_size.setdefault(len(b), []).append(k)
    from itertools import permutations as _perm
    choices = {s: list(_perm(idx2_by_size[s])) for s in idx1_by_size}
    if preset:
        # Restreint chaque taille aux permutations qui respectent les mappings
        # forces (bloc i de p1 -> bloc preset[i] de p2).
        for s, perms in choices.items():
            choices[s] = [
                p for p in perms
                if all(p[k] == preset[bidx]
                       for k, bidx in enumerate(idx1_by_size[s])
                       if bidx in preset)
            ]
    sizes = sorted(idx1_by_size)
    # produit cartesien des choix par taille
    def _combos(i: int, acc: dict):
        if i == len(sizes):
            yield dict(acc)
            return
        s = sizes[i]
        for perm in choices[s]:
            for k, bidx in enumerate(idx1_by_size[s]):
                acc[bidx] = perm[k]
            yield from _combos(i + 1, acc)
    for phi in _combos(0, {}):
        moved = set()
        for t in sat1:
            s = [0] * len(o2)
            for i, val in enumerate(t):
                s[phi[i]] = val
            moved.add(tuple(s))
        if moved == sat2:
            yield phi


def sat_isomorphic(p1: tuple, p2: tuple, n_slots: int = 12,
                   preset: dict | None = None) -> dict | None:
    """Premiere bijection a Sat egal (cf sat_isomorphisms), ou None."""
    for phi in sat_isomorphisms(p1, p2, n_slots, preset):
        return phi
    return None


def _perfect_matchings(items: tuple) -> "list[tuple]":
    """Tous les appariements parfaits (blocs de taille exactement 2).
    Pour 12 positions : 11!! = 10395."""
    if not items:
        return [()]
    out = []
    first = items[0]
    for k in range(1, len(items)):
        rest = items[1:k] + items[k + 1:]
        for m in _perfect_matchings(rest):
            out.append(((first, items[k]),) + m)
    return out


def run_triangle() -> int:
    print("== Partie C : triangle classique R3 (3 croisements) ==")
    # C1 -- fermeture complete du trefle : parmi les 10395 appariements
    # parfaits des 12 slots, combien dans la meme classe Sat.
    trefoil = trefoil_diagram()
    labels = [s for c in trefoil.crossings for s in _slots_of(c)]
    by_label: dict[int, list[int]] = {}
    for pos, lab in enumerate(labels):
        by_label.setdefault(lab, []).append(pos)
    p_trefoil = tuple(sorted(tuple(v) for v in by_label.values()))
    matchings = sorted({tuple(sorted(m)) for m in _perfect_matchings(tuple(range(12)))})
    assert len(matchings) == 10395, len(matchings)
    sat_trefoil = pattern_sat_set(p_trefoil)
    same = [m for m in matchings if pattern_sat_set(m) == sat_trefoil]
    print(f"   C1 fermeture trefle : {len(matchings)} appariements parfaits, "
          f"{len(same)} dans sa classe Sat (dont lui-meme)")
    # C2 -- bijection geometrique entre les deux triangles derives.
    phi = sat_isomorphic(P1_TRIANGLE, P2_TRIANGLE)
    if phi is None:
        print("   C2 triangle sigma1*sigma2*sigma1 <-> sigma2*sigma1*sigma2 : "
              "AUCUNE bijection a Sat egal -> candidat REUTE")
        return 1
    o1, o2 = var_order(P1_TRIANGLE), var_order(P2_TRIANGLE)
    # Correspondence geometrique FORCEE sur les 6 arcs de bord (meme arc
    # physique de part et d'autre) ; les 3 arcs internes n'ont pas de
    # correspondance canonique -- la bijection les decide.
    geo_border = {  # nom d'arc -> (bloc P1, bloc P2)
        "a2": ((0,), (1,)), "a1": ((1,), (5,)), "a3": ((4,), (0,)),
        "b3": ((7,), (11,)), "b2": ((10,), (10,)), "b1": ((11,), (6,)),
    }
    phi_blocks = {o1[i]: o2[phi[i]] for i in range(len(o1))}
    border_ok = all(phi_blocks[b1] == b2 for b1, b2 in geo_border.values())
    print(f"   C2 bijection a Sat egal TROUVEE ; respecte l'identite des arcs "
          f"de bord : {border_ok}")
    for name, (b1, b2) in sorted(geo_border.items()):
        mark = "OK" if phi_blocks[b1] == b2 else f"-> {phi_blocks[b1]}"
        print(f"     {name} {b1} {mark}")
    for b in sorted(phi_blocks):
        if len(b) == 2:
            print(f"     interne {b} -> {phi_blocks[b]}")
    # C2-bis : version GEOMETRIQUE -- identite forcee sur les 6 arcs de bord,
    # internes libres (6 permutations). C'est la forme du vrai move R3 : si
    # elle existe, la chirurgie associee EST le glissement de brin classique.
    idx1 = {b: i for i, b in enumerate(o1)}
    idx2 = {b: j for j, b in enumerate(o2)}
    preset = {idx1[b1]: idx2[b2] for b1, b2 in geo_border.values()}
    phi_geo = sat_isomorphic(P1_TRIANGLE, P2_TRIANGLE, preset=preset)
    if phi_geo is not None:
        print("   C2-bis version GEOMETRIQUE (identite des arcs de bord) : "
              "TROUVEE -> candidat Reidemeister3Connected canonique")
        print(f"     internes : "
              f"{ {b: o2[phi_geo[i]] for i, b in enumerate(o1) if len(b) == 2} }")
    else:
        print("   C2-bis version GEOMETRIQUE : ABSENTE "
              "(seules des redistributions non-geometriques transferent)")
    n_phis = sum(1 for _ in sat_isomorphisms(P1_TRIANGLE, P2_TRIANGLE))
    print(f"   C2-ter nombre total de bijections a Sat egal : {n_phis} "
          f"(sur 6!*3! = 4320 candidates taille-preservantes)")
    # C4 -- transport IDENTITE : parmi les 15 appariements internes possibles
    # (positions de bord fixees), un autre pattern a Sat canoniquement egal ?
    border = {p for b in P1_TRIANGLE if len(b) == 1 for p in b}
    internal = tuple(sorted(set(range(12)) - border))
    sat1 = pattern_sat_set(P1_TRIANGLE)
    ident_partners = []
    for m in _perfect_matchings(internal):
        y = tuple(sorted([(p,) for p in border]
                         + [tuple(sorted(pr)) for pr in m]))
        if pattern_sat_set(y) == sat1:
            ident_partners.append(y)
    nontrivial = [y for y in ident_partners if y != P1_TRIANGLE]
    print(f"   C4 transport identite (15 appariements internes, bord fixe) : "
          f"{len(ident_partners)} partenaire(s) a Sat egal, "
          f"{len(nontrivial)} non-trivial(aux) -- reponse "
          f"{'OUI' if nontrivial else 'NON (seul lui-meme)'}")
    # C3 -- temoins concrets : diagrammes wf aleatoires n=5 realisant le
    # triangle ouvert, chirurgie appliquee, bras verifies.
    import random
    rng = random.Random(0)
    singles = [min(b) for b in var_order(P1_TRIANGLE) if len(b) == 1]
    pairs = [b for b in var_order(P1_TRIANGLE) if len(b) == 2]
    checked = 0
    fails = 0
    for _ in range(300):
        # triple : labels de bord 1..6 aux positions singles, internes 7..9.
        triple = [0] * 12
        for k, pos in enumerate(singles):
            triple[pos] = k + 1
        for k, (p, q) in enumerate(pairs):
            triple[p] = triple[q] = 7 + k
        # 2 croisements externes : 6 bord (complement) + label 10 deux fois.
        rest = [1, 2, 3, 4, 5, 6, 10, 10]
        rng.shuffle(rest)
        d1 = KnotDiagram(
            (PDCrossing(*triple[0:4]), PDCrossing(*triple[4:8]),
             PDCrossing(*triple[8:12]), PDCrossing(*rest[0:4]),
             PDCrossing(*rest[4:8])), 10)
        assert d1.wf()
        # Chirurgie : l'arc j du nouveau triangle (bloc o2[j]) recupere le
        # label concret porte par l'arc i = inv(j) de l'ancien triangle.
        # Multiset de labels inchange -> wf preserve, contexte externe intact.
        inv = {phi[i]: i for i in range(len(o1))}
        lab_of_var2 = [triple[min(o1[inv[j]])] for j in range(len(o2))]
        pos2var2 = {p: k for k, b in enumerate(o2) for p in b}
        new12 = [lab_of_var2[pos2var2[p]] for p in range(12)]
        new_list = list(d1.crossings)
        new_list[0] = PDCrossing(*new12[0:4])
        new_list[1] = PDCrossing(*new12[4:8])
        new_list[2] = PDCrossing(*new12[8:12])
        d2 = KnotDiagram(tuple(new_list), 10)
        assert d2.wf()
        checked += 1
        if is_tricolorable(d1) != is_tricolorable(d2):
            fails += 1
            if fails <= 2:
                print(f"     ECHEC bras : {_fmt(d1)} -> {_fmt(d2)}")
    print(f"   C3 temoins concrets n=5 : {checked} chirurgies, {fails} echecs")
    return 0 if fails == 0 else 1

def _fmt(d: KnotDiagram) -> str:
    return "[" + ", ".join(f"<{c.e1},{c.e2},{c.e3},{c.e4}>" for c in d.crossings) + "]"


def selftest() -> int:
    assert not is_tricolorable(empty_diagram())
    assert is_tricolorable(two_twin_crossings())
    assert is_tricolorable(trefoil_diagram())
    assert not is_tricolorable(figure_eight_diagram())
    # Fox est symetrique en ses trois arguments (cle de la prediction V4).
    for c in product(range(3), repeat=3):
        base = (c[0] == c[1] and c[1] == c[2]) or (c[0] != c[1] and c[1] != c[2] and c[0] != c[2])
        for q in permutations(range(3)):
            assert cond_colors(c[q[0]], c[q[1]], c[q[2]], c[q[1]]) == base
    # Le temoin braid est wf.
    d1 = KnotDiagram((PDCrossing(2, 1, 3, 1), PDCrossing(4, 3, 4, 2)), 4)
    assert d1.wf()
    # 764 partitions attendues (involutions de S8).
    assert len(all_partitions_8()) == 764, len(all_partitions_8())
    print("selftest OK (diagrammes nommes, symetrie Fox, 764 partitions, wf braid)")
    return 0


def reproduce(diagrams: list[KnotDiagram]) -> int:
    print("== Reproduction R1 (equivalence du framework, comptes exacts) ==")
    total = 0
    fail = 0
    for d1 in diagrams:
        for d2, _meta in r1_surgeries(d1):
            total += 1
            if is_tricolorable(d1) != is_tricolorable(d2):
                fail += 1
    print(f"   diagrammes wf n<=2 : {len(diagrams)} (attendu 2526)")
    print(f"   torsions R1 : {total} (attendu 20184), echecs transfert : {fail} (attendu 0)")
    ok = len(diagrams) == 2526 and total == 20184 and fail == 0
    print(f"   verdict : {'CONFORME' if ok else 'ECART'}")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--reproduce", action="store_true")
    ap.add_argument("--perms", action="store_true")
    ap.add_argument("--r3search", action="store_true")
    ap.add_argument("--concrete", action="store_true")
    ap.add_argument("--triangle", action="store_true")
    ap.add_argument("--max-crossings", type=int, default=2)
    args = ap.parse_args()
    everything = not (args.selftest or args.reproduce or args.perms
                      or args.r3search or args.concrete or args.triangle)

    rc = 0
    if args.selftest or everything:
        rc |= selftest()
    if everything or args.reproduce or args.perms or args.concrete:
        diagrams = enumerate_wf_diagrams(args.max_crossings)
    if everything or args.reproduce:
        rc |= reproduce(diagrams)
    if everything or args.perms:
        rc |= run_perms(diagrams)
    groups = None
    if everything or args.r3search or args.concrete:
        groups = build_groups()
    if everything or args.r3search:
        rc |= run_r3search(groups)
    if everything or args.concrete:
        rc |= run_concrete(diagrams, groups)
        rc |= run_braid_witness(groups)
    if everything or args.triangle:
        rc |= run_triangle()
    return rc


if __name__ == "__main__":
    sys.exit(main())
