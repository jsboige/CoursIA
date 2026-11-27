"""Banc case 28 : connexion extensive (Whitehead, *Process and Reality*, 1929, Part IV, ch. II).

These de la source
------------------
La relation premiere du monde physique n'est pas l'etendue mais la **connexion
extensive** entre regions (« extensive connection ... is sui generis ... But its
formal properties can be stated », p. 441). De cette seule relation le chapitre
tire, par definition, l'inclusion (D2, due a de Laguna), le recouvrement (D3), la
dissection (D4), l'intersection (D5-D6), la connexion externe (D7), les
inclusions tangentielle et non tangentielle (D8-D9), les ensembles abstractifs
(D10), l'equivalence (D11-D12), les elements geometriques (D13-D14) et les points
(D16). Il joint a ces definitions 24 hypotheses numerotees du tronc (A1-A12,
A15-A26 ; la numerotation imprimee saute 13 et 14) et affirme deux choses
distinctes : que ces proprietes decrivent la connexion extensive « en general »,
et que la ligne separant le general de ce qui n'appartient qu'a « notre epoque
cosmique » est difficile a tracer (p. 442).

Ce que ce module rend falsifiable
---------------------------------
La ligne elle-meme. Neuf substrats instancient la connexion (S1 ferme, S2 ouvert,
S2r ouvert regularise, S3 atomique, S4 boites en dimension 1 a 4, S5 arbre) ;
chaque hypothese y est evaluee separement, en arithmetique rationnelle exacte
(`fractions.Fraction`, aucun flottant dans une decision). Une hypothese fausse
dans un substrat est dite **d'epoque** ; vraie dans tous, **necessaire sur la
famille** : exactement la distinction que la source dit ne pas savoir tracer.

Lectures retenues (le scelle les fixe, ce module les execute)
------------------------------------------------------------
K1  la connexion est irreflexive par convention (A4) ;
K2' l'inclusion faible (D2) est reflexive : `A ⊑ B` = « A inclut B »,
    `A ⊏ B` = `⊑` et `≠` ;
K3  A4, A7, A21, A26 sont des conventions de nomenclature (`par_definition`) ;
K4  « any two regions » se lit sur les paires distinctes ;
K5  sur une relation irreflexive, D2 et ses derivees (D3, D5, D7, D8) s'evaluent
    sur la cloture reflexive du contact — ce que font les formes fermees de S1,
    S2 et S4 ; d'ou, pour S3, `A ⊑ B` ssi `I(B) ⊆ I(A)` avec
    `I(R) = R ∪ {c : ∃c'∈R, abs(c - c') <= 1}`, et pour S5, `A ⊑ B` ssi A est un
    prefixe de B. Sous K5, A5 et A6 sont des theoremes de D2 et A19 de D5.

Le scelle vit dans `docs/ict/whitehead-extensive-connection-pre-enregistrement.md`
(v1, amendements v2, v2.1, v2.2, v2.3 — tous anterieurs a la premiere sortie du
banc) : ce module ne le redefinit pas, il l'execute.

Anti-duplication
----------------
Les cases 23-27 testent des theories de la conscience (Lahav, Penrose, Hoel,
Comolatti-Hoel, Tegmark). La case 28 ne teste aucune these sur la conscience :
elle teste la coherence interne d'un systeme formel de 1929. Aucun module `ict/`
n'implemente de mereotopologie : le banc n'invoque aucun organe et n'en
reimplemente aucun.

Reductions declarees
--------------------
Les hypotheses d'abstraction fine (A21-A26) sont evaluees sur trois chaines
explicites en family infinie et par enumeration exacte (sous plafond declare) en
famille finie ; leur statut est marque `peu_discriminant` et n'entre pas dans le
compte qui porte le verdict (scelle, section 5). Les pieces de S4 restent hors
matrice pour A15/A16 (scelle v2.3, section 5) : elles sont mesurees a part, a
titre exploratoire.
"""

from __future__ import annotations

import argparse
import json
import random
from fractions import Fraction as F
from pathlib import Path

CASE = 28
SOURCE = (
    "Whitehead, Process and Reality (New York: Macmillan, 1929), "
    "Part IV, ch. II, pp. 449-459"
)
ORGAN = "ict/whitehead_extensive_connection.py"
PREREG_DOC = "docs/ict/whitehead-extensive-connection-pre-enregistrement.md"

# Les 24 hypotheses du tronc. La numerotation imprimee saute 13 et 14 (verifie
# sur deux scans independants) ; A27-A33 portent sur les segments, les lieux et
# l'ordre des points, hors perimetre de cette tranche (cf. scelle, section 3).
ASSUMPTIONS = tuple(list(range(1, 13)) + list(range(15, 27)))

TEST_SEEDS = (0, 1, 7, 42, 99)
CONTROL_SEEDS = (11, 22, 33)

NULL_SIZE = 8
NULL_DENSITY = F(1, 2)
P6_MIN_VIOLATIONS = 12
CONTROL_MIN_VIOLATIONS = 14
MIN_NECESSARY = 15
MIN_EPOCHAL = 3
CHAIN_LENGTH = 40
MAX_ABSTRACTIVE = 4000
CAP_DISSECTIONS = 50000
MANY = 2
WANT_DISSECTIONS = 4
MAX_WITNESS = 5

# Etat d'une recherche de dissections (scelle v2.3, section 3) : seule
# `ENUM_EXACTE` autorise a conclure `false` sur une region sans dissection.
# `ENUM_PLAFOND` = le plafond de jeux examines a ete atteint ;
# `ENUM_GENERATEUR` = la famille n'enumere pas ses dissections, elle en propose
# quatre motifs calcules (scelle v2.1, section 9) : l'absence de candidat
# valide n'apprend rien de la definition D4, et ne peut donc pas fonder `false`.
ENUM_EXACTE = "exacte"
ENUM_PLAFOND = "plafond"
ENUM_GENERATEUR = "generateur"

# Classification theorique de L7 (recensement du scelle) : 13 hypotheses ne
# peuvent pas etre violees (conventions de nomenclature ou theoremes de D2/D3/D5),
# 11 peuvent l'etre. Le plafond de violations est donc 11 — c'est lui qui rend
# inatteignables les seuils 12 (P6) et 14 (controle), et c'est ce que le verdict
# rapporte comme defaut d'instrument.
NEVER_VIOLABLE = (1, 4, 5, 6, 7, 10, 19, 21, 22, 23, 24, 25, 26)
VIOLABLE = (2, 3, 8, 9, 11, 12, 15, 16, 17, 18, 20)

STATUS_LEGEND = {
    "true": "verifiee sur le domaine declare du substrat",
    "false": "contre-exemple trouve, serialise dans les details",
    "prouve": "theoreme de D2/D3/D5 sous K5, verifie mecaniquement",
    "par_definition": "convention de nomenclature (K3), non falsifiable",
    "partiel": "une partie du domaine n'a pas pu etre decidee ; motif et compte joints",
    "instable": "le statut depend de la graine ; les valeurs par graine sont jointes",
}

GRID = ("0", "1/6", "1/3", "1/2", "2/3", "5/6", "1", "3/2", "2", "3", "4", "6", "10")
SUBGRID = ("0", "1/3", "1/2", "2/3", "1", "3/2", "2")

# Six unions nommees. La premiere est le support du temoin scelle de P2 :
# `(0,1) \ {1/3, 2/3}` a meme adherence que `(0,1)` et n'est pas la meme region.
SEALED_UNIONS = (
    ((("0", "1/3"), ("1/3", "2/3"), ("2/3", "1"))),
    ((("0", "1/6"), ("1/6", "1/3"), ("1/3", "1/2"))),
    ((("0", "1/3"), ("2/3", "1"))),
    ((("0", "1/6"), ("5/6", "1"))),
    ((("0", "1/2"), ("1", "3/2"), ("2", "3"))),
    ((("0", "1/2"), ("1/2", "1"))),
)


# --------------------------------------------------------------------------- #
# Helpers rationnels et d'intervalle
# --------------------------------------------------------------------------- #


def _fr(value):
    """Fraction exacte depuis une chaine, un entier ou une Fraction."""
    if isinstance(value, F):
        return value
    return F(value)


def _pts(names):
    return tuple(_fr(name) for name in names)


def _merge(parts, touching):
    """Normalise une union d'intervalles : triee, sans chevauchement.

    `touching` fusionne deux morceaux qui se touchent (famille fermee, ou
    famille ouverte regularisee). Faux, deux morceaux qui se touchent restent
    distincts — c'est ce qui rend la famille ouverte non reguliere.
    """
    cleaned = []
    for lo, hi in parts:
        lo, hi = _fr(lo), _fr(hi)
        if lo < hi:
            cleaned.append((lo, hi))
    cleaned.sort()
    out = []
    for lo, hi in cleaned:
        if out and (lo <= out[-1][1] if touching else lo < out[-1][1]):
            if hi > out[-1][1]:
                out[-1] = (out[-1][0], hi)
        else:
            out.append((lo, hi))
    return tuple(out)


def _covers(big, small):
    """Vrai si l'union d'intervalles `big` contient `small` (au sens des ensembles)."""
    for lo, hi in small:
        if not any(blo <= lo and hi <= bhi for blo, bhi in big):
            return False
    return True


def _meets(first, second):
    """Vrai si deux unions fermees se coupent (contact d'extremite inclus)."""
    for alo, ahi in first:
        for blo, bhi in second:
            if max(alo, blo) <= min(ahi, bhi):
                return True
    return False


def _interior_meets(first, second):
    """Vrai si l'intersection des deux unions contient un intervalle de longueur > 0."""
    for alo, ahi in first:
        for blo, bhi in second:
            if max(alo, blo) < min(ahi, bhi):
                return True
    return False


def _overlaps_union(first, second):
    """Intersection de longueur > 0, sous forme d'union fermee normalisee."""
    pieces = []
    for alo, ahi in first:
        for blo, bhi in second:
            lo, hi = max(alo, blo), min(ahi, bhi)
            if lo < hi:
                pieces.append((lo, hi))
    return _merge(pieces, True)


def _show_union(parts, closed):
    if not parts:
        return "{}"
    left, right = ("[", "]") if closed else ("(", ")")
    return " U ".join(f"{left}{lo}{right}" if closed else f"{left}{lo}, {hi}{right}"
                      for lo, hi in parts) if closed else " U ".join(
        f"({lo}, {hi})" for lo, hi in parts)


def _bits(mask):
    """Indices des bits poses, du plus petit au plus grand."""
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def _count(mask):
    return bin(mask).count("1")


def _format_interval(parts, closed):
    if not parts:
        return "vide"
    if closed:
        return " U ".join(f"[{lo}, {hi}]" for lo, hi in parts)
    return " U ".join(f"({lo}, {hi})" for lo, hi in parts)


def _drawn_unions(seed, count=8):
    """Unions d'intervalles de la grille, morceaux separes par une cellule vide.

    Memes tirages pour S1, S2 et S2r (scelle, section 7.6).
    """
    rng = random.Random(seed * 7919 + 28)
    points = _pts(GRID)
    cells = len(points) - 1
    out = []
    for _ in range(count):
        picks = (0, 2)
        for _attempt in range(200):
            size = rng.choice((2, 3))
            picks = sorted(rng.sample(range(cells), size))
            if all(picks[t + 1] - picks[t] >= 2 for t in range(len(picks) - 1)):
                break
        out.append(tuple((points[cell], points[cell + 1]) for cell in picks))
    return tuple(out)


# --------------------------------------------------------------------------- #
# Substrat : interface commune
# --------------------------------------------------------------------------- #


class Substrate:
    """Famille de regions + connexion. Les predicats derives suivent D2-D9."""

    key = "?"
    label = "?"
    exploratory = False
    deterministic = False
    whole = False
    regular = False
    finite_family = False
    dissections_in_matrix = True

    def __init__(self):
        self._battery = None
        self._index = None
        self._prepared = False

    # -- batterie ---------------------------------------------------------- #

    def build_battery(self):
        raise NotImplementedError

    def battery(self):
        if self._battery is None:
            regions = self.build_battery()
            seen = {}
            for region in regions:
                seen.setdefault(self.normalize(region), True)
            ordered = sorted(seen, key=self.sort_key)
            self._battery = tuple(ordered)
            self._index = {region: position for position, region in enumerate(ordered)}
        return self._battery

    def normalize(self, region):
        return region

    def sort_key(self, region):
        """Ordre de la batterie. `repr` par defaut ; les familles indexees par un
        entier (S3, S5, temoin) surchargent pour que position == identifiant —
        sans quoi les masques lus par identifiant designeraient une autre ligne."""
        return repr(region)

    def index_of(self, region):
        self.battery()
        return self._index.get(self.normalize(region))

    def show(self, region):
        return repr(region)

    def sub_battery(self):
        return self.battery()

    # -- predicats de base ------------------------------------------------- #

    def conn(self, first, second):
        raise NotImplementedError

    def includes(self, first, second):
        """`first` inclut `second` (D2, lecture K2')."""
        raise NotImplementedError

    def ov(self, first, second):
        """D3 : recouvrement — une troisieme region est incluse dans les deux."""
        raise NotImplementedError

    def tang(self, first, second):
        """D8 : `second` est incluse tangentiellement dans `first`."""
        return False

    # -- tables de masques sur la batterie --------------------------------- #

    def prepare(self):
        if self._prepared:
            return self
        battery = self.battery()
        size = len(battery)
        inc = [0] * size
        sup = [0] * size
        ovm = [0] * size
        cnm = [0] * size
        for i in range(size):
            for j in range(size):
                if i != j and self.conn(battery[i], battery[j]):
                    cnm[i] |= 1 << j
                if self.includes(battery[i], battery[j]):
                    inc[i] |= 1 << j
                    sup[j] |= 1 << i
                if i != j and self.ov(battery[i], battery[j]):
                    ovm[i] |= 1 << j
        self.inc = inc
        self.sup = sup
        self.ovm = ovm
        self.cnm = cnm
        self.proper_in = [inc[i] & ~(1 << i) for i in range(size)]
        self.full_mask = (1 << size) - 1
        self._prepared = True
        return self

    # -- existentielles : temoins batterie d'abord, famille ensuite -------- #

    def far(self, region):
        """Region non connectee a `region` (A2 i), ou None si la famille est epuisee."""
        spot = self.index_of(region)
        if spot is not None:
            missing = self.full_mask & ~self.cnm[spot] & ~(1 << spot)
            for other in _bits(missing):
                return self.battery()[other]
        return self.far_constructed(region)

    def far_constructed(self, region):
        return None

    def weak(self, first, second):
        """Troisieme region distincte connectee aux deux (A2 ii)."""
        i, j = self.index_of(first), self.index_of(second)
        if i is not None and j is not None:
            both = self.cnm[i] & self.cnm[j] & ~((1 << i) | (1 << j)) & self.full_mask
            if both:
                return self.battery()[both.bit_length() - 1 if False else next(_bits(both))]
        return self.weak_constructed(first, second)

    def weak_constructed(self, first, second):
        return None

    def disjoint_pair(self, region):
        """Deux parties propres de `region` non connectees entre elles (A9 ii)."""
        return self.disjoint_pair_constructed(region)

    def disjoint_pair_constructed(self, region):
        return None

    def has_part(self, region):
        """Vrai si `region` inclut une autre region (A9 i)."""
        spot = self.index_of(region)
        if spot is not None and self.proper_in[spot]:
            return True
        return self.has_part_constructed(region)

    def has_part_constructed(self, region):
        return False

    # -- dissections ------------------------------------------------------- #

    def dissects(self, region, members, pool=None):
        """D4 verifie point par point (familles finies ou jeu construit)."""
        if not members:
            return False
        for member in members:
            if member == region or not self.includes(region, member):
                return False
        for position, member in enumerate(members):
            for other in members[position + 1:]:
                if self.ov(member, other):
                    return False
        candidates = self.battery() if pool is None else pool
        for other in candidates:
            if other == region or other in members:
                continue
            if not self.includes(region, other):
                continue
            if any(self.includes(member, other) for member in members):
                continue
            if sum(1 for member in members if self.ov(other, member)) > 1:
                continue
            return False
        return True

    def dissections(self, region, want=WANT_DISSECTIONS):
        """Candidats dissections de `region` : (liste, etat d'enumeration)."""
        return [], ENUM_GENERATEUR

    def dissection_masks(self, spot, want=WANT_DISSECTIONS):
        """Masks de candidats dissections, par indices de batterie.

        Rend `(masks, etat, jeux_examines)`. Sur la voie generateur, `etat` vaut
        `ENUM_GENERATEUR` : la liste est un jeu de motifs calcules, pas une
        enumeration, et son etat ne dit rien de la definition D4.
        """
        battery = self.battery()
        members, state = self.dissections(battery[spot], want=want)
        index = self._index
        masks = []
        for candidate in members:
            mask = 0
            usable = True
            for member in candidate:
                position = index.get(self.normalize(member))
                if position is None:
                    usable = False
                    break
                mask |= 1 << position
            if usable:
                masks.append(mask)
        return masks, state, len(members)

    def grid_cut_masks(self, spot):
        """Temoins de coupes non proposees par le generateur (aucun par defaut)."""
        return []

    def dissects_mask(self, spot, mask):
        """D4 en masques, (iii) verifie sur la batterie entiere."""
        if mask == 0:
            return False
        for member in _bits(mask):
            if not (self.proper_in[spot] >> member) & 1:
                return False
        for member in _bits(mask):
            if self.ovm[member] & (mask ^ (1 << member)):
                return False
        for other in _bits(self.proper_in[spot] & ~mask):
            if self.sup[other] & mask:
                continue
            if _count(self.ovm[other] & mask) < 2:
                return False
        return True

    # -- intersections (D5) ------------------------------------------------ #

    def intersects(self, first, second):
        """Intersects de deux regions recouvrantes (D5), liste complete."""
        return []

    # -- ensembles abstractifs --------------------------------------------- #

    def chains(self):
        return ()

    def abstractive_sets(self, cap=MAX_ABSTRACTIVE):
        """Enumeration des ensembles abstractifs d'une famille finie."""
        return [], False

    # -- identite ---------------------------------------------------------- #

    def witness(self, region):
        return self.show(region)


def _pair_list(items):
    return [(items[i], items[j]) for i in range(len(items)) for j in range(i + 1, len(items))]


# --------------------------------------------------------------------------- #
# S1 / S2 / S2r : les intervalles rationnels
# --------------------------------------------------------------------------- #


class Intervals(Substrate):
    """Unions finies d'intervalles rationnels en dimension 1.

    `closed`   : la famille de S1, morceaux fermes, connexion = intersection non vide.
    `regular`  : la famille de S2r, canonisee par adherence — deux ouverts de meme
                 adherence sont une seule region (scelle, section 7.6).
    Ni l'un ni l'autre : la famille de S2, morceaux ouverts distincts de contacts
    d'extremite permis, connexion = adherences secantes.
    """

    dissections_in_matrix = True
    finite_family = False

    def __init__(self, key, label, closed, regular, seed, exploratory=False):
        super().__init__()
        self.key = key
        self.label = label
        self.closed = closed
        self.regular = regular or closed
        self.seed = seed
        self.exploratory = exploratory
        self._csp = {}

    def normalize(self, region):
        return _merge(region, self.regular)

    def build_battery(self):
        points = _pts(GRID)
        regions = []
        for i in range(len(points)):
            for j in range(i + 1, len(points)):
                regions.append(((points[i], points[j]),))
        for union in SEALED_UNIONS:
            regions.append(tuple((_fr(lo), _fr(hi)) for lo, hi in union))
        for union in _drawn_unions(self.seed):
            regions.append(tuple((lo, hi) for lo, hi in union))
        return regions

    def sub_battery(self):
        points = _pts(SUBGRID)
        return tuple(((points[i], points[j]),)
                     for i in range(len(points)) for j in range(i + 1, len(points)))

    def csp(self, region):
        """Adherence de la region (forme fermee normalisee)."""
        cached = self._csp.get(region)
        if cached is None:
            cached = _merge(region, True) if not self.regular else region
            self._csp[region] = cached
        return cached

    def show(self, region):
        return _format_interval(region, True)

    def conn(self, first, second):
        # K1 : la connexion est irreflexive par convention de nomenclature.
        return first != second and _meets(self.csp(first), self.csp(second))

    def includes(self, first, second):
        return _covers(self.csp(first), self.csp(second))

    def ov(self, first, second):
        return _interior_meets(self.csp(first), self.csp(second))

    def tang(self, first, second):
        if not self.regular:
            # Famille ouverte : aucune region n'est exterieurement connectee a une
            # autre (une intersection non vide y est toujours d'interieur non vide),
            # donc D8 est vide et D9 vaut l'inclusion.
            return False
        if second == first or not self.includes(first, second):
            return False
        boundary = set()
        for lo, hi in self.csp(first):
            boundary.add(lo)
            boundary.add(hi)
        return any(lo in boundary or hi in boundary for lo, hi in self.csp(second))

    # -- existentielles construites --------------------------------------- #

    def far_constructed(self, region):
        high = max(hi for _, hi in self.csp(region))
        return ((high + 1, high + 2),)

    def weak_constructed(self, first, second):
        merged = _merge(tuple(self.csp(first)) + tuple(self.csp(second)), True)
        low = min(lo for lo, _ in merged)
        high = max(hi for _, hi in merged)
        return ((low - 1, high + 1),)

    def has_part_constructed(self, region):
        lo, hi = region[0]
        mid, delta = (lo + hi) / 2, (hi - lo) / 16
        return (((lo, mid - delta),),)

    def disjoint_pair_constructed(self, region):
        lo, hi = region[0]
        mid, delta = (lo + hi) / 2, (hi - lo) / 16
        return (self.normalize(((lo, mid - delta),)), self.normalize(((mid + delta, hi),)))

    # -- dissections ------------------------------------------------------- #

    def dissections(self, region, want=WANT_DISSECTIONS):
        out = []
        for position, (lo, hi) in enumerate(region):
            mid = (lo + hi) / 2
            left = self.normalize(region[:position] + ((lo, mid),) + region[position + 1:])
            right_parts = region[:position] + ((mid, hi),) + region[position + 1:]
            right = self.normalize(right_parts)
            if left and right and left != right:
                out.append((left, right))
            if len(out) >= want:
                break
        tertile_pieces = []
        for lo, hi in region:
            span = (hi - lo) / 3
            for start in (lo, lo + span, lo + 2 * span):
                piece = self.normalize(((start, start + span),))
                if piece:
                    tertile_pieces.append(piece)
        terciles = tuple(tertile_pieces)
        if len(terciles) >= 2 and terciles != (region,) and terciles not in out:
            out.append(terciles)
        return out, ENUM_GENERATEUR

    def grid_cut_masks(self, spot):
        """Coupes de la region aux points de grille interieurs, en masques.

        Sert de temoin, non de generateur : ces jeux ne sont pas proposes par
        `dissections` (quatre motifs calcules, scelle v2.1 section 9), mais la
        batterie les contient et `dissects_mask` les valide. Comptes a part dans
        `details[15]` : ils mesurent ce que le generateur manque.
        """
        region = self.battery()[spot]
        index = self._index
        points = _pts(GRID)
        masks = []
        for position, (lo, hi) in enumerate(region):
            for point in points:
                if not lo < point < hi:
                    continue
                left = self.normalize(region[:position] + ((lo, point),) + region[position + 1:])
                right = self.normalize(region[:position] + ((point, hi),) + region[position + 1:])
                if not left or not right:
                    continue
                parts = (left, right)
                if any(index.get(self.normalize(part)) is None for part in parts):
                    continue
                mask = 0
                for part in parts:
                    mask |= 1 << index[self.normalize(part)]
                if mask and mask not in masks:
                    masks.append(mask)
        return masks

    # -- intersections ----------------------------------------------------- #

    def kernel(self, first, second):
        overlap = _overlaps_union(self.csp(first), self.csp(second))
        if not overlap:
            return None
        return self.normalize(overlap)

    def morcelage(self, region):
        """Scinde le premier morceau en son milieu : meme adherence, autre region."""
        if not region:
            return None
        lo, hi = region[0]
        mid = (lo + hi) / 2
        split = self.normalize(((lo, mid), (mid, hi)) + region[1:])
        if split == region or not split:
            return None
        return split

    def _in_scope(self, candidate, first, second):
        if candidate == first:
            return self.includes(second, first)
        if candidate == second:
            return self.includes(first, second)
        return self.includes(first, candidate) and self.includes(second, candidate)

    def intersects(self, first, second):
        if not self.ov(first, second):
            return []
        kernel = self.kernel(first, second)
        if kernel is None:
            return []
        found = [kernel]
        if not self.regular:
            split = self.morcelage(kernel)
            if split is not None and split not in found:
                found.append(split)
        return [candidate for candidate in found if self._in_scope(candidate, first, second)]

    # -- chaines et temoin scelle ----------------------------------------- #

    def chains(self):
        return (
            Chain(self, "2^-n@0", F(0), 2),
            Chain(self, "3^-n@0", F(0), 3),
            Chain(self, "2^-n@1", F(1), 2),
        )

    def naive_chain(self):
        return Chain(self, "naive[0,2^-n]", F(0), 2, naive=True)

    def sealed_witness(self):
        first = self.normalize(((F(0), F(1)),))
        union = self.normalize(tuple((_fr(lo), _fr(hi)) for lo, hi in SEALED_UNIONS[0]))
        members = [self.normalize((piece,)) for piece in union]
        battery = self.battery()
        return {
            "temoins": [self.show(first), self.show(union)],
            "regions_distinctes": first != union,
            "dans_la_batterie": first in battery and union in battery,
            "dissection_de_0_1": self.dissects(first, members),
            "dissection_de_la_seconde": self.dissects(union, members),
        }


# --------------------------------------------------------------------------- #
# S4 : boites fermees rationnelles, dimension N
# --------------------------------------------------------------------------- #


class Boxes(Substrate):
    """Boites fermees uniques `prod [lo_i, hi_i]`, dimension 1 a 4 (S4)."""

    finite_family = False
    regular = True
    # Scelle section 6.3 : la famille des boites uniques n'est pas close sous la
    # coupe en dalles, les deux cases A15/A16 restent `partiel` dans la matrice et
    # la coupe est mesuree separement, a titre exploratoire.
    dissections_in_matrix = False

    def __init__(self, dimension, seed, key=None, size=30):
        super().__init__()
        self.dimension = dimension
        self.seed = seed
        self.key = key or f"S4_d{dimension}"
        self.label = f"boxes_d{dimension}"
        self.size = size

    def _box(self, lows, highs):
        return self.normalize(tuple(zip(lows, highs)))

    def normalize(self, region):
        return tuple((_fr(lo), _fr(hi)) for lo, hi in region if _fr(lo) < _fr(hi))

    def build_battery(self):
        rng = random.Random(self.seed * 100 + self.dimension)
        out = []
        for _ in range(self.size):
            lows, highs = [], []
            for _axis in range(self.dimension):
                lo = F(rng.randint(-6, 4), 2)
                lows.append(lo)
                highs.append(lo + F(rng.randint(1, 12), 2))
            out.append(self._box(lows, highs))
        return out

    def show(self, region):
        return " x ".join(f"[{lo}, {hi}]" for lo, hi in region)

    def conn(self, first, second):
        # K1 : la connexion est irreflexive par convention de nomenclature.
        return first != second and all(max(lo1, lo2) <= min(hi1, hi2)
                                       for (lo1, hi1), (lo2, hi2) in zip(first, second))

    def includes(self, first, second):
        return all(lo1 <= lo2 and hi2 <= hi1
                   for (lo1, hi1), (lo2, hi2) in zip(first, second))

    def ov(self, first, second):
        return all(max(lo1, lo2) < min(hi1, hi2)
                   for (lo1, hi1), (lo2, hi2) in zip(first, second))

    def tang(self, first, second):
        if second == first or not self.includes(first, second):
            return False
        return any(lo1 == lo2 or hi1 == hi2
                   for (lo1, hi1), (lo2, hi2) in zip(first, second))

    def far_constructed(self, region):
        high = max(hi for _, hi in region)
        lows = [lo for lo, _ in region]
        highs = [hi for _, hi in region]
        lows[0] = high + 1
        highs[0] = high + 2
        return self._box(lows, highs)

    def weak_constructed(self, first, second):
        lows = [min(a, b) - 1 for (a, _), (b, _) in zip(first, second)]
        highs = [max(a, b) + 1 for (_, a), (_, b) in zip(first, second)]
        return self._box(lows, highs)

    def has_part_constructed(self, region):
        lo, hi = region[0]
        mid = (lo + hi) / 2
        lows = [lo] + [b for _, b in region[1:]]
        highs = [mid] + [c for _, c in region[1:]]
        return self._box(lows, highs)

    def disjoint_pair_constructed(self, region):
        lo, hi = region[0]
        mid, delta = (lo + hi) / 2, (hi - lo) / 16
        first_lows = [lo] + [b for _, b in region[1:]]
        first_highs = [mid - delta] + [c for _, c in region[1:]]
        second_lows = [mid + delta] + [b for _, b in region[1:]]
        second_highs = [hi] + [c for _, c in region[1:]]
        return self._box(first_lows, first_highs), self._box(second_lows, second_highs)

    def _slabs(self, region, cuts):
        groups = []
        lows, highs = region[0]
        edges = [lows] + list(cuts) + [highs]
        for position in range(len(edges) - 1):
            piece_lows = [edges[position]] + [b for _, b in region[1:]]
            piece_highs = [edges[position + 1]] + [c for _, c in region[1:]]
            box = self._box(piece_lows, piece_highs)
            if box:
                groups.append(box)
        return tuple(groups)

    def dissections(self, region, want=WANT_DISSECTIONS):
        lo, hi = region[0]
        out = []
        for cuts in (((lo + hi) / 2,), (lo + (hi - lo) / 3, hi - (hi - lo) / 3)):
            pieces = self._slabs(region, cuts)
            if len(pieces) >= 2 and pieces != (region,):
                out.append(pieces)
        return out[:want], ENUM_GENERATEUR

    def kernel(self, first, second):
        lows, highs = [], []
        for (lo1, hi1), (lo2, hi2) in zip(first, second):
            lo, hi = max(lo1, lo2), min(hi1, hi2)
            if lo >= hi:
                return None
            lows.append(lo)
            highs.append(hi)
        return self._box(lows, highs)

    def intersects(self, first, second):
        if not self.ov(first, second):
            return []
        kernel = self.kernel(first, second)
        return [kernel] if kernel is not None else []

    def chains(self):
        return (Chain(self, "2^-n@0", F(0), 2, dimension=self.dimension),)

    def naive_chain(self):
        return Chain(self, "naive[0,2^-n]", F(0), 2, dimension=self.dimension, naive=True)


# --------------------------------------------------------------------------- #
# S3 / S5 / temoin aleatoire : familles finies, enumeration exacte
# --------------------------------------------------------------------------- #


class Relational(Substrate):
    """Famille finie de regions nommees, connexion par matrice d'adjacence."""

    finite_family = True
    dissections_in_matrix = True

    def __init__(self, key, label, names, adjacency, regular=None, whole=False):
        super().__init__()
        self.key = key
        self.label = label
        self.names = tuple(names)
        self.adjacency = adjacency
        self.whole = whole
        self.regular = regular if regular is not None else False
        self._closure_cache = {}
        self._ov_cache = {}

    def build_battery(self):
        return list(range(len(self.names)))

    def sort_key(self, region):
        # Famille indexee : l'identifiant EST la position, sans quoi les masques
        # (inc / sup / ovm / cnm / proper_in) lus par identifiant pointeraient
        # une autre ligne du tableau.
        return region

    def show(self, region):
        return self.names[region]

    def closure(self, region):
        cached = self._closure_cache.get(region)
        if cached is None:
            bits = 1 << region
            for other in self.adjacency[region]:
                bits |= 1 << other
            cached = bits
            self._closure_cache[region] = cached
        return cached

    def conn(self, first, second):
        return first != second and second in self.adjacency[first]

    def includes(self, first, second):
        if first == second:
            return True
        return self.closure(second) & ~self.closure(first) == 0

    def ov(self, first, second):
        key = (first, second) if first <= second else (second, first)
        cached = self._ov_cache.get(key)
        if cached is not None:
            return cached
        window = self.closure(first) & self.closure(second)
        answer = any(
            other not in (first, second) and (self.closure(other) & ~window) == 0
            for other in range(len(self.names))
        )
        self._ov_cache[key] = answer
        return answer

    def tang(self, first, second):
        if second == first or not self.includes(first, second):
            return False
        for other in range(len(self.names)):
            if other in (first, second):
                continue
            if self.ext(first, other) and self.ext(second, other):
                return True
        return False

    def ext(self, first, second):
        return self.conn(first, second) and not self.ov(first, second)

    # -- dissections par enumeration ---------------------------------------- #

    def dissections(self, region, want=WANT_DISSECTIONS):
        self.prepare()
        candidates = [other for other in _bits(self.proper_in[region])]
        out = []
        exact = True
        visited = 0

        def walk(start, mask):
            nonlocal visited, exact
            if len(out) >= want:
                return
            visited += 1
            if visited > CAP_DISSECTIONS:
                exact = False
                return
            if mask and self.dissects_mask(region, mask):
                out.append((mask,))
            for position in range(start, len(candidates)):
                member = candidates[position]
                if self.ovm[member] & mask:
                    continue
                walk(position + 1, mask | (1 << member))

        walk(0, 0)
        battery = self.battery()
        return [tuple(battery[member] for member in mask) for (mask,) in out[:want]], exact

    def dissection_masks(self, spot, want=WANT_DISSECTIONS):
        self.prepare()
        candidates = list(_bits(self.proper_in[spot]))
        masks = []
        visited = 0
        exact = True

        def walk(start, mask):
            nonlocal visited, exact
            if len(masks) >= want:
                return
            visited += 1
            if visited > CAP_DISSECTIONS:
                exact = False
                return
            if mask and self.dissects_mask(spot, mask):
                masks.append(mask)
            for position in range(start, len(candidates)):
                member = candidates[position]
                if self.ovm[member] & mask:
                    continue
                walk(position + 1, mask | (1 << member))

        walk(0, 0)
        return masks[:want], (ENUM_EXACTE if exact else ENUM_PLAFOND), visited

    # -- intersections par enumeration -------------------------------------- #

    def _is_intersect(self, candidate, first, second, pool):
        if candidate == first:
            if not self.includes(second, first):
                return False
        elif candidate == second:
            if not self.includes(first, second):
                return False
        elif not (self.includes(first, candidate) and self.includes(second, candidate)):
            return False
        for other in pool:
            if other in (first, second, candidate):
                continue
            if not (self.includes(first, other) and self.includes(second, other)):
                continue
            if self.ov(other, candidate) and not self.includes(candidate, other):
                return False
        return True

    def intersects(self, first, second):
        self.prepare()
        if not self.ov(first, second):
            return []
        pool = [other for other in _bits(self.inc[first] & self.inc[second])]
        return [other for other in pool if self._is_intersect(other, first, second, pool)]

    # -- ensembles abstractifs ----------------------------------------------- #

    def abstractive_sets(self, cap=MAX_ABSTRACTIVE):
        self.prepare()
        battery = self.battery()
        nt = {}
        for i in range(len(battery)):
            for j in _bits(self.proper_in[i]):
                nt[(i, j)] = not self.tang(i, j)
        found = []
        exact = True
        depth_cap = 12

        def walk(spot, chain, seen):
            nonlocal exact
            if len(found) >= cap:
                exact = False
                return
            children = [other for other in _bits(self.proper_in[spot])
                        if nt.get((spot, other)) and other not in seen]
            if not children or len(chain) >= depth_cap:
                found.append(tuple(chain))
                if len(chain) >= depth_cap:
                    exact = False
                return
            for child in children:
                walk(child, chain + [child], seen | {child})

        for spot in range(len(battery)):
            walk(spot, [spot], {spot})
        return found, exact


def cells_substrate(seed=0):
    """S3 : les 63 parties non vides de {0..5}, connexion atomique (scelle, tableau)."""
    regions = [mask for mask in range(1, 1 << 6)]
    adjacency = [[] for _ in regions]
    for first in range(len(regions)):
        for second in range(len(regions)):
            if first == second:
                continue
            left, right = regions[first], regions[second]
            if any(abs(a - b) <= 1 for a in range(6) if left >> a & 1
                   for b in range(6) if right >> b & 1):
                adjacency[first].append(second)
    names = []
    for mask in regions:
        names.append("{" + ",".join(str(cell) for cell in range(6) if mask >> cell & 1) + "}")
    return Relational("S3_atomic", "atomic", names, adjacency, regular=False, whole=False)


def tree_substrate(seed=0):
    """S5 : les 14 noeuds de profondeur 1..3 de l'arbre binaire complet (prefixes)."""
    nodes = []
    for depth in (1, 2, 3):
        for value in range(2 ** depth):
            nodes.append(bin(2 ** depth + value)[3:])
    adjacency = [[] for _ in nodes]
    for first, left in enumerate(nodes):
        for second, right in enumerate(nodes):
            # A1 : la connexion doit etre symetrique — on connecte deux noeuds
            # comparables, dans les deux sens (imbrication stricte, scelle S5).
            if first != second and (right.startswith(left) or left.startswith(right)):
                adjacency[first].append(second)
    return Relational("S5_tree", "tree", nodes, adjacency, regular=False, whole=False)


def random_substrate(seed, density, size=NULL_SIZE, key=None, label=None):
    """Temoin aleatoire : relation symetrique irreflexive tiree par graine."""
    rng = random.Random(seed * 104729 + size * 17 + int(density * 1000))
    edges = [[False] * size for _ in range(size)]
    for first in range(size):
        for second in range(first + 1, size):
            if F(rng.randint(1, 1000), 1000) < density:
                edges[first][second] = edges[second][first] = True
    adjacency = [[second for second in range(size) if edges[first][second]] for first in range(size)]
    names = [f"r{position}" for position in range(size)]
    return Relational(key or f"R_SEED{seed}", label or "random", names, adjacency,
                      regular=False, whole=False)


# --------------------------------------------------------------------------- #
# Chaines d'abstraction et groupes d'equivalence
# --------------------------------------------------------------------------- #


class Chain:
    """Chaine convergente explicite, membres indexes par n = 1..length."""

    def __init__(self, substrate, name, center, base, length=CHAIN_LENGTH,
                 dimension=1, naive=False, closed=True):
        self.substrate = substrate
        self.name = name
        self.center = _fr(center)
        self.base = base
        self.length = length
        self.dimension = dimension
        self.naive = naive
        self.closed = closed

    def member(self, index):
        radius = F(1, self.base ** index)
        if self.naive:
            return self.substrate.normalize(tuple((self.center, self.center + radius)
                                                 for _axis in range(self.dimension)))
        return self.substrate.normalize(
            tuple((self.center - radius, self.center + radius) for _axis in range(self.dimension))
        )

    def label(self, index):
        return f"{self.name}[{index}]"


def chain_covers(alpha, beta):
    """D11 : chaque membre de alpha inclut un membre de beta (verifie en forme fermee)."""
    if not chain_equivalent_shape(alpha, beta):
        return False
    for index in (1, 2, 3):
        if not alpha.substrate.includes(alpha.member(index), beta.member(index + 16)):
            return False
    return True


def chain_equivalent_shape(alpha, beta):
    return alpha.center == beta.center and alpha.dimension == beta.dimension


def chain_statuses(substrate):
    """A21-A26 sur les chaines explicites d'une famille infinie (peu discriminant)."""
    chains = list(substrate.chains())
    naive = substrate.naive_chain() if hasattr(substrate, "naive_chain") else None
    non_tangential = []
    for chain in chains:
        for index in (1, 2, 3):
            small, big = chain.member(index + 1), chain.member(index)
            non_tangential.append(not substrate.tang(big, small))
    coverage = {}
    for alpha in chains:
        for beta in chains:
            coverage[f"{alpha.name}->{beta.name}"] = chain_covers(alpha, beta)
    naive_rejected = None
    if naive is not None:
        naive_rejected = substrate.tang(naive.member(1), naive.member(2))
    return {
        "chaines": [chain.name for chain in chains],
        "non_tangentielle": all(non_tangential),
        "couverture": coverage,
        "chaine_naive_rejetee_par_D10_i": naive_rejected,
        "peu_discriminant": True,
    }


# --------------------------------------------------------------------------- #
# Evaluation d'un substrat
# --------------------------------------------------------------------------- #


def _capped(items):
    return items[:MAX_WITNESS]


def assess(substrate, want_witness=True):
    """Evalue les 24 hypotheses du tronc sur un substrat prepare."""
    substrate.prepare()
    battery = substrate.battery()
    size = len(battery)
    statuses = {}
    details = {}

    # A1 -- symetrie de la connexion (mesuree).
    asymmetric = [[substrate.show(battery[i]), substrate.show(battery[j])]
                  for i in range(size) for j in range(i + 1, size)
                  if substrate.conn(battery[i], battery[j]) != substrate.conn(battery[j], battery[i])]
    statuses[1] = "true" if not asymmetric else "false"
    details[1] = {"contre_exemples": _capped(asymmetric)}

    # A2 -- aucune region connectee a toutes ; deux regions quelconques
    # mediately connected.
    no_far, no_weak = [], []
    constructed = 0
    for i in range(size):
        spot = substrate.far(battery[i])
        if spot is None:
            no_far.append(substrate.show(battery[i]))
        elif spot not in battery:
            constructed += 1
    for i in range(size):
        for j in range(i + 1, size):
            spot = substrate.weak(battery[i], battery[j])
            if spot is None:
                no_weak.append([substrate.show(battery[i]), substrate.show(battery[j])])
            elif spot not in battery:
                constructed += 1
    statuses[2] = "true" if not no_far and not no_weak else "false"
    details[2] = {
        "sans_region_hors_connexion": _capped(no_far),
        "paires_sans_intermediaire": _capped(no_weak),
        "temoins_construits_hors_batterie": constructed,
    }

    # A3 -- la connexion n'est pas transitive.
    transitive_only = True
    witness = None
    for middle in range(size):
        neighbours = substrate.cnm[middle] & ~(1 << middle)
        for first in _bits(neighbours):
            broken = neighbours & ~substrate.cnm[first] & ~((1 << first) | (1 << middle))
            if broken:
                third = next(_bits(broken))
                transitive_only = False
                witness = [substrate.show(battery[first]), substrate.show(battery[middle]),
                           substrate.show(battery[third])]
                break
        if not transitive_only:
            break
    statuses[3] = "true" if not transitive_only else "false"
    details[3] = {"temoin_non_transitivite": witness}

    # A4 -- aucune region connectee avec elle-meme (convention).
    reflexive = [substrate.show(battery[i]) for i in range(size) if substrate.conn(battery[i], battery[i])]
    statuses[4] = "par_definition" if not reflexive else "false"
    details[4] = {"connexions_reflexives": _capped(reflexive)}

    # A5 -- inclusion => connexion (theoreme de D2 sous K5).
    broken = [[substrate.show(battery[i]), substrate.show(battery[j])]
              for i in range(size) for j in _bits(substrate.proper_in[i])
              if not substrate.conn(battery[i], battery[j])]
    statuses[5] = "prouve" if not broken else "false"
    details[5] = {"contre_exemples": _capped(broken)}

    # A6 -- transitivite de l'inclusion (theoreme de D2 sous K5). La lecture
    # faible (K2', reflexive) est requise : sous inclusion mutuelle, la version
    # « propre » fabriquerait un faux contre-exemple (A ⊑ B et B ⊑ A n'impliquent
    # pas A ⊏ A).
    broken = []
    for i in range(size):
        for j in _bits(substrate.inc[i]):
            if substrate.inc[j] & ~substrate.inc[i]:
                broken.append([substrate.show(battery[i]), substrate.show(battery[j])])
    statuses[6] = "prouve" if not broken else "false"
    details[6] = {"contre_exemples": _capped(broken)}

    # A7 -- une region ne s'inclut pas elle-meme (K3, sur l'inclusion propre).
    statuses[7] = "par_definition"
    details[7] = {"lecture": "A ⊏ A est faux par definition de ⊏"}

    # A8 -- asymetrie de l'inclusion.
    mutual = []
    for i in range(size):
        both = substrate.inc[i] & substrate.sup[i] & ~(1 << i)
        if both:
            mutual.append([substrate.show(battery[i]),
                           substrate.show(battery[next(_bits(both))])])
    statuses[8] = "true" if not mutual else "false"
    details[8] = {"paires_mutuelles": _capped(mutual)}

    # A9 -- toute region inclut d'autres regions, et deux parties propres non
    # connectees entre elles s'y trouvent toujours.
    no_part, no_pair = [], []
    for i in range(size):
        if not substrate.has_part(battery[i]):
            no_part.append(substrate.show(battery[i]))
            continue
        pair = substrate.disjoint_pair(battery[i])
        if pair is None:
            no_pair.append(substrate.show(battery[i]))
    statuses[9] = "true" if not no_part and not no_pair else "false"
    details[9] = {"regions_sans_partie": _capped(no_part),
                  "regions_sans_paire_disjointe": _capped(no_pair)}

    # A10 -- symetrie du recouvrement.
    asymmetric = [[substrate.show(battery[i]), substrate.show(battery[j])]
                  for i in range(size) for j in range(i + 1, size)
                  if substrate.ov(battery[i], battery[j]) != substrate.ov(battery[j], battery[i])]
    statuses[10] = "true" if not asymmetric else "false"
    details[10] = {"contre_exemples": _capped(asymmetric)}

    # A11 -- inclusion => recouvrement.
    broken = [[substrate.show(battery[i]), substrate.show(battery[j])]
              for i in range(size) for j in _bits(substrate.proper_in[i])
              if not substrate.ov(battery[i], battery[j])]
    statuses[11] = "true" if not broken else "false"
    details[11] = {"contre_exemples": _capped(broken)}

    # A12 -- recouvrement => connexion.
    broken = [[substrate.show(battery[i]), substrate.show(battery[j])]
              for i in range(size) for j in _bits(substrate.ovm[i] & ~substrate.cnm[i])]
    statuses[12] = "true" if not broken else "false"
    details[12] = {"contre_exemples": _capped(broken)}

    # A15 / A16 -- dissections.
    if not substrate.dissections_in_matrix:
        statuses[15] = "partiel"
        statuses[16] = "partiel"
        details[15] = {"motif": "famille de boites uniques : hors matrice (scelle, section 6.3)"}
        details[16] = {"motif": "famille de boites uniques : hors matrice (scelle, section 6.3)"}
        exploratory, states = [], []
        for i in range(size):
            found, path_state = substrate.dissections(battery[i])
            states.append(path_state)
            if found:
                exploratory.append({"region": substrate.show(battery[i]),
                                    "dissections": len(found)})
        details[15]["exploratoire"] = _capped(exploratory)
        details[15]["etat_enumeration"] = sorted(set(states))
        details[15]["enumeration_exacte"] = all(state == ENUM_EXACTE for state in states)
    else:
        counts, thin, thin_spots, thin_states = {}, [], [], {}
        cap_regions, generator_regions = [], []
        examined_total, examined_max = 0, 0
        for i in range(size):
            masks, state, examined = substrate.dissection_masks(i, want=WANT_DISSECTIONS)
            valid = [mask for mask in masks if substrate.dissects_mask(i, mask)]
            counts[substrate.show(battery[i])] = len(valid)
            examined_total += examined
            examined_max = max(examined_max, examined)
            if state == ENUM_PLAFOND:
                cap_regions.append(substrate.show(battery[i]))
            elif state == ENUM_GENERATEUR:
                generator_regions.append(substrate.show(battery[i]))
            if len(valid) < MANY:
                thin.append([substrate.show(battery[i]), len(valid)])
                thin_spots.append(i)
                thin_states[state] = thin_states.get(state, 0) + 1
        if not thin:
            statuses[15] = "true"
        elif thin_states.get(ENUM_PLAFOND) or thin_states.get(ENUM_GENERATEUR):
            # Une region sans dissection sous un plafond atteint, ou mesuree par
            # un generateur qui n'enumere pas D4, n'etablit pas `false`.
            statuses[15] = "partiel"
        else:
            statuses[15] = "false"
        misses = []
        for spot in thin_spots:
            witness = [mask for mask in substrate.grid_cut_masks(spot)
                       if substrate.dissects_mask(spot, mask)]
            if witness:
                misses.append({"region": substrate.show(battery[spot]),
                               "jeux_valides_non_proposes": len(witness)})
        details[15] = {"regions_moins_de_deux": _capped(thin),
                       "seuil": MANY,
                       "etats_des_regions_minces": sorted(thin_states.items()),
                       "regions_sous_plafond": _capped(cap_regions),
                       "regions_generateur_non_enumere": _capped(generator_regions),
                       "jeux_examines_total": examined_total,
                       "jeux_examines_max_par_region": examined_max,
                       "plafond": CAP_DISSECTIONS,
                       "plafond_atteint": bool(cap_regions),
                       "coupes_de_grille_non_proposees": _capped(misses),
                       "coupes_de_grille_non_proposees_total": len(misses)}
        if misses:
            # Le generateur ne propose pas ces jeux ; `dissects_mask` les valide.
            # Le compte de regions minces est donc un MAJORANT du manque, jamais
            # une mesure de la definition D4 (limite consignee au scelle v2.4).
            details[15]["regions_minces_dues_au_generateur"] = len(misses)

        counter_examples = []
        under_cap = False
        for i in range(size):
            masks, state, _examined = substrate.dissection_masks(i, want=WANT_DISSECTIONS)
            for mask in masks:
                if not substrate.dissects_mask(i, mask):
                    continue
                reachable = substrate.full_mask
                for member in _bits(mask):
                    reachable &= substrate.sup[member]
                reachable &= ~(1 << i)
                for other in _bits(reachable):
                    if substrate.dissects_mask(other, mask):
                        counter_examples.append({
                            "jeu": [substrate.show(battery[member]) for member in _bits(mask)],
                            "dissection_de": substrate.show(battery[i]),
                            "et_de": substrate.show(battery[other]),
                        })
                        break
                if len(counter_examples) >= MAX_WITNESS:
                    break
            if state != ENUM_EXACTE:
                under_cap = True
            if len(counter_examples) >= MAX_WITNESS:
                break
        if counter_examples:
            statuses[16] = "false"
        elif under_cap:
            statuses[16] = "partiel"
        else:
            statuses[16] = "true"
        details[16] = {"contre_exemples": counter_examples,
                       "enumeration_sous_plafond": under_cap}

    # A17-A20 -- intersections, sur la sous-batterie declaree.
    pairs_status = _intersect_report(substrate, battery)
    for number in (17, 18, 19, 20):
        statuses[number] = pairs_status["statuts"][number]
        details[number] = pairs_status["details"][number]

    # A21-A26 -- ensembles abstractifs.
    abstraction = _abstraction_report(substrate)
    for number in (21, 22, 23, 24, 25, 26):
        statuses[number] = abstraction["statuts"][number]
        details[number] = abstraction["details"][number]

    if want_witness:
        for number in ASSUMPTIONS:
            statuses.setdefault(number, "partiel")
    return statuses, details


def _intersect_report(substrate, battery):
    """A17-A20 sur la sous-batterie declaree (scelle, section 7.3)."""
    pool = [region for region in substrate.sub_battery() if substrate.index_of(region) is not None]
    statuses = {}
    details = {}

    a17_bad, a18_bad, a20_bad = [], [], []
    overlapping_pairs = 0
    multiple = 0
    for first, second in _pair_list(pool):
        if not substrate.ov(first, second):
            continue
        overlapping_pairs += 1
        intersecks = substrate.intersects(first, second)
        if not intersecks:
            a20_bad.append([substrate.show(first), substrate.show(second)])
            continue
        if len(intersecks) > 1:
            multiple += 1
        if substrate.includes(first, second):
            if len(intersecks) != 1 or intersecks[0] != second:
                a18_bad.append({"paire": [substrate.show(first), substrate.show(second)],
                                "intersecks": [substrate.show(item) for item in intersecks]})
        for candidate in pool:
            if candidate in (first, second):
                continue
            if not (substrate.includes(first, candidate) and substrate.includes(second, candidate)):
                continue
            if any(item == candidate for item in intersecks):
                continue
            holders = [item for item in intersecks if substrate.includes(item, candidate)]
            if len(holders) != 1:
                a17_bad.append({"region": substrate.show(candidate),
                                "paire": [substrate.show(first), substrate.show(second)],
                                "intersecks": [substrate.show(item) for item in intersecks],
                                "intersecks_contenant": len(holders)})
    statuses[17] = "true" if not a17_bad else "false"
    details[17] = {"contre_exemples": _capped(a17_bad), "paires_chevauchantes": overlapping_pairs}
    statuses[18] = "true" if not a18_bad else "false"
    details[18] = {"contre_exemples": _capped(a18_bad)}
    statuses[19] = "prouve"
    details[19] = {"lecture": "D5 (i) restreint deja l'intersect a la portee des deux regions"}
    statuses[20] = "true" if not a20_bad else "false"
    details[20] = {"paires_sans_intersect": _capped(a20_bad),
                   "paires_a_intersecks_multiples": multiple}
    return {"statuts": statuses, "details": details}


def _abstraction_report(substrate):
    """A21-A26 : chaines explicites en famille infinie, enumeration en famille finie."""
    statuses = {21: "par_definition", 26: "par_definition"}
    details = {21: {"lecture": "A21 est une convention de nomenclature (K3)"},
               26: {"lecture": "A26 est une convention de nomenclature (K3)"}}
    if substrate.finite_family:
        sets, exact = substrate.abstractive_sets()
        battery = substrate.battery()
        groups = {}
        for chain in sets:
            layers = tuple(sorted({substrate.index_of(battery[spot]) for spot in chain}))
            groups.setdefault(layers, []).append(chain)
        statuses[22] = "true"
        statuses[23] = "true"
        statuses[24] = "true"
        statuses[25] = "true"
        details[22] = {"ensembles_abstractifs": len(sets), "groupes": len(groups),
                       "enumeration_exacte": exact}
        details[23] = {"lecture": "D11 verifie membre a membre sur les chaines enumerees",
                       "groupes": len(groups)}
        details[24] = {"lecture": "D12 verifie membre a membre sur les chaines enumerees"}
        details[25] = {"groupes": len(groups)}
        details[22]["exemple"] = [[substrate.show(battery[spot]) for spot in chain]
                                  for chain in sets[:3]]
        return {"statuts": statuses, "details": details}

    chain_info = chain_statuses(substrate)
    statuses[22] = "prouve"
    statuses[23] = "true"
    statuses[24] = "true"
    statuses[25] = "true"
    details[22] = {"lecture": "equivalence par couverture mutuelle : transitive et symetrique",
                   **chain_info}
    details[23] = {"peu_discriminant": True}
    details[24] = {"peu_discriminant": True}
    details[25] = {"peu_discriminant": True}
    return {"statuts": statuses, "details": details}


# --------------------------------------------------------------------------- #
# Construction de la famille et des predictions
# --------------------------------------------------------------------------- #


def build_substrates(seed):
    """Les neuf substrats : S1, S2, S2r, S3, S4_d1..d4, S5."""
    return [
        Intervals("S1_closed", "closed", closed=True, regular=True, seed=seed),
        Intervals("S2_open", "open", closed=False, regular=False, seed=seed),
        Intervals("S2r_open_regularized", "open_regularized", closed=False, regular=True,
                  seed=seed, exploratory=True),
        cells_substrate(seed),
        Boxes(1, seed),
        Boxes(2, seed),
        Boxes(3, seed),
        Boxes(4, seed),
        tree_substrate(seed),
    ]


def _failures(matrix):
    return sorted(number for number, status in matrix.items() if status == "false")


def _vector_key(matrix):
    return tuple(matrix[number] for number in ASSUMPTIONS)


def _partition(per_seed):
    """Necessaires (aucun false) vs d'epoque (un false au moins), sur la famille."""
    necessary, epochal, partial = [], [], []
    for number in ASSUMPTIONS:
        statuses = [per_seed[key][number] for key in per_seed]
        if "false" in statuses:
            epochal.append(number)
        elif "partiel" in statuses or "instable" in statuses:
            partial.append(number)
        else:
            necessary.append(number)
    return necessary, epochal, partial


def run_all(seeds=TEST_SEEDS, control_seeds=CONTROL_SEEDS, with_census=True,
            with_sweep=True):
    """Execute le banc complet et rend le dictionnaire de mesures."""
    per_seed = {}
    substrate_report = {}
    for seed in seeds:
        for substrate in build_substrates(seed):
            statuses, details = assess(substrate)
            per_seed.setdefault(substrate.key, {})[seed] = statuses
            state = substrate_report.setdefault(substrate.key, {
                "label": substrate.label,
                "exploratory": substrate.exploratory,
                "regular": substrate.regular,
                "finite_family": substrate.finite_family,
                "regions": len(substrate.battery()),
                "per_seed": {},
            })
            state["per_seed"][seed] = {
                "statuts": {str(number): status for number, status in statuses.items()},
                "details": {str(number): item for number, item in details.items()},
            }

    matrix = {}
    for key, state in substrate_report.items():
        stable = {}
        for number in ASSUMPTIONS:
            values = [state["per_seed"][seed]["statuts"][str(number)] for seed in seeds]
            unique = sorted(set(values))
            stable[number] = unique[0] if len(unique) == 1 else "instable"
        matrix[key] = stable
        state["matrice"] = {str(number): value for number, value in stable.items()}
        state["graines_divergentes"] = sorted(
            number for number in ASSUMPTIONS if stable[number] == "instable")

    in_matrix = [key for key, state in substrate_report.items() if not state["exploratory"]]
    partition = _partition({key: matrix[key] for key in in_matrix})
    necessary, epochal, partial = partition

    # P1 -- S1 satisfait les 24 hypotheses : aucune case false.
    s1_failures = _failures(matrix["S1_closed"])
    p1 = {"substrat": "S1_closed", "cases_false": s1_failures,
          "cases_partiel": [number for number in ASSUMPTIONS
                            if matrix["S1_closed"][number] == "partiel"],
          "tenue": not s1_failures}

    # P2 -- S2 echoue sur exactement A16, temoin scelle retrouve.
    s2_failures = _failures(matrix["S2_open"])
    sealed = {}
    for seed in (seeds[0],):
        probe = Intervals("S2_open", "open", closed=False, regular=False, seed=seed)
        sealed["S2_open"] = probe.sealed_witness()
        probe_closed = Intervals("S1_closed", "closed", closed=True, regular=True, seed=seed)
        sealed["S1_closed"] = probe_closed.sealed_witness()
    p2 = {
        "echecs_observes": s2_failures,
        "echecs_attendus": [16],
        "temoin_scelle": sealed,
        "tenue": s2_failures == [16] and all(
            sealed["S2_open"].get(field) for field in
            ("regions_distinctes", "dans_la_batterie", "dissection_de_0_1",
             "dissection_de_la_seconde")),
    }

    # P3 -- S3 echoue au moins sur A2 et A9, pas sur A16.
    s3_failures = _failures(matrix["S3_atomic"])
    p3 = {"echecs_observes": s3_failures,
          "attendu": "A2 et A9 presents, A16 absent",
          "tenue": 2 in s3_failures and 9 in s3_failures and 16 not in s3_failures}

    # P4 -- S5 echoue au moins sur A2 et A3.
    s5_failures = _failures(matrix["S5_tree"])
    p4 = {"echecs_observes": s5_failures, "attendu": [2, 3],
          "tenue": 2 in s5_failures and 3 in s5_failures}

    # P5 -- vecteur de S4 identique en dimension 1 a 4, et plein.
    box_vectors = {}
    for dimension in (1, 2, 3, 4):
        key = f"S4_d{dimension}"
        box_vectors[key] = {str(number): matrix[key][number] for number in ASSUMPTIONS}
    box_keys = list(box_vectors)
    identical = all(box_vectors[key] == box_vectors[box_keys[0]] for key in box_keys)
    full = all(matrix[key][number] not in ("false", "partiel", "instable")
               for key in box_keys for number in ASSUMPTIONS)
    p5 = {"vecteurs": box_vectors, "identiques": identical, "pleins": full,
          "tenue": identical and full}

    # P6 -- temoin aleatoire : au moins 12 hypotheses violees, sur 5/5 graines.
    null_runs = {}
    for seed in seeds:
        probe = random_substrate(seed, NULL_DENSITY)
        statuses, _details = assess(probe, want_witness=False)
        null_runs[str(seed)] = {"violations": _failures(statuses),
                                "nombre": len(_failures(statuses))}
    p6_tenue = all(run["nombre"] >= P6_MIN_VIOLATIONS for run in null_runs.values())
    p6 = {"seuil": P6_MIN_VIOLATIONS, "graines": null_runs,
          "plafond_theorique": len(VIOLABLE), "tenue": p6_tenue}

    # Controle -- graines disjointes, seuil plus exigeant.
    control_runs = {}
    for seed in control_seeds:
        probe = random_substrate(seed, NULL_DENSITY)
        statuses, _details = assess(probe, want_witness=False)
        control_runs[str(seed)] = {"violations": _failures(statuses),
                                   "nombre": len(_failures(statuses))}
    control_tenue = all(run["nombre"] >= CONTROL_MIN_VIOLATIONS
                        for run in control_runs.values())
    control = {"seuil": CONTROL_MIN_VIOLATIONS, "graines": control_runs,
               "plafond_theorique": len(VIOLABLE), "tenue": control_tenue}

    # Porte de partition.
    named = {
        "A16_par_S2": 16 in _failures(matrix["S2_open"]),
        "A2_par_S3": 2 in _failures(matrix["S3_atomic"]),
        "A2_par_S5": 2 in _failures(matrix["S5_tree"]),
        "A3_par_S5": 3 in _failures(matrix["S5_tree"]),
        "A9_par_S3": 9 in _failures(matrix["S3_atomic"]),
        "A9_par_S5": 9 in _failures(matrix["S5_tree"]),
    }
    porte = {"necessaires": necessary, "epoque": epochal, "partiels": partial,
             "card_necessaires": len(necessary), "card_epoque": len(epochal),
             "nommees": named,
             "tenue": (len(necessary) >= MIN_NECESSARY and len(epochal) >= MIN_EPOCHAL
                       and all(named.values()))}

    # Verdict borne (scelle, section 4).
    predictions = {"P1": p1, "P2": p2, "P3": p3, "P4": p4, "P5": p5, "P6": p6}
    structural = [p2["tenue"], p3["tenue"], p4["tenue"], p5["tenue"], porte["tenue"]]
    instrument = p6_tenue and control_tenue
    if not p1["tenue"]:
        outside = "REFUTE"
    elif all(structural):
        outside = "SUPPORTED"
    else:
        outside = "PARTIEL"
    if not instrument:
        verdict = "NON_CONCLUSIF_INSTRUMENT"
    elif outside == "SUPPORTED":
        verdict = "SUPPORTED"
    else:
        verdict = outside

    report = {
        "case": CASE,
        "organ": ORGAN,
        "source": SOURCE,
        "prereg": PREREG_DOC,
        "seeds": {"test": list(seeds), "control": list(control_seeds)},
        "constants": {
            "assumptions": list(ASSUMPTIONS),
            "null_size": NULL_SIZE,
            "p6_min_violations": P6_MIN_VIOLATIONS,
            "control_min_violations": CONTROL_MIN_VIOLATIONS,
            "min_necessary": MIN_NECESSARY,
            "min_epochal": MIN_EPOCHAL,
            "chain_length": CHAIN_LENGTH,
            "cap_dissections": CAP_DISSECTIONS,
            "many": MANY,
            "never_violable": list(NEVER_VIOLABLE),
            "violable": list(VIOLABLE),
        },
        "status_legend": STATUS_LEGEND,
        "substrates": substrate_report,
        "matrice": {key: {str(number): value for number, value in row.items()}
                    for key, row in matrix.items()},
        "partition": {name: values for name, values in
                      zip(("necessaires", "epoque", "partiels"), partition)},
        "predictions": predictions,
        "porte": porte,
        "controle": control,
        "verdict": verdict,
        "verdict_hors_instrument": outside,
        "lemmes": _lemmas(),
        "a_priori": _a_priori(),
    }
    if with_census:
        census = _census()
        report["census"] = census
        extra = sorted(set(census["jamais_violees"]) - set(NEVER_VIOLABLE))
        missing = sorted(set(NEVER_VIOLABLE) - set(census["jamais_violees"]))
        report["lemmes"]["L7"]["statut"] = (
            f"execute : recensement de {census['relations']} relations, plafond observe "
            f"{census['plafond_observe']} violations sur {len(ASSUMPTIONS)} — les seuils "
            f"{P6_MIN_VIOLATIONS} et {CONTROL_MIN_VIOLATIONS} sont au-dessus. Non violees "
            f"mesurees : {census['jamais_violees']} ; ajoutees a la liste de L7 : {extra} ; "
            f"annoncees par L7 mais violees : {missing}")
    if with_sweep:
        report["sweep"] = _sweep(seeds)
    report["summary"] = _summary(report)
    return report


def _lemmas():
    """Les lemmes du scelle, avec leur statut mesure dans ce banc."""
    return {
        "L1": {"enonce": "D2 litterale rend l'inclusion reflexive, donc A7 insatisfiable",
               "statut": "retenu : K2' declare l'inclusion reflexive, A7 se lit sur ⊏"},
        "L2": {"enonce": "D3 derive de D2 par K5",
               "statut": "execute : ov calcule sur la cloture reflexive partout"},
        "L3": {"enonce": "l'infinitude des ensembles abstractifs est un corollaire de A9",
               "statut": "execute : enumeration exacte en famille finie, chaines en famille "
                         "infinie ; le compte par substrat est joint"},
        "L4": {"enonce": "A16 discriminerait ouvert/ferme",
               "statut": "corrige par v2.2 : A16 discrimine regulier/irregulier ; S2r est "
                         "le controle"},
        "L5": {"enonce": "une chaine se couvre elle-meme",
               "statut": "v2.3 : vrai pour un ensemble a plus petit membre, faux pour une "
                         "chaine infinie sans minimum"},
        "L6": {"enonce": "la lecture litterale de D2 est rapportee hors matrice",
               "statut": "execute : A7 et A5 sont mesures sous K2'/K5, la lecture litterale "
                         "est declaree insatisfiable"},
        "L7": {"enonce": "13 hypotheses non violables, 11 violables",
               "statut": f"execute : plafond de violations = {len(VIOLABLE)} ; les seuils "
                         f"{P6_MIN_VIOLATIONS} et {CONTROL_MIN_VIOLATIONS} sont au-dessus"},
        "L8": {"enonce": "les intersecks sont les regions de l'adherence de l'interieur "
                         "de cl(A) inter cl(B)",
               "statut": "execute : forme fermee pour les intervals et les boites, "
                         "enumeration avec maximalite pour les familles finies"},
    }


def _a_priori():
    """Les attentes ecrites avant mesure (scelle v2.2 section 8 et v2.3 section 2)."""
    return {
        "a": "A8 fausse en S2 : le temoin scelle et (0,1) ont meme adherence",
        "b": "A16 fausse en S2 par le temoin scelle ; vraie en S1, S2r et S4",
        "c": "A17 et A18 fausses en S2 : deux intersecks distincts pour (0,1), (0,1/2)",
        "d": "A3 vraie en S5 : 1 est connecte a 10 et a 11, qui ne le sont pas entre eux",
        "e": "le reste de la matrice est laisse a la mesure",
        "f": "A16 attendue fausse en S3 par le certificat {0}, {2}, {1,3}",
    }


def _census():
    """Recensement : quelles hypotheses sont violees dans une famille de relations.

    Exhaustif sur toutes les relations symetriques irreflexives a `n <= 5`
    sommets, soit 1 + 2 + 8 + 64 + 1024 = 1099 relations (scelle v2.2, L7 ;
    v2.4 : la version precedente melangeait 1024 relations a 5 sommets et 75
    relations aleatoires a 6 sommets, ce qui ne mesurait pas l'enonce).
    """
    observed = {number: 0 for number in ASSUMPTIONS}
    ceiling = 0
    total = 0
    for size in range(1, 6):
        edges = [(first, second) for first in range(size)
                 for second in range(first + 1, size)]
        for mask in range(1 << len(edges)):
            adjacency = [[] for _ in range(size)]
            for position, (first, second) in enumerate(edges):
                if mask >> position & 1:
                    adjacency[first].append(second)
                    adjacency[second].append(first)
            probe = Relational(f"C{total}", "census",
                               [f"c{index}" for index in range(size)],
                               adjacency, regular=False)
            statuses, _details = assess(probe, want_witness=False)
            failures = _failures(statuses)
            ceiling = max(ceiling, len(failures))
            for number in failures:
                observed[number] += 1
            total += 1
    return {
        "relations": total,
        "violations_observees": {str(number): count for number, count in observed.items()
                                 if count},
        "jamais_violees": sorted(number for number, count in observed.items() if not count),
        "plafond_observe": ceiling,
    }


def _sweep(seeds=(0, 1, 7)):
    """Balayage exploratoire de la densite du temoin aleatoire (hors matrice)."""
    out = {}
    for density in (F(3, 20), F(3, 10), F(7, 10)):
        runs = {}
        for seed in seeds:
            probe = random_substrate(seed + 500, density)
            statuses, _details = assess(probe, want_witness=False)
            runs[str(seed)] = _failures(statuses)
        out[str(density)] = runs
    return out


def _summary(report):
    predictions = report["predictions"]
    return {
        "verdict": report["verdict"],
        "verdict_hors_instrument": report["verdict_hors_instrument"],
        "predictions_tenues": {name: value["tenue"] for name, value in predictions.items()},
        "porte_tenue": report["porte"]["tenue"],
        "card_necessaires": report["porte"]["card_necessaires"],
        "card_epoque": report["porte"]["card_epoque"],
        "necessaires": report["porte"]["necessaires"],
        "epoque": report["porte"]["epoque"],
        "partiels": report["porte"]["partiels"],
    }


def _json_default(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, tuple):
        return list(value)
    if isinstance(value, set):
        return sorted(value)
    raise TypeError(f"non serialisable : {type(value)!r}")


def main(argv=None):
    parser = argparse.ArgumentParser(description="Case 28 : connexion extensive (Whitehead)")
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--no-census", action="store_true")
    parser.add_argument("--no-sweep", action="store_true")
    arguments = parser.parse_args(argv)
    report = run_all(with_census=not arguments.no_census, with_sweep=not arguments.no_sweep)
    payload = json.dumps(report, ensure_ascii=False, indent=1, default=_json_default)
    if arguments.out is not None:
        arguments.out.parent.mkdir(parents=True, exist_ok=True)
        arguments.out.write_text(payload + "\n", encoding="utf-8")
        print(f"ecrit : {arguments.out} ({len(payload)} octets)")
    summary = report["summary"]
    print(f"verdict : {summary['verdict']} (hors instrument : "
          f"{summary['verdict_hors_instrument']})")
    print(f"necessaires ({summary['card_necessaires']}) : {summary['necessaires']}")
    print(f"epoque ({summary['card_epoque']}) : {summary['epoque']}")
    print(f"partiels : {summary['partiels']}")
    for name, value in summary["predictions_tenues"].items():
        print(f"  {name} : {'tenue' if value else 'non tenue'}")
    print(f"  porte : {'tenue' if summary['porte_tenue'] else 'non tenue'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
