"""inference_trace -- trace verifiable des regles d'inference Sudoku (#26242 volet 3).

Ce module instrumente les techniques humaines du carnet
``Sudoku-08-HumanStrategies-Python.ipynb`` pour produire une **trace
verifiable** : chaque etape (placement ou elimination de candidats) est
controlee independamment contre l'oracle exact ``dlx_certificates``.

Frontiere « sans gomme » (inference pure vs recherche encapsulee) :

    Une etape est de l'INFERENCE PURE si et seulement si sa justification est
    une regle logique locale (naked/hidden single, naked pair, pointing pair,
    X-Wing) dont la conclusion se verifie SANS essai ni retour arriere. Le
    ``_backtrack`` du solveur du carnet 08 -- une recherche par essai/erreur --
    est DESACTIVE ici : la couverture mesuree est celle de l'inference pure
    seule, et les grilles non resolues sont conservees comme temoins de la
    frontiere (la ou l'inference pure s'arrete).

Copie pedagogique declaree (regle organ-first) : les cinq techniques du volet 3
sont reprises du carnet 08 et instrumentees ; l'organe natif de verification est
``dlx_certificates.solve_certificate`` (oracle exact, deja certifie #22375),
invoque tel quel -- aucune reimplementation du moteur DLX.

Lot 2 (#27533, onboarding par lots) : six regles supplementaires --
``naked_triple``, ``naked_quad``, ``hidden_pair``, ``hidden_triple``,
``hidden_quad``, ``locked_claiming`` -- implementees depuis leur definition
mathematique (taxonomie HoDoKu/sudokuwiki ; cf. la carte technique x depots de
l'issue #27533), sans copie de code des depots sources. Les noms ``Step.rule``
sont geles ici : le volet 4 (Lean) prouvera la correction de ces regles nommees.

Lot 3 (#27533) : fish d'ordre 3 et 4 -- ``swordfish`` et ``jellyfish``,
generalisation du X-Wing en base lignes OU colonnes (le ``x_wing`` du volet 3
reste base lignes uniquement, non modifie ; noms geles). Meme discipline :
definition mathematique, aucune copie de code des depots sources.

Lot 4 (#27533) : wings -- ``xy_wing`` (portage de la cellule 52 du carnet 08,
meme semantique : pivot bi-valeur, chaque pince bi-valeur partage exactement
une valeur distincte du pivot, elimination sur l'intersection des visees des
deux pinces) et ``xyz_wing`` (pivot tri-valeur, elimination sur l'intersection
des visees des trois cases). Meme discipline : definition mathematique,
aucune copie de code des depots sources, noms geles.

Verifiabilite : le corpus #26426 livre des grilles a solution UNIQUE (statut
``exhausted``, ``solutions_found == 1``). Une elimination ``(cell, value)`` est
donc valide si et seulement si la solution unique ne place PAS ``value`` en
``cell`` ; un placement ``(cell, value)`` est valide ssi la solution unique y
place ``value``. Chaque etape de la trace est ainsi rejetee ou acceptee par
l'oracle, independamment des autres etapes.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

from dlx_certificates import solve_certificate, StopStatus

# ---------------------------------------------------------------------------
# Etat d'une grille : valeurs placees + candidats par case
# ---------------------------------------------------------------------------

Grid = List[List[int]]           # 9x9, 0 = vide
Cands = List[List[Set[int]]]     # 9x9 ensembles de candidats


def _peers(row: int, col: int) -> List[Tuple[int, int]]:
    """Cases de la meme ligne, colonne et bloc (hors la case elle-meme)."""
    out = {(row, c) for c in range(9)} | {(r, col) for r in range(9)}
    br, bc = 3 * (row // 3), 3 * (col // 3)
    out |= {(r, c) for r in range(br, br + 3) for c in range(bc, bc + 3)}
    out.discard((row, col))
    return sorted(out)


def parse_grid(puzzle: str) -> Grid:
    s = puzzle.replace(".", "0").replace(" ", "").replace("\n", "")
    if len(s) != 81:
        raise ValueError(f"81 caracteres attendus, recu {len(s)}")
    return [[int(s[r * 9 + c]) for c in range(9)] for r in range(9)]


def grid_to_string(grid: Grid) -> str:
    return "".join(str(grid[r][c]) for r in range(9) for c in range(9))


def init_candidates(grid: Grid) -> Cands:
    """Candidats initiaux : valeurs non presentes dans les pairs deja places."""
    cands: Cands = [[set() for _ in range(9)] for _ in range(9)]
    for r in range(9):
        for c in range(9):
            if grid[r][c] == 0:
                used = {grid[pr][pc] for pr, pc in _peers(r, c)}
                cands[r][c] = set(range(1, 10)) - used
    return cands


# ---------------------------------------------------------------------------
# Trace : une etape verifiable
# ---------------------------------------------------------------------------


@dataclass
class Step:
    """Une etape d'inference pure, verifiable independamment.

    Attributes:
        index: rang de l'etape dans la trace (0-based)
        rule: nom precis de la regle (cf. ``InferenceSolver.RULE_ORDER`` :
            singles, tuples nus et caches d'ordre 2 a 4, candidats verrouilles,
            X-Wing, Swordfish, Jellyfish) -- le volet 4 (Lean) prouvera la
            correction de ces regles nommees
        premises: justification lisible (cases/valeurs qui fondent la regle)
        placements: [(row, col, value)] valeurs placees par cette etape
        eliminations: [(row, col, value)] candidats elimines par cette etape
        grid_after: grille 81 caracteres APRES l'etape (etat resultat)
    """

    index: int
    rule: str
    premises: str
    placements: List[Tuple[int, int, int]] = field(default_factory=list)
    eliminations: List[Tuple[int, int, int]] = field(default_factory=list)
    grid_after: str = ""

    def to_dict(self) -> Dict:
        return {
            "index": self.index,
            "rule": self.rule,
            "premises": self.premises,
            "placements": self.placements,
            "eliminations": self.eliminations,
            "grid_after": self.grid_after,
        }


@dataclass
class Trace:
    """Trace complete d'une resolution par inference pure."""

    puzzle: str
    steps: List[Step] = field(default_factory=list)
    solved: bool = False
    stalled: bool = False   # True si l'inference pure s'arrete sans resoudre

    def to_dict(self) -> Dict:
        return {
            "puzzle": self.puzzle,
            "solved": self.solved,
            "stalled": self.stalled,
            "n_steps": len(self.steps),
            "steps": [s.to_dict() for s in self.steps],
        }


# ---------------------------------------------------------------------------
# Solveur instrumente : regles du carnet 08 (volet 3) + lot 2 de #27533,
# SANS backtrack
# ---------------------------------------------------------------------------


class InferenceSolver:
    """Resolution par inference pure, tracee et verifiable (sans recherche)."""

    RULE_ORDER = ("naked_single", "hidden_single", "naked_pair", "naked_triple",
                  "naked_quad", "hidden_pair", "hidden_triple", "hidden_quad",
                  "pointing_pair", "locked_claiming", "x_wing", "swordfish",
                  "jellyfish", "xy_wing", "xyz_wing")

    def __init__(self, puzzle: str):
        self.grid = parse_grid(puzzle)
        self.cands = init_candidates(self.grid)
        self.puzzle = grid_to_string(self.grid)

    # -- utilitaires --------------------------------------------------------

    def is_solved(self) -> bool:
        return all(self.grid[r][c] != 0 for r in range(9) for c in range(9))

    def _place(self, r: int, c: int, v: int) -> List[Tuple[int, int, int]]:
        """Place v en (r,c), retire le candidat des pairs ; rend les eliminations."""
        self.grid[r][c] = v
        self.cands[r][c] = set()
        elims: List[Tuple[int, int, int]] = []
        for pr, pc in _peers(r, c):
            if self.grid[pr][pc] == 0 and v in self.cands[pr][pc]:
                self.cands[pr][pc].discard(v)
                elims.append((pr, pc, v))
        return elims

    # -- regles (copie instrumentee du carnet 08) ---------------------------

    def _naked_single(self) -> Optional[Step]:
        for r in range(9):
            for c in range(9):
                if self.grid[r][c] == 0 and len(self.cands[r][c]) == 1:
                    v = next(iter(self.cands[r][c]))
                    elims = self._place(r, c, v)
                    return Step(0, "naked_single",
                                f"case ({r},{c}) n'a qu'un candidat : {v}",
                                placements=[(r, c, v)], eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    def _hidden_single(self) -> Optional[Step]:
        units = (
            [[(r, c) for c in range(9)] for r in range(9)]                       # lignes
            + [[(r, c) for r in range(9)] for c in range(9)]                     # colonnes
            + [[(3 * br + i, 3 * bc + j) for i in range(3) for j in range(3)]
               for br in range(3) for bc in range(3)]                            # blocs
        )
        for unit in units:
            for v in range(1, 10):
                spots = [(r, c) for (r, c) in unit
                         if self.grid[r][c] == 0 and v in self.cands[r][c]]
                if len(spots) == 1:
                    r, c = spots[0]
                    elims = self._place(r, c, v)
                    return Step(0, "hidden_single",
                                f"valeur {v} n'apparait qu'en ({r},{c}) dans son unite",
                                placements=[(r, c, v)], eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    def _naked_pair(self) -> Optional[Step]:
        units = (
            [("row", r, [(r, c) for c in range(9)]) for r in range(9)]
            + [("col", c, [(r, c) for r in range(9)]) for c in range(9)]
            + [("block", (br, bc), [(3 * br + i, 3 * bc + j)
                for i in range(3) for j in range(3)])
               for br in range(3) for bc in range(3)]
        )
        for unit_type, _, cells in units:
            pairs = [(r, c) for (r, c) in cells
                     if self.grid[r][c] == 0 and len(self.cands[r][c]) == 2]
            for i in range(len(pairs)):
                for j in range(i + 1, len(pairs)):
                    (r1, c1), (r2, c2) = pairs[i], pairs[j]
                    if self.cands[r1][c1] == self.cands[r2][c2]:
                        vals = self.cands[r1][c1]
                        elims: List[Tuple[int, int, int]] = []
                        for (r, c) in cells:
                            if (r, c) in (pairs[i], pairs[j]) or self.grid[r][c] != 0:
                                continue
                            for v in list(vals):
                                if v in self.cands[r][c]:
                                    self.cands[r][c].discard(v)
                                    elims.append((r, c, v))
                        if elims:
                            return Step(0, "naked_pair",
                                        f"({r1},{c1}) et ({r2},{c2}) partagent "
                                        f"exactement {sorted(vals)} ({unit_type})",
                                        eliminations=elims,
                                        grid_after=grid_to_string(self.grid))
        return None

    def _pointing_pair(self) -> Optional[Step]:
        for br in range(3):
            for bc in range(3):
                for v in range(1, 10):
                    spots = [(3 * br + i, 3 * bc + j) for i in range(3) for j in range(3)
                             if self.grid[3 * br + i][3 * bc + j] == 0
                             and v in self.cands[3 * br + i][3 * bc + j]]
                    if len(spots) < 2:
                        continue
                    rows = {s[0] for s in spots}
                    cols = {s[1] for s in spots}
                    elims: List[Tuple[int, int, int]] = []
                    if len(rows) == 1:
                        r = spots[0][0]
                        for c in range(9):
                            if c // 3 != bc and self.grid[r][c] == 0 and v in self.cands[r][c]:
                                self.cands[r][c].discard(v)
                                elims.append((r, c, v))
                    elif len(cols) == 1:
                        c = spots[0][1]
                        for r in range(9):
                            if r // 3 != br and self.grid[r][c] == 0 and v in self.cands[r][c]:
                                self.cands[r][c].discard(v)
                                elims.append((r, c, v))
                    if elims:
                        return Step(0, "pointing_pair",
                                    f"valeur {v} alignee dans le bloc ({br},{bc})",
                                    eliminations=elims,
                                    grid_after=grid_to_string(self.grid))
        return None

    def _x_wing(self) -> Optional[Step]:
        for v in range(1, 10):
            rows_two = []
            for r in range(9):
                cols = [c for c in range(9)
                        if self.grid[r][c] == 0 and v in self.cands[r][c]]
                if len(cols) == 2:
                    rows_two.append((r, cols))
            for i in range(len(rows_two)):
                for j in range(i + 1, len(rows_two)):
                    r1, cols1 = rows_two[i]
                    r2, cols2 = rows_two[j]
                    if cols1 == cols2:
                        elims: List[Tuple[int, int, int]] = []
                        for c in cols1:
                            for r in range(9):
                                if r not in (r1, r2) and self.grid[r][c] == 0 \
                                        and v in self.cands[r][c]:
                                    self.cands[r][c].discard(v)
                                    elims.append((r, c, v))
                        if elims:
                            return Step(0, "x_wing",
                                        f"valeur {v} : lignes {r1},{r2} partagent "
                                        f"colonnes {cols1}",
                                        eliminations=elims,
                                        grid_after=grid_to_string(self.grid))
        return None

    # -- lot 2 (#27533) : tuples nus/caches et candidats verrouilles --------

    def _all_units(self) -> List[Tuple[str, List[Tuple[int, int]]]]:
        """Les 27 unites (9 lignes, 9 colonnes, 9 blocs) avec leurs cases."""
        units: List[Tuple[str, List[Tuple[int, int]]]] = []
        units += [("ligne", [(r, c) for c in range(9)]) for r in range(9)]
        units += [("colonne", [(r, c) for r in range(9)]) for c in range(9)]
        units += [("bloc", [(3 * br + i, 3 * bc + j)
                            for i in range(3) for j in range(3)])
                  for br in range(3) for bc in range(3)]
        return units

    def _naked_tuple(self, n: int, rule_name: str) -> Optional[Step]:
        """Tuple nu d'ordre n : n cases vides d'une unite dont l'union des
        candidats compte exactement n valeurs -- ces valeurs occupent ces n
        cases, donc elles sont eliminees des AUTRES cases de l'unite.

        Couplage d'ordre (invariant) : dans la boucle de resolution, aucune
        case a candidat unique n'existe au moment de ce scan, car
        ``naked_single`` precede les tuples dans ``RULE_ORDER`` et chaque pas
        reprend au sommet (une elimination peut reduire une case a un seul
        candidat, aussitot consomme au tour suivant). Cet ordre n'est PAS une
        condition de correction : le filtre ``2 <= len(cands) <= n`` exclut
        structurellement les cases a candidat unique des combos, donc la
        regle reste correcte meme appelee hors ordre (test negatif
        ``test_naked_tuple_ignores_single_candidate_cells``).
        """
        for unit_type, cells in self._all_units():
            empty = [(r, c) for (r, c) in cells if self.grid[r][c] == 0]
            eligible = [(r, c) for (r, c) in empty
                        if 2 <= len(self.cands[r][c]) <= n]
            for combo in itertools.combinations(eligible, n):
                vals: Set[int] = set()
                for (r, c) in combo:
                    vals |= self.cands[r][c]
                if len(vals) != n:
                    continue
                elims: List[Tuple[int, int, int]] = []
                for (r, c) in empty:
                    if (r, c) in combo:
                        continue
                    for v in sorted(vals):
                        if v in self.cands[r][c]:
                            self.cands[r][c].discard(v)
                            elims.append((r, c, v))
                if elims:
                    cells_txt = ", ".join(f"({r},{c})" for (r, c) in combo)
                    return Step(0, rule_name,
                                f"{cells_txt} ne portent que {sorted(vals)} "
                                f"({unit_type}, tuple nu d'ordre {n})",
                                eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    def _naked_triple(self) -> Optional[Step]:
        return self._naked_tuple(3, "naked_triple")

    def _naked_quad(self) -> Optional[Step]:
        return self._naked_tuple(4, "naked_quad")

    def _hidden_tuple(self, n: int, rule_name: str) -> Optional[Step]:
        """Tuple cache d'ordre n : n valeurs d'une unite dont les positions
        candidates (cases vides) sont confinees a n cases exactement -- ces n
        valeurs occupent ces n cases, donc tout AUTRE candidat de ces cases
        est elimine.
        """
        for unit_type, cells in self._all_units():
            empty = [(r, c) for (r, c) in cells if self.grid[r][c] == 0]
            digit_cells: Dict[int, List[Tuple[int, int]]] = {}
            for v in range(1, 10):
                spots_v = [(r, c) for (r, c) in empty if v in self.cands[r][c]]
                if spots_v:
                    digit_cells[v] = spots_v
            for digits in itertools.combinations(sorted(digit_cells), n):
                spots: Set[Tuple[int, int]] = set()
                confined = True
                for v in digits:
                    if len(digit_cells[v]) > n:
                        confined = False
                        break
                    spots.update(digit_cells[v])
                if not confined or len(spots) != n:
                    continue
                elims: List[Tuple[int, int, int]] = []
                for (r, c) in sorted(spots):
                    for v in sorted(self.cands[r][c]):
                        if v not in digits:
                            self.cands[r][c].discard(v)
                            elims.append((r, c, v))
                if elims:
                    cells_txt = ", ".join(f"({r},{c})" for (r, c) in sorted(spots))
                    return Step(0, rule_name,
                                f"valeurs {list(digits)} confinees a "
                                f"{cells_txt} ({unit_type}, tuple cache d'ordre {n})",
                                eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    def _hidden_pair(self) -> Optional[Step]:
        return self._hidden_tuple(2, "hidden_pair")

    def _hidden_triple(self) -> Optional[Step]:
        return self._hidden_tuple(3, "hidden_triple")

    def _hidden_quad(self) -> Optional[Step]:
        return self._hidden_tuple(4, "hidden_quad")

    def _locked_claiming(self) -> Optional[Step]:
        """Candidats verrouilles (claiming, miroir de pointing_pair) : toutes
        les positions candidates d'une valeur dans une ligne (resp. colonne)
        sont confinees a un seul bloc -- la valeur est eliminee du reste de
        ce bloc.
        """
        for unit_type in ("ligne", "colonne"):
            for idx in range(9):
                for v in range(1, 10):
                    spots: List[Tuple[int, int]] = []
                    for other in range(9):
                        r, c = (idx, other) if unit_type == "ligne" else (other, idx)
                        if self.grid[r][c] == 0 and v in self.cands[r][c]:
                            spots.append((r, c))
                    if len(spots) < 2:
                        continue
                    blocks = {(r // 3, c // 3) for (r, c) in spots}
                    if len(blocks) != 1:
                        continue
                    br, bc = blocks.pop()
                    elims: List[Tuple[int, int, int]] = []
                    for i in range(3):
                        for j in range(3):
                            r, c = 3 * br + i, 3 * bc + j
                            if (r, c) in spots or self.grid[r][c] != 0:
                                continue
                            if v in self.cands[r][c]:
                                self.cands[r][c].discard(v)
                                elims.append((r, c, v))
                    if elims:
                        return Step(0, "locked_claiming",
                                    f"valeur {v} de la {unit_type} {idx} "
                                    f"confinee au bloc ({br},{bc})",
                                    eliminations=elims,
                                    grid_after=grid_to_string(self.grid))
        return None

    # -- lot 3 (#27533) : fish d'ordre 3 et 4 (swordfish, jellyfish) -------

    def _unit_cells(self, unit_type: str, idx: int) -> List[Tuple[int, int]]:
        """Les 9 cases de l'unite ``unit_type`` (ligne/colonne) d'indice ``idx``."""
        if unit_type == "ligne":
            return [(idx, c) for c in range(9)]
        return [(r, idx) for r in range(9)]

    def _fish(self, n: int, rule_name: str) -> Optional[Step]:
        """Fish d'ordre n (Swordfish n=3, Jellyfish n=4) : n unites de BASE
        (lignes ou colonnes) dont les positions candidates d'une valeur
        vivent dans exactement n unites de COUVERTURE de l'autre orientation
        -- la valeur est eliminee du reste des unites de couverture.

        Le X-Wing du volet 3 couvre le fish n=2 en base lignes uniquement ;
        cette generalisation couvre les DEUX orientations de base pour n=3
        et n=4 (l'extension base colonnes du n=2 reste a la regle ``x_wing``
        du volet 3, non reprise ici).

        Couplage d'ordre (invariant) : ``naked_single``/``hidden_single``
        precedent dans ``RULE_ORDER`` et chaque pas reprend au sommet, donc
        dans la boucle une unite a position unique est consommee avant ce
        scan ; le filtre ``2 <= len(spots) <= n`` exclut en outre
        structurellement les unites a 0 ou 1 position des bases, et la
        regle reste correcte appelee hors ordre (test negatif
        ``test_fish_ignores_units_with_single_position``).
        """
        for base_type in ("ligne", "colonne"):
            cover_is_row = base_type == "colonne"
            for v in range(1, 10):
                bases: List[Tuple[int, List[Tuple[int, int]]]] = []
                for idx in range(9):
                    spots = [(r, c) for (r, c) in self._unit_cells(base_type, idx)
                             if self.grid[r][c] == 0 and v in self.cands[r][c]]
                    if 2 <= len(spots) <= n:
                        bases.append((idx, spots))
                for combo in itertools.combinations(bases, n):
                    positions = [p for (_, spots) in combo for p in spots]
                    covers = {(p[0] if cover_is_row else p[1]) for p in positions}
                    if len(covers) != n:
                        continue
                    base_idxs = tuple(sorted(idx for (idx, _) in combo))
                    elims: List[Tuple[int, int, int]] = []
                    for k in covers:
                        for (r, c) in self._unit_cells("ligne" if cover_is_row
                                                       else "colonne", k):
                            if (r, c) in positions or self.grid[r][c] != 0:
                                continue
                            if v in self.cands[r][c]:
                                self.cands[r][c].discard(v)
                                elims.append((r, c, v))
                    if elims:
                        return Step(0, rule_name,
                                    f"valeur {v} : {base_type}s {base_idxs} "
                                    f"couvrent les "
                                    f"{'lignes' if cover_is_row else 'colonnes'} "
                                    f"{sorted(covers)}",
                                    eliminations=elims,
                                    grid_after=grid_to_string(self.grid))
        return None

    def _swordfish(self) -> Optional[Step]:
        return self._fish(3, "swordfish")

    def _jellyfish(self) -> Optional[Step]:
        return self._fish(4, "jellyfish")

    # -- lot 4 (#27533) : wings ----------------------------------------------

    def _xy_wing(self) -> Optional[Step]:
        """XY-Wing : pivot bi-valeur {x, y} dont deux pinces bi-valeur
        {x, z} et {y, z} lui sont visibles (meme ligne, colonne ou bloc).
        Dans chaque cas possible pour le pivot, l'une des pinces vaut z,
        donc z est elimine de toute case vide visible des DEUX pinces
        (hors les trois cases de l'aile).

        Portage de la cellule 52 du carnet 08 (meme semantique) : chaque
        pince partage EXACTEMENT une valeur avec le pivot, et les deux
        ancres sont distinctes (sinon ce n'est pas une aile).

        Couplage d'ordre (invariant) : ``naked_single`` precede dans
        ``RULE_ORDER`` et chaque pas reprend au sommet, donc une case a
        candidat unique est placee avant ce scan ; les filtres
        ``len == 2`` excluent en outre structurellement les cases
        mono-valeur des pivots et pinces, et la regle reste correcte
        appelee hors ordre.
        """
        bivalue = [(r, c) for r in range(9) for c in range(9)
                   if self.grid[r][c] == 0 and len(self.cands[r][c]) == 2]
        for (pr, pc) in bivalue:
            pivot_cands = self.cands[pr][pc]
            wings = [(r, c) for (r, c) in bivalue
                     if (r, c) in _peers(pr, pc)]
            for (r1, c1), (r2, c2) in itertools.combinations(wings, 2):
                w1, w2 = self.cands[r1][c1], self.cands[r2][c2]
                anchor1 = w1 & pivot_cands
                anchor2 = w2 & pivot_cands
                if (len(anchor1) != 1 or len(anchor2) != 1
                        or anchor1 == anchor2):
                    continue
                z = next(iter(w1 - anchor1))
                if w2 - anchor2 != {z}:
                    continue
                seen = set(_peers(r1, c1)) & set(_peers(r2, c2))
                elims: List[Tuple[int, int, int]] = []
                for (r, c) in sorted(seen - {(pr, pc), (r1, c1), (r2, c2)}):
                    if self.grid[r][c] == 0 and z in self.cands[r][c]:
                        self.cands[r][c].discard(z)
                        elims.append((r, c, z))
                if elims:
                    return Step(0, "xy_wing",
                                f"pivot ({pr},{pc}) {sorted(pivot_cands)}, "
                                f"pinces ({r1},{c1}) {sorted(w1)} et "
                                f"({r2},{c2}) {sorted(w2)} : {z} elimine "
                                f"des cases visibles des deux pinces",
                                eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    def _xyz_wing(self) -> Optional[Step]:
        """XYZ-Wing : pivot tri-valeur {x, y, z} avec deux pinces
        bi-valeur {x, z} et {y, z} visibles du pivot -- quel que soit le
        cas possible pour le pivot, z sort (pivot = z, ou pince = z),
        donc z est elimine des cases vides visibles des TROIS cases
        (pivot et pinces).

        Couplage d'ordre (invariant) : comme ``_xy_wing`` -- les filtres
        ``len == 3`` (pivot) et ``len == 2`` (pinces) excluent
        structurellement les cases mono-valeur, la regle reste correcte
        appelee hors ordre.
        """
        trivalue = [(r, c) for r in range(9) for c in range(9)
                    if self.grid[r][c] == 0 and len(self.cands[r][c]) == 3]
        bivalue = [(r, c) for r in range(9) for c in range(9)
                   if self.grid[r][c] == 0 and len(self.cands[r][c]) == 2]
        for (pr, pc) in trivalue:
            xyz = self.cands[pr][pc]
            wings = [(r, c) for (r, c) in bivalue
                     if (r, c) in _peers(pr, pc) and self.cands[r][c] < xyz]
            for (r1, c1), (r2, c2) in itertools.combinations(wings, 2):
                w1, w2 = self.cands[r1][c1], self.cands[r2][c2]
                if w1 | w2 != xyz or len(w1 & w2) != 1:
                    continue
                z = next(iter(w1 & w2))
                seen = (set(_peers(pr, pc)) & set(_peers(r1, c1))
                        & set(_peers(r2, c2)))
                elims: List[Tuple[int, int, int]] = []
                for (r, c) in sorted(seen - {(pr, pc), (r1, c1), (r2, c2)}):
                    if self.grid[r][c] == 0 and z in self.cands[r][c]:
                        self.cands[r][c].discard(z)
                        elims.append((r, c, z))
                if elims:
                    return Step(0, "xyz_wing",
                                f"pivot ({pr},{pc}) {sorted(xyz)}, pinces "
                                f"({r1},{c1}) {sorted(w1)} et ({r2},{c2}) "
                                f"{sorted(w2)} : {z} elimine des cases "
                                f"visibles des trois cases",
                                eliminations=elims,
                                grid_after=grid_to_string(self.grid))
        return None

    # -- boucle de resolution ----------------------------------------------

    def solve(self, max_steps: int = 10000) -> Trace:
        """Resout par inference pure ; s'arrete (stalled) sans JAMAIS rechercher."""
        trace = Trace(puzzle=self.puzzle)
        dispatch = {
            "naked_single": self._naked_single,
            "hidden_single": self._hidden_single,
            "naked_pair": self._naked_pair,
            "naked_triple": self._naked_triple,
            "naked_quad": self._naked_quad,
            "hidden_pair": self._hidden_pair,
            "hidden_triple": self._hidden_triple,
            "hidden_quad": self._hidden_quad,
            "pointing_pair": self._pointing_pair,
            "locked_claiming": self._locked_claiming,
            "x_wing": self._x_wing,
            "swordfish": self._swordfish,
            "jellyfish": self._jellyfish,
            "xy_wing": self._xy_wing,
            "xyz_wing": self._xyz_wing,
        }
        while not self.is_solved() and len(trace.steps) < max_steps:
            progress = False
            for rule in self.RULE_ORDER:
                step = dispatch[rule]()
                if step is not None:
                    step.index = len(trace.steps)
                    trace.steps.append(step)
                    progress = True
                    break   # re-evaluer depuis la regle la plus simple
            if not progress:
                trace.stalled = True
                break
        trace.solved = self.is_solved()
        return trace


# ---------------------------------------------------------------------------
# Verification independante : chaque etape contre l'oracle exact
# ---------------------------------------------------------------------------


@dataclass
class StepVerdict:
    index: int
    rule: str
    ok: bool
    reason: str = ""


@dataclass
class TraceVerdict:
    puzzle: str
    accepted: bool
    n_steps: int
    step_verdicts: List[StepVerdict] = field(default_factory=list)
    oracle_status: str = ""
    reason: str = ""

    @property
    def n_bad(self) -> int:
        return sum(1 for v in self.step_verdicts if not v.ok)


def verify_trace(trace: Trace) -> TraceVerdict:
    """Verifie chaque etape de la trace contre la solution unique (oracle dlx).

    Toute etape dont un placement ou une elimination contredit la solution
    unique est rejetee et nommee. Le témoin negatif (regle organ-first) : une
    regle qui elimine un candidat present dans la solution est rejetee ici.
    """
    cert = solve_certificate(trace.puzzle, find_all=True, limit=2)
    if cert is None or cert.solutions_found == 0:
        return TraceVerdict(trace.puzzle, False, len(trace.steps),
                            oracle_status=StopStatus.EXHAUSTED,
                            reason="aucune solution (puzzle insatisfiable)")
    if cert.solutions_found > 1:
        return TraceVerdict(trace.puzzle, False, len(trace.steps),
                            oracle_status=cert.status,
                            reason="solution non unique : la verification par "
                                   "solution unique ne s'applique pas")
    sol = [0] * 81
    for ci, v in cert.placements:
        sol[ci] = v + 1

    verdicts: List[StepVerdict] = []
    for step in trace.steps:
        ok, reason = True, ""
        for (r, c, v) in step.placements:
            if sol[r * 9 + c] != v:
                ok, reason = False, f"placement ({r},{c})={v} contredit la solution"
                break
        if ok:
            for (r, c, v) in step.eliminations:
                if sol[r * 9 + c] == v:
                    ok = False
                    reason = (f"elimination du candidat {v} en ({r},{c}) alors "
                              f"que la solution l'y place")
                    break
        verdicts.append(StepVerdict(step.index, step.rule, ok, reason))

    accepted = all(v.ok for v in verdicts)
    return TraceVerdict(trace.puzzle, accepted, len(trace.steps),
                        step_verdicts=verdicts, oracle_status=cert.status,
                        reason="" if accepted else "etapes invalides detectees")


# ---------------------------------------------------------------------------
# Mesure de couverture sur un corpus, recherche desactivee
# ---------------------------------------------------------------------------


@dataclass
class CoverageRow:
    puzzle: str
    solved_by_inference: bool
    n_steps: int
    trace_accepted: bool
    rules_used: Dict[str, int]


def measure_coverage(puzzles: List[str]) -> List[CoverageRow]:
    """Pour chaque grille : resolution par inference pure seule + verification.

    Aucune recherche / essai / retour arriere : les grilles resolues ET non
    resolues sont conservees (temoins de la frontiere de l'inference pure).
    """
    rows: List[CoverageRow] = []
    for p in puzzles:
        solver = InferenceSolver(p)
        trace = solver.solve()
        verdict = verify_trace(trace)
        rules: Dict[str, int] = {}
        for s in trace.steps:
            rules[s.rule] = rules.get(s.rule, 0) + 1
        rows.append(CoverageRow(
            puzzle=trace.puzzle,
            solved_by_inference=trace.solved,
            n_steps=len(trace.steps),
            trace_accepted=verdict.accepted,
            rules_used=rules,
        ))
    return rows
