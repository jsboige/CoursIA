"""dlx_certificates -- certificats DLX transportables pour Sudoku (issue #22375).

Extraction fidele du moteur Dancing Links du carnet
``Sudoku-02-DancingLinks-Python.ipynb`` (cellules 9, 11, 13 -- copie verbatim,
aucune modification semantique), completee par une API de certificat :

- ``solve_certificate`` : resolution renvoyant la selection de placements,
  la correspondance ligne DLX -> (ligne, colonne, valeur), et un **statut
  d'arret** ``exhausted`` / ``limit_reached`` (jamais confondus) ;
- ``validate_certificate`` : validation par etages (domaine, doublon brut,
  conflit de cellule, completude, exact-cover par portee, indices du puzzle),
  chaque corruption etant rejete par l'etage qui la concerne -- les doublons
  bruts sont rejetes **avant** toute conversion en ensemble (celle-ci
  effacerait le doublon, le rendant indetectable) ;
- ``certificate_to_lean`` : emission d'un fichier donnees Lean consommant le
  checker calculable du lake natif (``Sudoku.Certificate``).

Module : le carnet Sudoku-02 reste la demonstration pedagogique ; ce module
est la voie reusable. Les exercices du carnet (``verify_dlx_solution``,
``count_solutions``) restent non resolus -- rien ici ne les complete.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# 1. Moteur DLX -- extraction fidele de Sudoku-02-DancingLinks-Python.ipynb
#    (cellules 9, 11 et 13, copie verbatim ; voir tests d'equivalence)
# ---------------------------------------------------------------------------


class DancingLinksNode:
    """Noeud dans la structure Dancing Links.

    Chaque noeud est connecte a 4 voisins (gauche, droite, haut, bas)
    formant une grille de listes doublement chainees circulaires.

    Attributes:
        left: Noeud a gauche dans la meme ligne
        right: Noeud a droite dans la meme ligne
        up: Noeud au-dessus dans la meme colonne
        down: Noeud en-dessous dans la meme colonne
        column: Reference vers le header de colonne
        row_id: Identifiant de la ligne (pour reconstruire la solution)
    """

    __slots__ = ["left", "right", "up", "down", "column", "row_id"]

    def __init__(self):
        self.left = self
        self.right = self
        self.up = self
        self.down = self
        self.column = None
        self.row_id = None


class ColumnHeader(DancingLinksNode):
    """Header de colonne avec compteur de taille.

    Attributes:
        size: Nombre de noeuds (1s) dans cette colonne
        name: Identifiant de la colonne (pour debug)
    """

    __slots__ = ["size", "name"]

    def __init__(self, name: int = 0):
        super().__init__()
        self.size = 0
        self.name = name
        self.column = self  # Un header pointe vers lui-meme


class DancingLinks:
    """Implementation complete de l'algorithme Dancing Links.

    Cette classe construit une matrice creuse et implemente l'Algorithm X
    de Knuth pour resoudre le probleme de couverture exacte.
    """

    def __init__(self, num_columns: int):
        """Initialise la structure avec le nombre de colonnes.

        Args:
            num_columns: Nombre de contraintes (324 pour Sudoku 9x9)
        """
        # Creer le noeud racine
        self.root = ColumnHeader(-1)

        # Creer les headers de colonnes
        self.columns: List[ColumnHeader] = []
        prev = self.root

        for i in range(num_columns):
            header = ColumnHeader(i)
            self.columns.append(header)

            # Lier horizontalement
            header.left = prev
            header.right = self.root
            prev.right = header
            self.root.left = header
            prev = header

        # Solution courante (liste d'indices de lignes)
        self.solution: List[int] = []
        self.solutions_found: List[List[int]] = []

    def add_row(self, row_id: int, columns: List[int]):
        """Ajoute une ligne avec des 1s aux colonnes specifiees.

        Args:
            row_id: Identifiant unique de la ligne
            columns: Liste des indices de colonnes ayant un 1
        """
        if not columns:
            return

        first_node = None
        prev_node = None

        for col_idx in columns:
            # Creer un nouveau noeud
            node = DancingLinksNode()
            node.row_id = row_id
            node.column = self.columns[col_idx]

            # Inserer en bas de la colonne
            col_header = self.columns[col_idx]
            node.up = col_header.up
            node.down = col_header
            col_header.up.down = node
            col_header.up = node
            col_header.size += 1

            # Lier horizontalement
            if first_node is None:
                first_node = node
                node.left = node
                node.right = node
            else:
                node.left = prev_node
                node.right = first_node
                prev_node.right = node
                first_node.left = node

            prev_node = node

    def cover(self, col: ColumnHeader):
        """Couvre une colonne (la supprime temporairement).

        Args:
            col: Header de la colonne a couvrir
        """
        # Deconnecter le header horizontalement
        col.right.left = col.left
        col.left.right = col.right

        # Parcourir vers le bas dans la colonne
        i = col.down
        while i != col:
            # Parcourir vers la droite dans la ligne
            j = i.right
            while j != i:
                # Deconnecter verticalement
                j.down.up = j.up
                j.up.down = j.down
                j.column.size -= 1
                j = j.right
            i = i.down

    def uncover(self, col: ColumnHeader):
        """Decouvre une colonne (la restaure).

        Operation inverse de cover(), executee dans l'ordre inverse.

        Args:
            col: Header de la colonne a restaurer
        """
        # Parcourir vers le haut dans la colonne
        i = col.up
        while i != col:
            # Parcourir vers la gauche dans la ligne
            j = i.left
            while j != i:
                # Reconnecter verticalement
                j.column.size += 1
                j.down.up = j
                j.up.down = j
                j = j.left
            i = i.up

        # Reconnecter le header horizontalement
        col.right.left = col
        col.left.right = col

    def choose_column(self) -> Optional[ColumnHeader]:
        """Choisit la colonne avec le moins de 1s (heuristique MRV).

        Returns:
            Le header de colonne avec le minimum de noeuds,
            ou None si toutes les colonnes sont couvertes.
        """
        min_size = float("inf")
        best_col = None

        col = self.root.right
        while col != self.root:
            if col.size < min_size:
                min_size = col.size
                best_col = col
            col = col.right

        return best_col

    def search(self, find_all: bool = True, max_count=10) -> bool:
        """Algorithme X recursif.

        Args:
            find_all: Si True, trouve toutes les solutions

        Returns:
            True si une solution est trouvee
        """
        output = 0

        # Cas de base: toutes les colonnes couvertes
        if self.root.right == self.root:
            self.solutions_found.append(self.solution.copy())
            return not find_all  # Continuer si on cherche toutes les solutions

        if len(self.solutions_found) == max_count:
            return max_count

        if max_count == 0:
            return 0

        # Choisir la colonne avec le moins de 1s
        col = self.choose_column()

        # Si une colonne est vide, impasse
        if col is None or col.size == 0:
            return 0

        # Couvrir cette colonne
        self.cover(col)

        # Essayer chaque ligne ayant un 1 dans cette colonne
        row = col.down
        while row != col:
            # Ajouter cette ligne a la solution
            self.solution.append(row.row_id)

            # Couvrir toutes les colonnes de cette ligne
            j = row.right
            while j != row:
                self.cover(j.column)
                j = j.right

            # Recursion
            output += self.search(find_all, max_count)
            if output != 0:
                if not find_all:
                    return output

            # Backtrack
            self.solution.pop()

            max_count -= 1

            # Decouvrir les colonnes dans l'ordre inverse
            j = row.left
            while j != row:
                self.uncover(j.column)
                j = j.left

            row = row.down

        # Decouvrir la colonne choisie
        self.uncover(col)
        return len(self.solutions_found)

    def search2(self, find_all: bool = True, limit: int = 10) -> bool:
        """Algorithme X avec support pour solutions multiples et limite."""
        # Cas de base : toutes les colonnes sont couvertes
        if self.root.right == self.root:
            self.solutions_found.append(self.solution.copy())
            # Si on a atteint la limite, on signale qu'il faut s'arrêter
            return True if (not find_all or len(self.solutions_found) >= limit) else False

        col = self.choose_column()
        if col is None or col.size == 0:
            return False

        self.cover(col)
        row = col.down
        while row != col:
            self.solution.append(row.row_id)

            # Couvrir les colonnes liées à cette ligne
            j = row.right
            while j != row:
                self.cover(j.column)
                j = j.right

            # Récursion : si elle retourne True, on a atteint l'arrêt demandé
            if self.search2(find_all, limit):
                if not find_all or len(self.solutions_found) >= limit:
                    # Nettoyage avant de remonter (Backtrack partiel)
                    # Note : Dans une recherche exhaustive avec arrêt brutal,
                    # le nettoyage est moins critique car on sort de la pile.
                    return True

            # Backtrack
            self.solution.pop()
            j = row.left
            while j != row:
                self.uncover(j.column)
                j = j.left

            row = row.down

        self.uncover(col)
        return len(self.solutions_found) >= limit


class SudokuGrid:
    """Representation d'une grille de Sudoku 9x9."""

    def __init__(self, cells: Optional[List[List[int]]] = None):
        if cells is None:
            self.cells = [[0] * 9 for _ in range(9)]
        else:
            self.cells = [row[:] for row in cells]

    @classmethod
    def from_string(cls, s: str) -> "SudokuGrid":
        """Cree une grille depuis une chaine de 81 caracteres."""
        s = s.replace(".", "0").replace(" ", "").replace("\n", "")
        if len(s) != 81:
            raise ValueError(f"Attendu 81 caracteres, recu {len(s)}")

        grid = cls()
        for i in range(81):
            grid.cells[i // 9][i % 9] = int(s[i])
        return grid

    def clone(self) -> "SudokuGrid":
        return SudokuGrid(self.cells)

    def is_valid(self) -> bool:
        """Verifie si la grille est une solution valide."""
        # Verifier que toutes les cellules sont remplies
        for r in range(9):
            for c in range(9):
                if self.cells[r][c] == 0:
                    return False

        # Verifier lignes
        for r in range(9):
            if len(set(self.cells[r])) != 9:
                return False

        # Verifier colonnes
        for c in range(9):
            if len(set(self.cells[r][c] for r in range(9))) != 9:
                return False

        # Verifier blocs
        for br in range(3):
            for bc in range(3):
                block = []
                for r in range(3):
                    for c in range(3):
                        block.append(self.cells[br * 3 + r][bc * 3 + c])
                if len(set(block)) != 9:
                    return False

        return True

    def __str__(self) -> str:
        lines = []
        for r in range(9):
            if r > 0 and r % 3 == 0:
                lines.append("-" * 21)
            row_str = ""
            for c in range(9):
                if c > 0 and c % 3 == 0:
                    row_str += "| "
                val = self.cells[r][c]
                row_str += (str(val) if val != 0 else ".") + " "
            lines.append(row_str)
        return "\n".join(lines)


class DLXSudokuSolver:
    """Solveur de Sudoku utilisant Dancing Links.

    Traduit le Sudoku en probleme de couverture exacte:
    - 324 colonnes (contraintes)
    - Jusqu'a 729 lignes (possibilites)
    - 4 bits a 1 par ligne
    """

    NUM_COLUMNS = 324  # 4 * 81 contraintes

    def __init__(self):
        self.call_count = 0

    def solve(self, puzzle: SudokuGrid) -> Optional[SudokuGrid]:
        """Resout le Sudoku avec Dancing Links.

        Args:
            puzzle: Grille de depart (0 = case vide)

        Returns:
            Grille resolue ou None si pas de solution
        """
        dlx, row_info = self._build_matrix(puzzle)

        # Resoudre (verbatim Sudoku-02 : le solveur historique appelle search ;
        # l'API de certificat, elle, appelle search2 -- voir solve_certificate)
        if dlx.search():
            # Reconstruire la solution
            result = puzzle.clone()
            for rid in dlx.solutions_found[0]:
                r, c, v = row_info[rid]
                result.cells[r][c] = v
            return result

        return None

    def _build_matrix(self, puzzle: SudokuGrid) -> Tuple[DancingLinks, Dict[int, Tuple[int, int, int]]]:
        """Construit la matrice de couverture exacte du puzzle.

        C'est la matrice de ``solve`` (Sudoku-02, cellule 13), exposee pour
        l'API de certificat : la correspondance ``row_id -> (r, c, v)`` --
        jusqu'ici locale au corps de ``solve`` -- devient consultable.

        Returns:
            Le couple (structure DancingLinks peuplee, correspondance des lignes).
        """
        dlx = DancingLinks(self.NUM_COLUMNS)
        row_info = {}  # row_id -> (r, c, v)
        row_id = 0

        # Construire la matrice
        for r in range(9):
            for c in range(9):
                cell_value = puzzle.cells[r][c]

                # Determiner les valeurs possibles
                if cell_value != 0:
                    # Cellule deja remplie: une seule possibilite
                    values = [cell_value]
                else:
                    # Cellule vide: toutes les valeurs 1-9
                    values = range(1, 10)

                for v in values:
                    # Calculer les 4 colonnes a mettre a 1
                    columns = self._get_columns(r, c, v)

                    # Ajouter la ligne
                    dlx.add_row(row_id, columns)
                    row_info[row_id] = (r, c, v)
                    row_id += 1

        return dlx, row_info

    def _get_columns(self, r: int, c: int, v: int) -> List[int]:
        """Calcule les 4 indices de colonnes pour un placement.

        Args:
            r: Ligne (0-8)
            c: Colonne (0-8)
            v: Valeur (1-9)

        Returns:
            Liste de 4 indices de colonnes
        """
        box = (r // 3) * 3 + (c // 3)

        return [
            r * 9 + c,                    # Cell constraint (0-80)
            81 + r * 9 + (v - 1),         # Row constraint (81-161)
            162 + c * 9 + (v - 1),        # Column constraint (162-242)
            243 + box * 9 + (v - 1)       # Box constraint (243-323)
        ]


# ---------------------------------------------------------------------------
# 2. API de certificat (nouveau, issue #22375)
# ---------------------------------------------------------------------------

#: Version du format de certificat. Toute evolution du format (champs,
#: conventions d'indices, domaine des valeurs) incremente ce numero.
CERTIFICATE_VERSION = 1

#: Conventions explicites du format (transportees dans chaque certificat) :
#:   cell_index   = r * 9 + c,  r et c dans [0, 8]
#:   value        = v - 1,      v dans [1, 9]  (valeur Sudoku -> [0, 8])
#:   placements   = liste (cell_index, value) triee par cell_index croissant
CONVENTIONS = {
    "cell_index": "r * 9 + c (r, c in [0, 8])",
    "value": "v - 1 (v in [1, 9] -> [0, 8])",
    "placements": "liste (cell_index, value), triee par cell_index croissant",
}


class StopStatus:
    """Statut d'arret de la recherche -- jamais confondu avec un denombrement.

    - ``EXHAUSTED`` : la recherche a epuise l'espace (arret naturel).
    - ``LIMIT_REACHED`` : la recherche s'est arretee sur la limite demandee ;
      d'autres solutions peuvent exister au-dela. Un unique certificat trouve
      sous limite ne prouve donc RIEN sur l'unicite.
    """

    EXHAUSTED = "exhausted"
    LIMIT_REACHED = "limit_reached"


@dataclass
class CertificateResult:
    """Resultat d'une resolution certifiee.

    Attributes:
        puzzle: chaine 81 caracteres du puzzle initial (0 = vide)
        clues: liste triee des indices du puzzle, [(cell_index, value)]
        placements: selection DLX complete, [(cell_index, value)] (81 elements)
        row_ids: identifiants DLX des lignes selectionnees, dans l'ordre de
            decouverte (correspondance ligne -> placement via row_info)
        row_info: correspondance explicite row_id -> (r, c, v)
        status: statut d'arret (exhausted / limit_reached)
        solutions_found: nombre de solutions trouvees au moment de l'arret
        version: version du format de certificat
        conventions: conventions d'indices/valeurs
    """

    puzzle: str
    clues: List[Tuple[int, int]]
    placements: List[Tuple[int, int]]
    row_ids: List[int]
    row_info: Dict[int, Tuple[int, int, int]]
    status: str
    solutions_found: int
    version: int = CERTIFICATE_VERSION
    conventions: Dict[str, str] = field(default_factory=lambda: dict(CONVENTIONS))


def clues_from_puzzle(puzzle: str) -> List[Tuple[int, int]]:
    """Extrait les indices du puzzle sous forme (cell_index, value), tries."""
    s = puzzle.replace(".", "0").replace(" ", "").replace("\n", "")
    if len(s) != 81 or not all(ch in "0123456789" for ch in s):
        raise ValueError(f"Puzzle invalide : 81 chiffres attendus, recu {len(s)} caracteres")
    return sorted(
        (i, int(ch) - 1) for i, ch in enumerate(s) if ch != "0"
    )


def solve_certificate(
    puzzle: str, find_all: bool = False, limit: int = 10
) -> Optional[CertificateResult]:
    """Resout le puzzle et renvoie un certificat transportable.

    Args:
        puzzle: chaine de 81 caracteres (0 ou '.' = vide)
        find_all: si False, premiere solution seulement ; si True, collecte
            jusqu'a ``limit`` solutions et rapporte le statut d'arret
        limit: nombre maximal de solutions collectees

    Returns:
        ``CertificateResult`` de la premiere solution (le statut porte sur la
        recherche dans son ensemble), ou None si le puzzle n'a aucune solution.
    """
    grid = SudokuGrid.from_string(puzzle)
    solver = DLXSudokuSolver()
    dlx, row_info = solver._build_matrix(grid)

    dlx.search2(find_all=True, limit=limit)

    if not dlx.solutions_found:
        return CertificateResult(
            puzzle=puzzle,
            clues=clues_from_puzzle(puzzle),
            placements=[],
            row_ids=[],
            row_info=row_info,
            status=StopStatus.EXHAUSTED,
            solutions_found=0,
        )

    # Statut : limite atteinte ssi l'arret est du a la limite. search2
    # s'arrete sur la limite exactement quand il en a trouve ``limit``.
    status = (
        StopStatus.LIMIT_REACHED
        if len(dlx.solutions_found) >= limit
        else StopStatus.EXHAUSTED
    )

    first = dlx.solutions_found[0]
    placements = sorted(
        (row_info[rid][0] * 9 + row_info[rid][1], row_info[rid][2] - 1)
        for rid in first
    )
    return CertificateResult(
        puzzle=puzzle,
        clues=clues_from_puzzle(puzzle),
        placements=placements,
        row_ids=list(first),
        row_info=row_info,
        status=status,
        solutions_found=len(dlx.solutions_found),
    )


class RejectionStage:
    """Etages de rejet d'un certificat, dans l'ordre d'examen.

    L'ordre compte : DOMAIN avant RAW_DUPLICATE (un doublon hors domaine doit
    etre rapporte comme hors domaine), et RAW_DUPLICATE avant toute
    conversion en ensemble -- la conversion effacerait le doublon.
    """

    DOMAIN = "domain"                # indice ou valeur hors domaine
    RAW_DUPLICATE = "raw_duplicate"  # doublon brut (paire exacte repetee)
    CELL_CONFLICT = "cell_conflict"  # deux valeurs pour une meme cellule
    COMPLETENESS = "completeness"   # placement manquant (< 81 placements)
    EXACT_COVER = "exact_cover"      # portee (ligne/colonne/bloc) violee
    CLUES = "clues"                  # indice du puzzle non respecte

    ORDER = [DOMAIN, RAW_DUPLICATE, CELL_CONFLICT, COMPLETENESS, EXACT_COVER, CLUES]


@dataclass
class ValidationVerdict:
    """Verdict de validation : accepte, ou rejete par un etage nomme."""

    accepted: bool
    stage: Optional[str] = None
    detail: str = ""


def validate_certificate(
    puzzle: str, placements: List[Tuple[int, int]]
) -> ValidationVerdict:
    """Valide un certificat par etages, sans jamais convertir avant controle.

    Le doublon brut est detecte sur la liste telle quelle (etage
    ``raw_duplicate``) : une conversion prematuree en ensemble masquerait le
    doublon -- c'est precisement le piege que cet etage existe pour fermer.

    Args:
        puzzle: chaine 81 caracteres du puzzle initial
        placements: liste (cell_index, value) pretendue complete

    Returns:
        ``ValidationVerdict`` -- accepte, ou le PREMIER etage qui rejete et
        le detail du rejet.
    """
    clues = clues_from_puzzle(puzzle)

    # Etage 1 -- domaine
    for cell, value in placements:
        if not (0 <= cell < 81) or not (0 <= value < 9):
            return ValidationVerdict(
                False, RejectionStage.DOMAIN,
                f"placement ({cell}, {value}) hors domaine ([0,80] x [0,8])",
            )

    # Etage 2 -- doublon brut (AVANT toute conversion en ensemble)
    seen = set()
    for pair in placements:
        if pair in seen:
            return ValidationVerdict(
                False, RejectionStage.RAW_DUPLICATE,
                f"paire brute repetee : {pair}",
            )
        seen.add(pair)

    # Etage 3 -- conflit de cellule (deux valeurs pour une meme cellule)
    by_cell: Dict[int, int] = {}
    for cell, value in placements:
        if cell in by_cell:
            return ValidationVerdict(
                False, RejectionStage.CELL_CONFLICT,
                f"cellule {cell} porte deux valeurs ({by_cell[cell]}, {value})",
            )
        by_cell[cell] = value

    # Etage 4 -- completude (une valeur par cellule, 81 cellules)
    if len(by_cell) != 81:
        missing = [c for c in range(81) if c not in by_cell]
        return ValidationVerdict(
            False, RejectionStage.COMPLETENESS,
            f"{len(by_cell)} placements / 81 ; manquantes : {missing[:5]}{'...' if len(missing) > 5 else ''}",
        )

    # Etage 5 -- couverture exacte par portee (lignes, colonnes, blocs)
    for r in range(9):
        scope = [by_cell[r * 9 + c] for c in range(9)]
        if len(set(scope)) != 9:
            return ValidationVerdict(
                False, RejectionStage.EXACT_COVER,
                f"ligne {r} : valeurs repetees {sorted(scope)}",
            )
    for c in range(9):
        scope = [by_cell[r * 9 + c] for r in range(9)]
        if len(set(scope)) != 9:
            return ValidationVerdict(
                False, RejectionStage.EXACT_COVER,
                f"colonne {c} : valeurs repetees {sorted(scope)}",
            )
    for br in range(3):
        for bc in range(3):
            scope = [
                by_cell[(br * 3 + r) * 9 + (bc * 3 + c)]
                for r in range(3)
                for c in range(3)
            ]
            if len(set(scope)) != 9:
                return ValidationVerdict(
                    False, RejectionStage.EXACT_COVER,
                    f"bloc ({br}, {bc}) : valeurs repetees {sorted(scope)}",
                )

    # Etage 6 -- respect des indices du puzzle
    for cell, value in clues:
        if by_cell[cell] != value:
            return ValidationVerdict(
                False, RejectionStage.CLUES,
                f"indice ({cell}, {value}) viole : la solution y place {by_cell[cell]}",
            )

    return ValidationVerdict(True)


def certificate_to_lean(
    result: CertificateResult, name: str = "exportedCertificate"
) -> str:
    """Emet le fichier donnees Lean d'un certificat resolu.

    Le fichier produit declare une definition ``Sudoku.Certificate.<name>``
    consommable par le checker calculable du lake natif. Confiance residuelle
    (a ecrire dans tout rapport utilisant cette emission) : la transcription
    Python -> litteral Lean (puzzle et placements) n'est pas prouvee ; tout
    le reste -- domaine, doublons, unicites, portees, indices -- est re-verifie
    par le checker Lean, independamment de ce module.

    Args:
        result: certificat resolu (placements attendus non vides)
        name: nom de la definition Lean emise

    Returns:
        Le contenu source du fichier ``.lean`` a deposer dans le lake.
    """
    puzzle81 = result.puzzle.replace(".", "0")
    clues_lit = ", ".join(f"({c}, {v})" for c, v in result.clues)
    placements_lit = ", ".join(f"({c}, {v})" for c, v in result.placements)
    lines = [
        "-- Fichier genere par dlx_certificates.py (issue #22375) -- NE PAS EDITER A LA MAIN.",
        "-- Certificat DLX exporte ; verifie par Sudoku.Certificate.checkCertificate.",
        f"-- Puzzle : {result.puzzle}",
        f"-- Statut de recherche : {result.status} ({result.solutions_found} solution(s) collectee(s)).",
        "-- Confiance residuelle : transcription du puzzle et des placements (voir module).",
        "",
        "import Sudoku.Certificate",
        "",
        "namespace Sudoku.Certificate",
        "",
        f"def {name} : RawCertificate (Fin 81) (Fin 9) where",
        f'  version := {result.version}',
        f'  puzzle := "{puzzle81}"',
        "  clues := [" + clues_lit + "]",
        "  placements := [" + placements_lit + "]",
        "",
        f"example : checkCertificate {name} sudokuScopes = .ok := by decide",
        "",
        "end Sudoku.Certificate",
        "",
    ]
    return "\n".join(lines)


def certificate_to_json(result: CertificateResult) -> str:
    """Serialise un certificat (format versionne, pour transport/archivage)."""
    return json.dumps(
        {
            "version": result.version,
            "conventions": result.conventions,
            "puzzle": result.puzzle,
            "clues": [list(p) for p in result.clues],
            "placements": [list(p) for p in result.placements],
            "row_ids": result.row_ids,
            "status": result.status,
            "solutions_found": result.solutions_found,
        },
        indent=2,
        sort_keys=True,
    )


# ---------------------------------------------------------------------------
# 3. Corpus 4x4 borne -- comptage compare a une enumeration independante
# ---------------------------------------------------------------------------


def solve_4x4_all(puzzle16: str, limit: int = 100) -> Tuple[List[List[Tuple[int, int]]], str]:
    """Resout un Sudoku 4x4 par couverture exacte (encodeur dedie, n = 2).

    L'encodeur generalise ``_get_columns`` au cas 4x4 : 4 * 16 = 64 colonnes,
    blocs 2x2. Il est distinct du moteur 9x9 (qui reste le canon du carnet
    Sudoku-02) ; il sert uniquement au corpus borne de comptage.

    Returns:
        (solutions, statut) -- chaque solution est une liste triee de
        (cell_index, value) avec value dans [0, 3] ; le statut distingue
        exhausted / limit_reached.
    """
    s = puzzle16.replace(".", "0").replace(" ", "")
    if len(s) != 16 or not all(ch in "01234" for ch in s):
        raise ValueError("Puzzle 4x4 invalide : 16 chiffres (0-4) attendus")

    def columns4(cell: int, value: int) -> List[int]:
        r, c, box = cell // 4, cell % 4, (cell // 8) * 2 + ((cell % 4) // 2)
        return [
            cell,             # contrainte cellule (0-15)
            16 + r * 4 + value,    # contrainte ligne-valeur (16-31)
            32 + c * 4 + value,    # contrainte colonne-valeur (32-47)
            48 + box * 4 + value,  # contrainte bloc-valeur (48-63)
        ]

    dlx = DancingLinks(64)
    row_info: Dict[int, int] = {}
    row_id = 0
    for cell in range(16):
        v0 = int(s[cell])
        values = [v0 - 1] if v0 != 0 else range(4)
        for v in values:
            dlx.add_row(row_id, columns4(cell, v))
            row_info[row_id] = cell * 4 + v
            row_id += 1

    dlx.search2(find_all=True, limit=limit)
    status = (
        StopStatus.LIMIT_REACHED if len(dlx.solutions_found) >= limit else StopStatus.EXHAUSTED
    )
    solutions = []
    for sol in dlx.solutions_found:
        placements = sorted(
            (row_info[rid] // 4, row_info[rid] % 4) for rid in sol
        )
        solutions.append(placements)
    solutions.sort()
    return solutions, status


def enumerate_4x4_independent(puzzle16: str) -> List[List[Tuple[int, int]]]:
    """Enumeration 4x4 independante de DLX (backtracking naif cellule par cellule).

    Sert de temoin croise au comptage DLX : aucune structure partagee avec
    DancingLinks. La validite de chaque solution trouvee est re-verifiee par
    la specification (unicite par portee), pas par la construction seule.
    """
    s = puzzle16.replace(".", "0").replace(" ", "")

    def ok(cell: int, value: int, assigned: List[Optional[int]]) -> bool:
        r, c = cell // 4, cell % 4
        for other in range(16):
            if other == cell or assigned[other] is None:
                continue
            orr, oc = other // 4, other % 4
            same_row, same_col = orr == r, oc == c
            same_box = (orr // 2 == r // 2) and (oc // 2 == c // 2)
            if (same_row or same_col or same_box) and assigned[other] == value:
                return False
        return True

    results: List[List[Tuple[int, int]]] = []

    def backtrack(cell: int, assigned: List[Optional[int]]):
        if cell == 16:
            results.append(sorted((i, v) for i, v in enumerate(assigned) if v is not None))
            return
        v0 = int(s[cell])
        candidates = [v0 - 1] if v0 != 0 else range(4)
        for v in candidates:
            if ok(cell, v, assigned):
                assigned[cell] = v
                backtrack(cell + 1, assigned)
                assigned[cell] = None

    backtrack(0, [None] * 16)
    results.sort()
    return results
