#!/usr/bin/env python3
"""Audit du corpus de puzzles de la serie Sudoku.

Le corpus `MyIA.AI.Notebooks/Sudoku/Puzzles/` (trois fichiers, 157 grilles
au total) est **consomme** par plusieurs carnets de la serie, mais rien dans
le depot ne le **certifie** : ni l'unicite des solutions, ni la hierarchie de
difficulte que les noms de fichiers (`Easy51`, `hardest`, `top95`) affirment.

Ce module rend ces trois proprietes mesurables :

- `count_solutions` -- nombre exact de solutions, plafonne a un seuil
  (2 = « au moins deux »), etabli par **denombrement exhaustif** ;
- `search_effort` -- nombre de decisions de backtracking pour trouver la
  premiere solution : 0 signifie que la **propagation seule** (candidats nus
  et candidats caches) suffit, ce qui est la lecture « solveur humain » ;
- `minimal_clue_set` -- sous-ensemble d'indices qui determine **la meme
  solution unique** ; la suppression est testee indice par indice, dans
  l'ordre, donc le sous-ensemble rendu est **irredondant** a l'etape de
  suppression consideree, et pas necessairement *minimal* en cardinal.

**Organe, pas second solveur.** La propagation et la recherche MRV viennent
de `solvers.py`, l'organe canonique de la serie (`solve_sudoku`,
`is_valid_puzzle`, et la primitive de propagation `_fill`) : ce module
denombre et mesure ce que l'organe resout, il n'ecrit pas de moteur de
resolution concurrent. Le seul code ajoute est un *comptage* de solutions et
un *comptage de decisions*, qui reutilisent la propagation de l'organe.

Ddependencies : `numpy` seul. Aucun import de `torch` : le module est
importable par chemin de fichier (`sys.path` sur `core/`), comme
`scripts/sudoku/tests/test_core_solvers.py` le fait deja pour rester
hermetique.

Point d'entree :

    python scripts/sudoku/core/corpus.py            # tableau de synthese
    python scripts/sudoku/core/corpus.py --json     # sortie machine
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Iterable, Sequence

import numpy as np

try:  # import comme membre du paquet `scripts.sudoku.core`
    from .solvers import _DIGITS, _fill, is_valid_puzzle, solve_sudoku
except ImportError:  # import par chemin de fichier (tests) : la chaine
    # `core/__init__.py` force-importe torch, on la contourne comme le fait
    # deja `scripts/sudoku/tests/test_core_solvers.py`.
    from solvers import _DIGITS, _fill, is_valid_puzzle, solve_sudoku  # type: ignore[no-redef]

#: Repertoire du corpus, derive de l'emplacement du module (racine du depot).
PUZZLE_DIR: Path = (
    Path(__file__).resolve().parents[3] / "MyIA.AI.Notebooks" / "Sudoku" / "Puzzles"
)

#: Les trois corpus de la serie, dans l'ordre de difficulte annonce.
CORPUS_FILES: tuple[str, ...] = (
    "Sudoku_Easy51.txt",
    "Sudoku_hardest.txt",
    "Sudoku_top95.txt",
)

_EMPTY_CHARS = "0."


# ---------------------------------------------------------------------------
# Lecture du corpus
# ---------------------------------------------------------------------------

def parse_puzzle(line: str) -> np.ndarray:
    """Parse une grille de 81 caracteres en tableau de 81 entiers (0 = vide).

    Deux notations sont acceptees, celles des deux corpus de la serie :
    `Sudoku_Easy51.txt` ecrit les cases vides `0`, les deux autres ecrivent
    `.`.

    Args:
        line: une ligne de 81 caracteres, espaces de bord toleres.

    Returns:
        Un tableau numpy de 81 entiers dans {0, ..., 9}.

    Raises:
        ValueError: si la ligne ne fait pas 81 caracteres, ou porte un
            caractere qui n'est ni un chiffre ni une case vide.
    """
    text = line.strip()
    if len(text) != 81:
        raise ValueError(
            f"une grille fait 81 caracteres, elle en fait {len(text)} : {text[:40]!r}"
        )
    cells = np.zeros(81, dtype=np.int64)
    for index, char in enumerate(text):
        if char in _EMPTY_CHARS:
            continue
        if char not in "123456789":
            raise ValueError(
                f"caractere invalide {char!r} a la position {index} (attendu 0, . ou 1-9)"
            )
        cells[index] = int(char)
    return cells


def load_corpus(path: Path | str) -> list[np.ndarray]:
    """Charge un fichier de puzzles : une grille par ligne non vide.

    Args:
        path: chemin du fichier de corpus.

    Returns:
        La liste des grilles, dans l'ordre du fichier.

    Raises:
        ValueError: si une ligne est mal formee ; le message nomme le
            fichier et le numero de ligne.
    """
    source = Path(path)
    puzzles: list[np.ndarray] = []
    for lineno, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            puzzles.append(parse_puzzle(line))
        except ValueError as exc:
            raise ValueError(f"{source.name}:{lineno} : {exc}") from exc
    return puzzles


# ---------------------------------------------------------------------------
# Denombrement et mesure (propagation de l'organe `solvers.py`)
# ---------------------------------------------------------------------------

def _propagated(puzzle: Sequence[int] | np.ndarray) -> dict[int, str] | None:
    """Grille de candidats apres propagation des indices, ou None si incoherent.

    Reutilise la primitive de propagation de l'organe (`_fill`), qui enchaine
    candidats nus et candidats caches.

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.

    Returns:
        Un dict case -> candidats restants, ou None si la propagation detecte
        une contradiction.
    """
    grid: dict[int, str] = {i: _DIGITS for i in range(81)}
    for index in range(81):
        if puzzle[index] != 0:
            grid = _fill(grid, index, str(puzzle[index]))
            if grid is None:
                return None
    return grid


def _search(grid: dict[int, str] | None, limit: int) -> tuple[int, int]:
    """Recherche MRV : compte les solutions (plafonnees) et les decisions.

    Args:
        grid: grille de candidats deja propagee, ou None.
        limit: nombre de solutions a compter au plus.

    Returns:
        Le couple `(solutions, decisions)` ou `solutions` est plafonne a
        `limit` et `decisions` compte les branches `(case, chiffre)` essayees.
    """
    if grid is None:
        return 0, 0
    min_len, best = 10, -1
    for cell in range(81):
        size = len(grid[cell])
        if 1 < size < min_len:
            min_len, best = size, cell
    if best == -1:
        return 1, 0
    solutions, decisions = 0, 0
    for digit in grid[best]:
        found, spent = _search(_fill(grid.copy(), best, digit), limit - solutions)
        solutions += found
        decisions += 1 + spent
        if solutions >= limit:
            break
    return solutions, decisions


def count_solutions(puzzle: Sequence[int] | np.ndarray, limit: int = 2) -> int:
    """Nombre de solutions d'une grille, plafonne a `limit`.

    Le denombrement est **exhaustif** : la recherche explore toutes les
    branches jusqu'a avoir compte `limit` solutions. Avec `limit=2`, le
    resultat vaut 2 des que deux solutions distinctes existent -- c'est ce
    qui distingue « une solution unique » de « une solution trouvee ».

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.
        limit: seuil de saturation du comptage (2 par defaut).

    Returns:
        Le nombre de solutions, plafonne a `limit`.
    """
    if limit < 1:
        raise ValueError("le seuil de comptage doit valoir au moins 1")
    solutions, _ = _search(_propagated(puzzle), limit)
    return solutions


def search_effort(puzzle: Sequence[int] | np.ndarray) -> int:
    """Nombre de decisions de backtracking pour trouver la premiere solution.

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.

    Returns:
        Le nombre de branches `(case, chiffre)` essayees. **0** signifie que
        la propagation seule a suffit : aucun backtracking n'a ete necessaire.
        -1 signifie que la grille n'a pas de solution.
    """
    grid = _propagated(puzzle)
    if grid is None:
        return -1
    _, decisions = _search(grid, 1)
    return decisions


def propagation_only(puzzle: Sequence[int] | np.ndarray) -> bool:
    """Vrai si la grille se resout par propagation seule, sans backtracking.

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.

    Returns:
        True si la propagation des indices suffit a determiner toutes les
        cases, False si un backtracking est necessaire.
    """
    return search_effort(puzzle) == 0


def minimal_clue_set(
    puzzle: Sequence[int] | np.ndarray,
) -> tuple[np.ndarray, list[int]]:
    """Reduit les indices a un sous-ensemble qui determine la meme solution.

    La suppression est testee indice par indice, dans l'ordre : un indice
    retire est conserve comme retire si la grille reduite a **exactement une**
    solution, identique a celle de la grille de depart. Le resultat est donc
    un sous-ensemble **irredondant** a l'etape de suppression consideree ; il
    n'est pas necessairement *minimal* en cardinal (le minimum exigerait une
    recherche exhaustive sur les sous-ensembles).

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.

    Returns:
        Le couple `(grille reduite, indices retires)`.

    Raises:
        ValueError: si la grille n'a pas de solution unique.
    """
    grid = np.asarray(puzzle, dtype=np.int64).copy()
    solution = solve_sudoku(grid)
    if solution is None:
        raise ValueError("grille sans solution : aucun jeu d'indices minimal n'est defini")
    if count_solutions(grid, 2) != 1:
        raise ValueError("grille a plusieurs solutions : le jeu d'indices n'est pas determinant")

    retired: list[int] = []
    for index in range(81):
        if grid[index] == 0:
            continue
        kept = int(grid[index])
        grid[index] = 0
        # Le critere de retention est l'**unicite**, pas « une solution trouvee » :
        # `solve_sudoku` rend la premiere solution qu'il trouve, donc une grille
        # reduite a plusieurs solutions pourrait passer le test a tort. On
        # denombre donc les solutions de la grille reduite, et on exige
        # qu'il n'y en ait qu'une, egale a celle de la grille de depart.
        if count_solutions(grid, 2) == 1:
            candidate = solve_sudoku(grid)
            if candidate is not None and np.array_equal(candidate, solution):
                retired.append(index)
                continue
        grid[index] = kept
    return grid, retired


# ---------------------------------------------------------------------------
# Audit
# ---------------------------------------------------------------------------

def audit_puzzle(puzzle: Sequence[int] | np.ndarray) -> dict[str, Any]:
    """Mesure les proprietes d'une grille.

    Args:
        puzzle: tableau de 81 entiers, 0 pour une case vide.

    Returns:
        Un dictionnaire de mesures : nombre d'indices, coherence, nombre de
        solutions (plafonne a 2), decisions de backtracking, et le drapeau
        « resolu par propagation seule ».
    """
    grid = np.asarray(puzzle, dtype=np.int64)
    decisions = search_effort(grid)
    return {
        "clues": int((grid != 0).sum()),
        "valid": bool(is_valid_puzzle(grid)),
        "solutions": count_solutions(grid, 2),
        "decisions": decisions,
        "propagation_only": decisions == 0,
    }


def audit_corpus(path: Path | str, reduce_clues: bool = False) -> dict[str, Any]:
    """Mesure un corpus entier.

    Args:
        path: chemin du fichier de corpus.
        reduce_clues: si vrai, mesure aussi le **jeu d'indices irredondant**
            de chaque grille (operation plus couteuse : elle denombre les
            solutions de chaque grille reduite candidate).

    Returns:
        Un dictionnaire : nom du fichier, nombre de puzzles, indices des
        puzzles invalides ou non uniques, part resolue par propagation seule,
        pire effort de recherche, et les mesures detaillees de chaque puzzle.
        Quand `reduce_clues` est vrai, s'y ajoutent le nombre d'indices
        redondants total et le nombre de grilles deja irredundantes.
    """
    source = Path(path)
    puzzles = load_corpus(source)
    records = [audit_puzzle(puzzle) for puzzle in puzzles]
    clues = [record["clues"] for record in records]
    audit: dict[str, Any] = {
        "file": source.name,
        "count": len(records),
        "invalid": [i + 1 for i, r in enumerate(records) if not r["valid"]],
        "not_unique": [i + 1 for i, r in enumerate(records) if r["solutions"] != 1],
        "unsolved": [i + 1 for i, r in enumerate(records) if r["solutions"] == 0],
        "propagation_only": sum(1 for r in records if r["propagation_only"]),
        "max_decisions": max((r["decisions"] for r in records), default=0),
        "min_clues": min(clues, default=0),
        "max_clues": max(clues, default=0),
        "records": records,
    }
    if reduce_clues:
        redundant = 0
        irredundant = 0
        for puzzle in puzzles:
            _, retired = minimal_clue_set(puzzle)
            redundant += len(retired)
            if not retired:
                irredundant += 1
        audit["redundant_clues"] = redundant
        audit["irredundant_puzzles"] = irredundant
    return audit


def audit_all(
    directory: Path | str = PUZZLE_DIR, reduce_clues: bool = False
) -> dict[str, dict[str, Any]]:
    """Mesure les trois corpus de la serie.

    Args:
        directory: repertoire contenant les fichiers de corpus.
        reduce_clues: propager l'option a chaque corpus.

    Returns:
        Un dictionnaire `{nom de fichier: mesures}`.
    """
    root = Path(directory)
    return {
        name: audit_corpus(root / name, reduce_clues=reduce_clues)
        for name in CORPUS_FILES
    }


def format_summary(audits: dict[str, dict[str, Any]]) -> str:
    """Met en forme le tableau de synthese d'un audit.

    Args:
        audits: sortie de `audit_all`.

    Returns:
        Un tableau texte, une ligne par corpus.
    """
    header = (
        f"{'corpus':<22}{'n':>5}{'invalides':>11}{'non uniques':>13}"
        f"{'propagation seule':>20}{'pire effort':>13}"
    )
    lines = [header, "-" * len(header)]
    for name, audit in audits.items():
        lines.append(
            f"{audit['file']:<22}{audit['count']:>5}{len(audit['invalid']):>11}"
            f"{len(audit['not_unique']):>13}{audit['propagation_only']:>13}"
            f" ({100 * audit['propagation_only'] // max(audit['count'], 1)} %)"
            f"{audit['max_decisions']:>13}"
        )
    if any("redundant_clues" in audit for audit in audits.values()):
        lines.append("")
        lines.append(
            f"{'corpus':<22}{'indices redondants':>20}{'grilles irredondantes':>26}"
        )
        for name, audit in audits.items():
            if "redundant_clues" not in audit:
                continue
            lines.append(
                f"{audit['file']:<22}{audit['redundant_clues']:>20}"
                f"{audit['irredundant_puzzles']:>20} / {audit['count']}"
            )
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    """Point d'entree : audite les trois corpus et affiche la synthese.

    Args:
        argv: arguments de la ligne de commande (`--json` pour une sortie
            machine, `--reduce` pour mesurer aussi les indices redondants).

    Returns:
        0 si l'audit se termine, 1 si un corpus est invalide ou non unique.
    """
    args = list(sys.argv[1:] if argv is None else argv)
    audits = audit_all(reduce_clues="--reduce" in args)
    if "--json" in args:
        printable = {
            name: {key: value for key, value in audit.items() if key != "records"}
            for name, audit in audits.items()
        }
        print(json.dumps(printable, indent=2, ensure_ascii=False))
    else:
        print(format_summary(audits))
    broken = any(audit["invalid"] or audit["not_unique"] for audit in audits.values())
    return 1 if broken else 0


if __name__ == "__main__":  # pragma: no cover - point d'entree CLI
    import sys

    raise SystemExit(main())
