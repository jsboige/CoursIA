"""Generation certifiee d'un corpus Sudoku equilibre par la mesure.

Organe du volet 1 de l'EPIC Sudoku (#26242, issue #26426) : generer des
grilles dont l'unicite est **prouvee par denombrement certifie** (le moteur
DLX de ``dlx_certificates.py``, invoque tel quel), puis les repartir en
paliers de difficulte **mesures** par les instruments de la serie
(``corpus.search_effort``, ``corpus.propagation_only``) -- jamais supposes
par un nombre de cases vides.

Composition d'organes existants (regle organ-first) :

- ``generation.generate_complete_grid`` (``scripts/sudoku/core/generation.py``)
  produit la solution pleine aleatoire ;
- ``dlx_certificates.solve_certificate(puzzle, limit=2)`` fournit le verdict
  d'unicite : ``solutions_found == 1`` et ``status == "exhausted"`` prouvent
  l'unicite ; ``solutions_found >= 2`` ou ``status == "limit_reached"``
  demontrent la sous-determination ; ``solutions_found == 0`` l'absence de
  solution ;
- ``corpus.search_effort`` / ``corpus.propagation_only`` / ``corpus.audit_corpus``
  (``scripts/sudoku/core/corpus.py``) mesurent la difficulte et produisent le
  tableau de distribution comparable aux corpus herites.

Trois strategies de creusage produisent les trois paliers :

- ``facile``  : on creuse tant que la grille reste resoluble par propagation
  seule (0 decision de backtracking, garanti par construction puis verifie) ;
- ``moyen``   : on creuse sous contrainte d'unicite jusqu'a un nombre d'indices
  cible (28 par defaut) ;
- ``difficile`` : creusage **adversarial** -- a chaque etape, le retrait
  (parmi 8 candidats aleatoires) qui maximise l'effort de recherche mesure est
  applique, sous contrainte d'unicite certifiee.

Chaque grille emise est ensuite acceptee ou rejetee selon la bande de
difficulté **mesurée** de son palier (tirage-rejet) : c'est la mesure qui
equilibre le corpus, jamais un compte de cases vides.

Notation de sortie : un fichier par palier, une grille de 81 caracteres par
ligne, chiffre ``0`` pour une case vide (notation homogene, documentee ici --
les corpus herites melangent ``0`` et ``.``).
"""

from __future__ import annotations

import argparse
import random
import sys
from pathlib import Path
from typing import Optional

import numpy as np

# Resolution des organes par chemin de fichier, comme le font Sudoku-20 et les
# tests de la serie (la chaine de paquet core/__init__.py charge torch).
_HERE = Path(__file__).resolve()
_SERIES_DIR = _HERE.parent.parent
_REPO_CANDIDATES = [*_SERIES_DIR.parents]
_REPO_ROOT = next(
    p for p in _REPO_CANDIDATES if (p / "scripts" / "sudoku" / "core" / "corpus.py").exists()
)
sys.path.insert(0, str(_REPO_ROOT / "scripts" / "sudoku" / "core"))
sys.path.insert(0, str(_SERIES_DIR))

import corpus  # noqa: E402  (organe: scripts/sudoku/core/corpus.py)
import dlx_certificates  # noqa: E402  (organe: Sudoku/dlx_certificates.py)
from generation import generate_complete_grid  # noqa: E402  (organe: core/generation.py)

TIERS = ("facile", "moyen", "difficile")
DEFAULT_PER_TIER = 10
DEFAULT_MEDIUM_CLUES = 28

# Bandes de difficulté calibrees sur les corpus HERITES (Sudoku-20 : Easy51
# mediane 0 / pire 7 ; hardest mediane 8 / pire 21 ; top95 mediane 39 / pire
# 446) ET sur ce qu'un creusage certifie atteint reellement (adversarial :
# queue 12-22, comparable a `hardest` ; les sommets de top95 sont des corpus
# curates, pas produits par creusage). Le palier difficile genere egale la
# bande `hardest`, il ne pretend pas a celle de top95.
MOYEN_BAND = (1, 9)      # decisions de backtracking, bornes incluses
DIFFICILE_MIN = 10       # decisions a partir de la bande difficile
ADVERSARIAL_CANDIDATES = 8  # retraits comparés par étape de creusage adversarial


def puzzle_to_string(grid) -> str:
    """Rend la grille (81 entiers, 0 = vide) en chaine de 81 caracteres."""
    return "".join(str(int(v)) for v in grid)


def uniqueness_verdict(puzzle_line: str) -> tuple[str, int]:
    """Verdict d'unicite par denombrement certifie (DLX, plafond 2).

    Rend ``(statut, solutions_trouvees)``. Le verdict ``unique`` exige
    ``solutions_found == 1`` **et** ``status == "exhausted"`` : un arret sur
    limite ne prouve jamais l'unicite.
    """
    result = dlx_certificates.solve_certificate(puzzle_line, find_all=True, limit=2)
    if result is None:  # pragma: no cover - solve_certificate ne rend jamais None
        return ("sans_solution", 0)
    return (result.status, result.solutions_found)


def is_unique(puzzle_line: str) -> bool:
    """Vrai ssi le denombrement certifie prouve l'unicite (1 solution, epuise)."""
    status, found = uniqueness_verdict(puzzle_line)
    return status == "exhausted" and found == 1


def certify(puzzle_line: str) -> dict:
    """Certification complete d'une grille emise : unicite + difficulte mesuree."""
    grid = corpus.parse_puzzle(puzzle_line)
    status, found = uniqueness_verdict(puzzle_line)
    decisions = corpus.search_effort(grid)
    return {
        "puzzle": puzzle_line,
        "status": status,
        "solutions_found": found,
        "unique": status == "exhausted" and found == 1,
        "clues": int((grid != 0).sum()),
        "decisions": decisions,
        "propagation_only": corpus.propagation_only(grid),
    }


def dig_facile(solution: list[int], rng: random.Random) -> list[int]:
    """Creuse tant que la grille reste resoluble par propagation seule.

    La grille emise est unique par construction : la propagation qui la
    complete est une preuve constructive d'unicite (certifiee ensuite par DLX).
    """
    puzzle = list(solution)
    for pos in rng.sample(range(81), 81):
        saved = puzzle[pos]
        if saved == 0:
            continue
        puzzle[pos] = 0
        if not corpus.propagation_only(puzzle):
            puzzle[pos] = saved  # frontiere de propagation atteinte : on annule
    return puzzle


def dig_under_uniqueness(
    solution: list[int], rng: random.Random, target_clues: Optional[int] = None
) -> list[int]:
    """Creuse sous contrainte d'unicite certifiee, jusqu'a la cible ou au maximum.

    Args:
        solution: grille pleine (81 entiers).
        rng: generateur aleatoire pilotant l'ordre de creusage.
        target_clues: nombre d'indices a atteindre ; ``None`` = creusage
            maximal (toutes les positions sont tentees).
    """
    puzzle = list(solution)
    clues = 81
    for pos in rng.sample(range(81), 81):
        if target_clues is not None and clues <= target_clues:
            break
        saved = puzzle[pos]
        if saved == 0:
            continue
        puzzle[pos] = 0
        if not is_unique(puzzle_to_string(puzzle)):
            puzzle[pos] = saved  # retrait cassant l'unicite : annule
        else:
            clues -= 1
    return puzzle


def dig_adversarial(solution: list[int], rng: random.Random) -> list[int]:
    """Creusage adversarial : chaque retrait maximise l'effort de recherche mesure.

    A chaque etape, ``ADVERSARIAL_CANDIDATES`` retraits valides (conservant
    l'unicite certifiee) sont compares par ``corpus.search_effort`` ; le
    retrait qui rend la grille la plus difficile est applique. Le creusage
    s'arrete quand aucun retrait ne conserve l'unicite.
    """
    puzzle = list(solution)
    while True:
        filled = [pos for pos in range(81) if puzzle[pos] != 0]
        if not filled:
            break
        best = None  # (effort, pos)
        for pos in rng.sample(filled, min(len(filled), ADVERSARIAL_CANDIDATES)):
            saved = puzzle[pos]
            puzzle[pos] = 0
            if is_unique(puzzle_to_string(puzzle)):
                effort = corpus.search_effort(puzzle)
                if best is None or effort > best[0]:
                    best = (effort, pos)
            puzzle[pos] = saved
        if best is None:
            break  # retrait maximal atteint : plus aucun retrait ne preserve l'unicite
        puzzle[best[1]] = 0
    return puzzle


def tier_accepts(tier: str, record: dict) -> bool:
    """Palier accepte si la difficulte MESUREE tombe dans sa bande calibree."""
    if not record["unique"]:
        return False
    if tier == "facile":
        return record["decisions"] == 0
    if tier == "moyen":
        return MOYEN_BAND[0] <= record["decisions"] <= MOYEN_BAND[1]
    return record["decisions"] >= DIFFICILE_MIN


def generate_tier(
    tier: str, per_tier: int, seed: int, medium_clues: int
) -> list[dict]:
    """Genere ``per_tier`` grilles certifiees pour un palier, par tirage-rejet.

    Chaque tentative genere une solution pleine aleatoire, la creuse selon la
    strategie du palier, certifie l'unicite par denombrement DLX, mesure la
    difficulte, puis accepte ou rejette selon la bande du palier. Le rejet par
    la mesure -- et non un compte de cases vides -- est ce qui equilibre le
    corpus.
    """
    out: list[dict] = []
    attempts = 0
    max_attempts = max(200, per_tier * 40)
    while len(out) < per_tier:
        attempts += 1
        if attempts > max_attempts:
            raise RuntimeError(
                f"palier {tier} : {per_tier} grilles non atteintes en "
                f"{max_attempts} tentatives (bande trop stricte ?)"
            )
        rng = random.Random(seed * 100_003 + attempts)
        full_flat = [int(v) for v in generate_complete_grid(
            np_random_state(attempts, seed)).flatten()]
        if tier == "facile":
            puzzle = dig_facile(full_flat, rng)
        elif tier == "moyen":
            puzzle = dig_under_uniqueness(full_flat, rng, target_clues=medium_clues)
        elif tier == "difficile":
            puzzle = dig_adversarial(full_flat, rng)
        else:  # pragma: no cover - TIERS est une enumeration fermee
            raise ValueError(f"palier inconnu : {tier}")
        record = certify(puzzle_to_string(puzzle))
        if tier_accepts(tier, record):
            out.append(record)
    return out


def np_random_state(attempt: int, seed: int) -> np.random.RandomState:
    """RandomState numpy deterministe par (seed, tentative)."""
    return np.random.RandomState(seed * 1_000_003 + attempt)


def tier_summary(name: str, records: list[dict]) -> str:
    """Ligne de resume au format de Sudoku-20 (comparaison directe)."""
    decisions = sorted(r["decisions"] for r in records)
    clues = sorted(r["clues"] for r in records)
    return (
        f"{name:<28} propagation seule : {decisions.count(0):>2}/{len(records):<2}"
        f" | mediane : {decisions[len(decisions) // 2]:>4} decisions"
        f" | pire : {decisions[-1]:>5}"
        f" | indices : {clues[0]} a {clues[-1]}"
    )


def audit_irredundancy(out_dir: Path, per_tier: int | None = None) -> list[dict]:
    """Cardinal d'irredundance du corpus livre, par grille (organe Sudoku-20).

    Pour chaque grille, ``corpus.minimal_clue_set`` retire gloutonnement les
    indices dont le retrait preserve l'unicite de la solution : le cardinal
    documente est ``N indices -> K conserves (R redondants)``, au format de
    Sudoku-20. Irredundant (a l'ordre de suppression pres) n'est pas minimal
    en cardinal -- la distinction est portee par l'organe lui-meme.

    Rend la liste des enregistrements ``(tier, clues, kept, retired)`` pour
    les tests ; l'impression est cote appelant.
    """
    rows: list[dict] = []
    for tier in TIERS:
        path = out_dir / f"Sudoku_gen_{tier}.txt"
        lines = [l for l in path.read_text(encoding="utf-8").splitlines() if l.strip()]
        if per_tier is not None:
            lines = lines[:per_tier]
        kept_list: list[int] = []
        for idx, line in enumerate(lines, start=1):
            grid = corpus.parse_puzzle(line)
            clues = int((grid != 0).sum())
            _, retired = corpus.minimal_clue_set(grid)
            kept = clues - len(retired)
            kept_list.append(kept)
            rows.append(
                {"tier": tier, "no": idx, "clues": clues, "kept": kept, "retired": len(retired)}
            )
            print(f"  {tier} no {idx:>2} : {clues} indices -> {kept} conserves ({len(retired)} redondants)")
        kept_sorted = sorted(kept_list)
        print(
            f"{path.name:<28} irreductibilite : mediane {kept_sorted[len(kept_sorted) // 2]:>2} conserves"
            f" | min : {kept_sorted[0]:>2} | max : {kept_sorted[-1]:>2}"
        )
    return rows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generation certifiee d'un corpus Sudoku equilibre."
    )
    parser.add_argument("--per-tier", type=int, default=DEFAULT_PER_TIER)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--medium-clues", type=int, default=DEFAULT_MEDIUM_CLUES)
    parser.add_argument("--out-dir", type=Path, default=_SERIES_DIR / "Puzzles")
    parser.add_argument(
        "--audit",
        action="store_true",
        help="ne generer rien : documenter le cardinal d'irreductibilite du corpus existant",
    )
    args = parser.parse_args(argv)

    args.out_dir.mkdir(parents=True, exist_ok=True)

    if args.audit:
        audit_irredundancy(args.out_dir)
        return 0
    all_unique = True
    for tier in TIERS:
        records = generate_tier(tier, args.per_tier, args.seed, args.medium_clues)
        out_path = args.out_dir / f"Sudoku_gen_{tier}.txt"
        out_path.write_text(
            "\n".join(r["puzzle"] for r in records) + "\n", encoding="utf-8"
        )
        print(tier_summary(f"Sudoku_gen_{tier}.txt", records))
        for r in records:
            if not r["unique"]:
                all_unique = False
                print(f"  !! grille non unique emise : {r['puzzle']}")
    print("certification : " + ("UNIQUE (exhausted, 1 solution) sur toutes les grilles emises"
                                if all_unique else "ECHEC"))
    audit_irredundancy(args.out_dir)
    return 0 if all_unique else 1


if __name__ == "__main__":
    raise SystemExit(main())
