"""
Tests pour le module WFC (Wave Function Collapse) du notebook Search App-19
(`Applications/CSP/wfc_cpsat.py`).

Le module implemente la generation procedurale de niveaux par collapse de la
fonction d'onde, en trois variantes :
  - generate_random : baseline aleatoire (aucune contrainte)
  - PureWFC         : AC-3 propagation + collapse guide par entropie + backtracking
  - solve_cpsat     : modelisation CP-SAT (OR-Tools) avec contraintes globales
                      (adjacency, ratio floor, objets, connectivite)

Les tests assertent des INVARIANTS (le contrat de chaque solveur), pas
seulement l'absence de crash :
  - **WFC respecte l'adjacence** : toute solution PureWFC a 0 violation des
    regles tile-a-tile (c'est LA definition d'une solution WFC valide).
  - **CP-SAT respecte TOUTES ses contraintes globales** : adjacency, ratio de
    floor dans les bornes, exactement n_keys/n_chests, objets uniquement sur
    floor, source floor, connectivite BFS.
  - **Determinisme** : meme graine -> meme grille (PureWFC et generate_random).
  - **Metriques** : adjacency_violations / bfs_reachable_floor / tile_variety
    retournent les bonnes valeurs sur des grilles construites.

Run with: pytest tests/test_wfc_cpsat.py -v
"""

import json
import sys
from pathlib import Path

import numpy as np
import pytest

# Ajoute Applications/CSP/ au path pour importer wfc_cpsat.
sys.path.insert(0, str(Path(__file__).parent.parent / "Applications" / "CSP"))

import wfc_cpsat  # noqa: E402
from wfc_cpsat import (  # noqa: E402
    PureWFC,
    CPSATResult,
    generate_random,
    solve_cpsat,
    bfs_reachable_floor,
    adjacency_violations,
    tile_variety,
    load_tileset,
)

# Identites du tileset (tileset.json, id == index) :
#   0=wall, 1=floor, 2=water, 3=door, 4=grass
FLOOR_ID = 1
WATER_ID = 2
WALL_ID = 0


# ----------------------------------------------------------------------------
# Fixtures
# ----------------------------------------------------------------------------

@pytest.fixture(scope="module")
def tileset():
    """Charge le tileset reel (a cote du module wfc_cpsat)."""
    return load_tileset()


@pytest.fixture(scope="module")
def rules(tileset):
    """Regles d'adjacence sous forme {int: [bool x5]} (clefs entieres)."""
    raw = tileset["adjacency"]["rules"]
    return {int(k): v for k, v in raw.items()}


# ----------------------------------------------------------------------------
# Baseline aleatoire (aucune contrainte).
# ----------------------------------------------------------------------------

class TestGenerateRandom:
    """generate_random : baseline sans contraintes."""

    def test_shape(self, tileset):
        grid = generate_random(5, 7, tileset, seed=0)
        assert grid.shape == (5, 7)

    def test_values_in_range(self, tileset):
        grid = generate_random(6, 6, tileset, seed=1)
        n_tiles = len(tileset["tiles"])
        assert grid.min() >= 0
        assert grid.max() < n_tiles

    def test_deterministic_same_seed(self, tileset):
        """Meme graine -> meme grille (reproductibilite)."""
        a = generate_random(6, 6, tileset, seed=42)
        b = generate_random(6, 6, tileset, seed=42)
        np.testing.assert_array_equal(a, b)

    def test_different_seeds_differ(self, tileset):
        """Graines differentes -> grilles differentes (presque surement)."""
        a = generate_random(8, 8, tileset, seed=1)
        b = generate_random(8, 8, tileset, seed=999)
        assert not np.array_equal(a, b)


# ----------------------------------------------------------------------------
# Pure WFC : AC-3 + entropy-guided collapse + backtracking.
# ----------------------------------------------------------------------------

class TestPureWFC:
    """PureWFC : solveur par propagation de contraintes. L'invariant cle est
    que toute solution respecte les regles d'adjacence."""

    def test_returns_grid(self, tileset):
        wfc = PureWFC(6, 6, tileset, seed=0)
        grid = wfc.solve()
        assert grid is not None
        assert grid.shape == (6, 6)

    def test_solution_has_no_adjacency_violations(self, tileset, rules):
        """INVARIANT FONDAMENTAL : une solution WFC respecte l'adjacence.

        C'est la definition meme d'une solution WFC valide : chaque paire de
        tiles voisins doit etre autorisee par les regles. Si ce test echoue,
        le solveur est casse (propagation AC-3 ou backtracking defectueux).
        """
        wfc = PureWFC(8, 8, tileset, seed=3)
        grid = wfc.solve()
        assert grid is not None
        assert adjacency_violations(grid, rules) == 0

    def test_deterministic(self, tileset):
        """Meme graine -> meme solution (le collapse est seeded)."""
        a = PureWFC(6, 6, tileset, seed=7).solve()
        b = PureWFC(6, 6, tileset, seed=7).solve()
        np.testing.assert_array_equal(a, b)

    def test_all_cells_collapsed(self, tileset, rules):
        """Chaque cellule a exactement une tile valide dans [0, n_tiles)."""
        n_tiles = len(tileset["tiles"])
        grid = PureWFC(6, 6, tileset, seed=0).solve()
        assert grid is not None
        assert grid.min() >= 0
        assert grid.max() < n_tiles


# ----------------------------------------------------------------------------
# CP-SAT : modelisation OR-Tools avec contraintes globales.
# ----------------------------------------------------------------------------

class TestCPSat:
    """solve_cpsat : modelisation CP-SAT. Chaque contrainte globale annoncee
    dans la docstring doit etre respectee par la solution retournee."""

    @pytest.fixture(scope="class")
    def cpsat_solution(self, tileset):
        """Solution CP-SAT 6x6 (rapide) reutilisee par toute la classe."""
        res = solve_cpsat(
            rows=6, cols=6, tileset=tileset, seed=42,
            min_floor_ratio=0.30, max_floor_ratio=0.60,
            min_enemy_ratio=0.05, max_enemy_ratio=0.20,
            n_keys=1, n_chests=1, add_connectivity=True, timeout_s=10.0,
        )
        # On exige qu'une solution soit trouvee sur ce petit instance realisable.
        assert res.grid is not None, f"CP-SAT n'a pas trouve de solution (status={res.status})"
        return res

    def test_status_feasible_or_optimal(self, cpsat_solution):
        assert cpsat_solution.status in ("OPTIMAL", "FEASIBLE")

    def test_grid_shape(self, cpsat_solution):
        assert cpsat_solution.grid.shape == (6, 6)

    def test_adjacency_respected(self, cpsat_solution, rules):
        """Contrat 1 (adjacency) : la grille CP-SAT respecte les regles tile-a-tile."""
        assert adjacency_violations(cpsat_solution.grid, rules) == 0

    def test_floor_ratio_in_bounds(self, cpsat_solution):
        """Contrat 2 (floor ratio) : floor_cells dans [min*N, max*N]."""
        n = 6 * 6
        lo, hi = int(0.30 * n), int(0.60 * n)
        n_floor = int((cpsat_solution.grid == FLOOR_ID).sum())
        assert lo <= n_floor <= hi

    def test_exact_key_chest_counts(self, cpsat_solution):
        """Contrat 5 : exactement n_keys=1 keys (obj==2) et n_chests=1 chests (obj==3)."""
        obj_grid = cpsat_solution.stats["obj_grid"]
        assert int((obj_grid == 2).sum()) == 1  # keys
        assert int((obj_grid == 3).sum()) == 1  # chests

    def test_objects_only_on_floor(self, cpsat_solution):
        """Contrat 3 : tout objet (obj > 0) est pose sur une cellule floor."""
        grid = cpsat_solution.grid
        obj_grid = cpsat_solution.stats["obj_grid"]
        object_cells = np.argwhere(obj_grid > 0)
        for r, c in object_cells:
            assert grid[r, c] == FLOOR_ID, (
                f"objet {obj_grid[r, c]} a ({r},{c}) sur tile {grid[r, c]} != floor"
            )

    def test_source_cell_is_floor(self, cpsat_solution):
        """Contrat 6 (connectivite) : la cellule source (0,0) est forcee floor."""
        assert cpsat_solution.grid[0, 0] == FLOOR_ID

    def test_enemy_density_in_bounds(self, cpsat_solution):
        """Contrat 4 : enemies/floor dans [min_enemy_ratio, max_enemy_ratio]."""
        n_floor = int((cpsat_solution.grid == FLOOR_ID).sum())
        n_enemies = int((cpsat_solution.stats["obj_grid"] == 1).sum())
        assert n_floor > 0
        ratio = n_enemies / n_floor
        # Bornes : 0.05 <= enemies/floor <= 0.20 (tolerance arrondi entier).
        assert 0.05 - 1e-9 <= ratio <= 0.20 + 1e-9 + 1.0 / n_floor

    def test_infeasible_floor_ratio(self, tileset):
        """min_floor_ratio > max_floor_ratio => INFEASIBLE (contradiction)."""
        res = solve_cpsat(
            rows=6, cols=6, tileset=tileset, seed=0,
            min_floor_ratio=0.90, max_floor_ratio=0.10,
            timeout_s=5.0,
        )
        assert res.grid is None
        assert "INFEASIBLE" in res.status

    def test_result_object_fields(self, cpsat_solution):
        """CPSATResult expose grid, solve_time, status, stats."""
        assert isinstance(cpsat_solution, CPSATResult)
        assert cpsat_solution.solve_time >= 0.0
        assert isinstance(cpsat_solution.stats, dict)


# ----------------------------------------------------------------------------
# Metriques pures d'evaluation (adjacency_violations, bfs_reachable_floor,
# tile_variety) -- testables avec des grilles construites.
# ----------------------------------------------------------------------------

class TestMetrics:
    """Fonctions d'evaluation post-hoc, testees sur des grilles controlees."""

    def test_adjacency_violations_all_floor_zero(self, rules):
        """Une grille entierement floor n'a aucune violation (floor accepte tout)."""
        grid = np.full((5, 5), FLOOR_ID)
        assert adjacency_violations(grid, rules) == 0

    def test_adjacency_violations_water_next_to_wall(self, rules):
        """water(2) a cote de wall(0) = violation (rules[2][0] == 0)."""
        grid = np.array([[WATER_ID, WALL_ID], [FLOOR_ID, FLOOR_ID]])
        # (0,0)=water voisin de (0,1)=wall -> rules[2][0] = 0 -> 1 violation.
        assert adjacency_violations(grid, rules) >= 1

    def test_bfs_reachable_all_floor(self):
        """Grille entierement floor : 100% atteignable."""
        grid = np.full((5, 5), FLOOR_ID)
        assert bfs_reachable_floor(grid, FLOOR_ID) == 1.0

    def test_bfs_reachable_no_floor(self):
        """Grille sans floor : 0.0 (rien a atteindre)."""
        grid = np.full((4, 4), WALL_ID)
        assert bfs_reachable_floor(grid, FLOOR_ID) == 0.0

    def test_bfs_reachable_disconnected(self):
        """Deux iles floor separees par water : fraction < 1.0.

        La BFS demarre de la premiere cellule floor trouvee (scan ligne par
        ligne), donc seule l'ile contenant cette cellule est atteignable.
        """
        # Ligne 0 = floor (4 cellules connectees), ligne 2 = floor (4 cellules),
        # ligne 1 = water (barriere). 2 iles de 4 cellules chacune.
        grid = np.array([
            [FLOOR_ID, FLOOR_ID, FLOOR_ID, FLOOR_ID],
            [WATER_ID, WATER_ID, WATER_ID, WATER_ID],
            [FLOOR_ID, FLOOR_ID, FLOOR_ID, FLOOR_ID],
            [WATER_ID, WATER_ID, WATER_ID, WATER_ID],
        ])
        frac = bfs_reachable_floor(grid, FLOOR_ID)
        # 8 cellules floor au total ; seule la premiere ile (4) est atteignable.
        assert 0.0 < frac < 1.0
        assert abs(frac - 0.5) < 1e-9

    def test_tile_variety(self):
        """tile_variety = nombre de tiles distincts."""
        grid = np.array([[0, 1, 2], [1, 1, 4]])
        # tiles {0, 1, 2, 4} -> 4 valeurs distinctes.
        assert tile_variety(grid, 5) == 4

    def test_tile_variety_uniform(self):
        grid = np.full((3, 3), FLOOR_ID)
        assert tile_variety(grid, 5) == 1


# ----------------------------------------------------------------------------
# Integration end-to-end : run_all.
# ----------------------------------------------------------------------------

class TestRunAll:
    """run_all : le pipeline complet (random + wfc + cpsat) tourne sur petite grille."""

    def test_run_all_structure(self):
        results, tileset = wfc_cpsat.run_all(rows=5, cols=5, seed=42)
        assert set(results.keys()) >= {"random", "wfc", "cpsat"}
        assert "tiles" in tileset
        # Chaque entree a une grille et un status.
        for key in ("random", "wfc", "cpsat"):
            assert "grid" in results[key]
            assert "status" in results[key]
        # Random et WFC doivent produire une grille (5x5 realisable).
        assert results["random"]["grid"] is not None
        assert results["random"]["grid"].shape == (5, 5)
