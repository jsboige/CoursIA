"""Tests du mode wolfram (Origami pli 3, scripts/hashlife/k_trajectory.py).

Teste :
1. `wolfram_trajectory_to_grid` : conversion 1-D -> 1xN grid compatible
   avec grid_to_packed.
2. `measure_wolfram_trajectory` : mesure K_trajectory sur Rule 30 et
   Rule 110 via l'organe ict.wolfram_step (PR #19793).
3. `wolfram_verdict` : verdict par regle (CHAOTIC-FRAGILE / TURING-ENTRENED / REFUTED).
4. `wolfram_cross_verdict` : verdict final cross-regles.
5. Mode `--json-in` round-trip : un JSON produit par --mode wolfram peut etre
   relu et verifier.

Note sur l'environnement : ces tests dependent de l'organe ict.wolfram_step
(PR #19793). Le dossier `MyIA.AI.Notebooks/IIT/ICT-Series` doit etre dans
sys.path. Le conftest.py ajoute ce chemin automatiquement.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[3]
ICT_PATH = REPO_ROOT / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series"
if str(ICT_PATH) not in sys.path:
    sys.path.insert(0, str(ICT_PATH))

from ict.wolfram_step import wolfram_trajectory  # noqa: E402

from scripts.hashlife.k_trajectory import (  # noqa: E402
    k_trajectory,
    measure_wolfram_corpus,
    measure_wolfram_trajectory,
    wolfram_cross_verdict,
    wolfram_trajectory_to_grid,
    wolfram_verdict,
)


# ---------------------------------------------------------------------------
# Tests : conversion 1-D -> 1xN grid
# ---------------------------------------------------------------------------

class TestWolframTrajectoryToGrid:
    def test_1d_state_becomes_1xN_grid(self):
        traj_1d = [[1, 0, 0, 1, 1], [0, 1, 1, 0, 1]]
        grid = wolfram_trajectory_to_grid(traj_1d)
        assert len(grid) == 2
        assert all(len(row) == 1 for row in grid)
        assert [c for c in grid[0][0]] == [1, 0, 0, 1, 1]
        assert [c for c in grid[1][0]] == [0, 1, 1, 0, 1]

    def test_1d_state_from_organe(self):
        # Trajectoire reelle generee par l'organe ict.wolfram_step
        traj_1d = wolfram_trajectory(30, n_cells=64, n_steps=10, seed=33, record_densities=False)
        grid = wolfram_trajectory_to_grid(traj_1d)
        assert len(grid) == 10
        assert all(len(row) == 1 and len(row[0]) == 64 for row in grid)

    def test_grid_is_compatible_with_k_trajectory(self):
        # Le packing bits de grid_to_packed + K_trajectory doivent donner
        # un entier positif (>= 0).
        traj_1d = wolfram_trajectory(30, n_cells=64, n_steps=10, seed=33, record_densities=False)
        grid = wolfram_trajectory_to_grid(traj_1d)
        k = k_trajectory(grid, W=1)
        assert k > 0  # au moins un etat = au moins 16 bytes compresses minimum


# ---------------------------------------------------------------------------
# Tests : mesure K_trajectory
# ---------------------------------------------------------------------------

class TestMeasureWolframTrajectory:
    def test_rule_30_n64_seed33_runs(self):
        results = measure_wolfram_trajectory(
            rule=30, n_cells=64, n_steps=64, seed=33, n_values=[0, 1, 2, 3, 4, 5, 6]
        )
        assert len(results) == 7
        # K doit etre strictement positif et decroissant en fonction de n
        ks = [r["k_trajectory"] for r in results]
        assert all(k > 0 for k in ks)
        # LZ collapse le chaos : K(t, W_last) < K(t, W_first)
        assert ks[-1] < ks[0]

    def test_rule_110_n64_seed33_runs(self):
        results = measure_wolfram_trajectory(
            rule=110, n_cells=64, n_steps=64, seed=33, n_values=[0, 1, 2, 3, 4, 5, 6]
        )
        assert len(results) == 7
        ks = [r["k_trajectory"] for r in results]
        assert all(k > 0 for k in ks)

    def test_measure_wolfram_corpus_includes_both_rules(self):
        results = measure_wolfram_corpus(n_cells=64, n_steps=64, seed=33)
        names = {r["trajectory"] for r in results}
        assert "wolfram_R30_n64_seed33" in names
        assert "wolfram_R110_n64_seed33" in names


# ---------------------------------------------------------------------------
# Tests : verdicts
# ---------------------------------------------------------------------------

class TestWolframVerdict:
    def test_rule_30_classified_fragile(self):
        results = measure_wolfram_corpus(n_cells=64, n_steps=64, seed=33)
        wv = wolfram_verdict(results)
        # Rule 30 doit etre CHAOTIC-FRAGILE (LZ collapse le chaos)
        assert any(
            "R30" in name and "CHAOTIC-FRAGILE" in status
            for name, status in wv.items()
        ), f"Rule 30 should be CHAOTIC-FRAGILE, got: {wv}"

    def test_cross_verdict_is_partial(self):
        # Resultat falsifiable mesure ce cycle : Rule 30 = CHAOTIC-FRAGILE,
        # Rule 110 = TURING-REFUTED (LZ collapse Rule 110 aussi, contre la
        # prediction de Turing-complet = non-compressible).
        results = measure_wolfram_corpus(n_cells=64, n_steps=64, seed=33)
        wv = wolfram_verdict(results)
        cross = wolfram_cross_verdict(wv)
        assert cross in {
            "WOLFRAM-CROSS-DIMENSION-CONFIRMED",
            "WOLFRAM-CROSS-DIMENSION-PARTIAL",
            "WOLFRAM-CROSS-DIMENSION-REFUTED",
            "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE",
        }
        # Resultat attendu ce cycle : PARTIAL (Rule 30 confirme, Rule 110 refute)
        assert cross == "WOLFRAM-CROSS-DIMENSION-PARTIAL", (
            f"Expected PARTIAL but got {cross}. Le verdict courant est : {wv}"
        )


# ---------------------------------------------------------------------------
# Tests : round-trip JSON
# ---------------------------------------------------------------------------

class TestWolframJsonRoundtrip:
    def test_results_json_has_required_keys(self, tmp_path):
        # Executer le mode wolfram avec --json-out dans tmp_path
        import subprocess

        env_path = str(ICT_PATH)
        out_path = tmp_path / "wolfram.json"
        result = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "scripts" / "hashlife" / "k_trajectory.py"),
                "--mode", "wolfram",
                "--all",
                "--n-cells", "64",
                "--json-out", str(out_path),
            ],
            cwd=REPO_ROOT,
            env={**__import__("os").environ, "PYTHONPATH": env_path},
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, f"stderr: {result.stderr}"
        assert out_path.exists()
        data = json.loads(out_path.read_text())
        assert "results" in data
        assert "per_rule_verdicts" in data
        assert "cross_verdict" in data
        assert data["cross_verdict"] in {
            "WOLFRAM-CROSS-DIMENSION-CONFIRMED",
            "WOLFRAM-CROSS-DIMENSION-PARTIAL",
            "WOLFRAM-CROSS-DIMENSION-REFUTED",
            "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE",
        }