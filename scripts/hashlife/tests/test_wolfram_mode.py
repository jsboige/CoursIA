"""Tests du mode wolfram (Origami pli 3, scripts/hashlife/k_trajectory.py).

Teste :
1. `wolfram_trajectory_to_grid` : conversion 1-D -> 1xN grid compatible
   avec grid_to_packed.
2. `measure_wolfram_trajectory` : mesure K_trajectory sur Rule 30 et
   Rule 110 via l'organe ict.wolfram_step (PR #19793).
3. `wolfram_verdict` : verdict par regle (SATURATED sous n_cells=512 ;
   INCOMPRESSIBLE / STRUCTURED-COMPRESSIBLE / WEAK au-dessus).
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

# Mesures mise en cache par taille (chaque test reutilise le meme corpus).
_CORPUS_CACHE: dict[int, list[dict]] = {}


def _corpus(n_cells: int) -> list[dict]:
    if n_cells not in _CORPUS_CACHE:
        _CORPUS_CACHE[n_cells] = measure_wolfram_corpus(
            n_cells=n_cells, n_steps=n_cells, seed=33
        )
    return _CORPUS_CACHE[n_cells]


class TestWolframVerdict:
    def test_n64_is_saturated_artifact_zone(self):
        # A n_cells=64, chaque etat packe (8 octets) est sous le plancher de
        # cadrage zlib (~11 octets/fenetre) : Rule 30 et Rule 110 y mesurent
        # identiques a l'octet pres. L'instrument doit refuser de discriminer
        # (SATURATED / INCONCLUSIVE), pas fabriquer un verdict de cadrage.
        results = _corpus(64)
        wv = wolfram_verdict(results)
        assert all("SATURATED" in s for s in wv.values()), wv
        assert wolfram_cross_verdict(wv) == "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE"

    def test_rule_30_incompressible_at_512(self):
        # Mesure falsifiable : le chaos classe III ne compresse pas -- chaque
        # fenetre reste au plafond d'entropie (frac ~ 1.00, per-state K(W=1)
        # = contenu + 11 = plancher de cadrage exact).
        wv = wolfram_verdict(_corpus(512))
        r30 = next(s for n, s in wv.items() if "R30" in n)
        assert "CHAOTIC-INCOMPRESSIBLE" in r30, wv

    def test_rule_110_structured_compressible_at_512(self):
        # Mesure falsifiable : la structure emergente de Rule 110 (fond
        # periodique + particules) est reguliere donc LZ-compressible
        # (frac ~ 0.57 a n=512, ~ 0.43 a n=1024).
        wv = wolfram_verdict(_corpus(512))
        r110 = next(s for n, s in wv.items() if "R110" in n)
        assert "STRUCTURED-COMPRESSIBLE" in r110, wv

    def test_cross_verdict_is_refuted_inverted_at_512(self):
        # Resultat falsifiable remesure : a n_cells >= 512 l'instrument
        # discrimine les deux regles, mais dans le sens INVERSE de
        # l'hypothese cross-dimension -- chaos incompressible, Turing-complet
        # compressible. L'ancien verdict PARTIAL etait un artefact de cadrage
        # a n=64 (les deux regles y sont identiques a l'octet pres).
        wv = wolfram_verdict(_corpus(512))
        cross = wolfram_cross_verdict(wv)
        assert cross in {
            "WOLFRAM-CROSS-DIMENSION-CONFIRMED",
            "WOLFRAM-CROSS-DIMENSION-PARTIAL",
            "WOLFRAM-CROSS-DIMENSION-REFUTED",
            "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE",
        }
        assert cross == "WOLFRAM-CROSS-DIMENSION-REFUTED", (
            f"Expected REFUTED (direction inversee) but got {cross}. "
            f"Le verdict courant est : {wv}"
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
        # A n_cells=64 (zone saturee), le CLI doit rendre SATURATED par regle
        # et INCONCLUSIVE en cross -- aucune discrimination n'y est honnete.
        assert all("SATURATED" in s for s in data["per_rule_verdicts"].values())
        assert data["cross_verdict"] == "WOLFRAM-CROSS-DIMENSION-INCONCLUSIVE"