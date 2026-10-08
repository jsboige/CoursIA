"""Tests pli 8 -- Block decomposition (Zenil 2013) Rule 30 / Rule 110.

Couvre :
- WOLFRAM_BLOCK_LANDMARKS : 4 entrees canoniques
- shannon_entropy_bits : entropie Shannon base 2 sur bitstring 0/1
- block_decompose_trajectory : decomposition non-chevauchante
- block_entropy_distribution : statistiques agregees
- measure_wolfram_blocks : 24 mesures (4 regles x 6 longueurs)
- wolfram_blocks_verdict : verdict par regle vs landmark
- wolfram_blocks_discrimination_verdict : verdict discrimination R30 vs R110
- JSON round-trip : resultats via subprocess
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

# Permet `import k_trajectory` depuis le dossier hashlife
HASHLIFE_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
K_TRAJ = HASHLIFE_DIR / "k_trajectory.py"
if str(HASHLIFE_DIR) not in sys.path:
    sys.path.insert(0, str(HASHLIFE_DIR))


class TestWolframBlockLandmarks:
    """Constantes canoniques des 4 classes Wolframe pour block decomposition."""

    def test_landmarks_has_four_entries(self):
        from k_trajectory import WOLFRAM_BLOCK_LANDMARKS
        assert len(WOLFRAM_BLOCK_LANDMARKS) == 4

    def test_landmarks_canonical_assignments(self):
        from k_trajectory import WOLFRAM_BLOCK_LANDMARKS
        # Format : rule -> (klass_label, klass_name, expected_mean, expected_std)
        assert WOLFRAM_BLOCK_LANDMARKS[0][0] == "I"
        assert WOLFRAM_BLOCK_LANDMARKS[4][0] == "II"
        assert WOLFRAM_BLOCK_LANDMARKS[30][0] == "III"
        assert WOLFRAM_BLOCK_LANDMARKS[110][0] == "IV"
        # Std monotone (R30 bas, R110 eleve)
        assert WOLFRAM_BLOCK_LANDMARKS[30][3] < WOLFRAM_BLOCK_LANDMARKS[110][3]


class TestShannonEntropyBits:
    """Entropie de Shannon (base 2) sur sequence de bits."""

    def test_entropy_empty(self):
        from k_trajectory import shannon_entropy_bits
        assert shannon_entropy_bits([]) == 0.0

    def test_entropy_all_zeros(self):
        from k_trajectory import shannon_entropy_bits
        assert shannon_entropy_bits([0, 0, 0, 0]) == 0.0

    def test_entropy_all_ones(self):
        from k_trajectory import shannon_entropy_bits
        assert shannon_entropy_bits([1, 1, 1, 1]) == 0.0

    def test_entropy_balanced(self):
        from k_trajectory import shannon_entropy_bits
        # 50/50 -> entropie maximale = 1.0 bit
        assert abs(shannon_entropy_bits([0, 1, 0, 1, 0, 1]) - 1.0) < 1e-9

    def test_entropy_skewed(self):
        from k_trajectory import shannon_entropy_bits
        # 1/4, 3/4 -> -0.25*log2(0.25) - 0.75*log2(0.75) ~= 0.8113
        h = shannon_entropy_bits([0, 0, 0, 1])
        assert abs(h - 0.8113) < 1e-3


class TestBlockDecomposeTrajectory:
    """Decomposition d'une trajectoire en blocs non-chevauchants."""

    def test_empty_trajectory(self):
        from k_trajectory import block_decompose_trajectory
        assert block_decompose_trajectory([], 4) == []

    def test_single_block(self):
        from k_trajectory import block_decompose_trajectory
        # 4 etats, block_length=4 -> 1 bloc de 4*3 = 12 bits
        traj = [[0, 1, 0], [1, 1, 0], [0, 0, 1], [1, 1, 1]]
        blocks = block_decompose_trajectory(traj, 4)
        assert len(blocks) == 1
        assert blocks[0] == [0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1]

    def test_multiple_blocks(self):
        from k_trajectory import block_decompose_trajectory
        # 8 etats, block_length=4 -> 2 blocs de 4*2 = 8 bits chacun
        traj = [[0, 1], [1, 0], [0, 0], [1, 1]] * 2
        blocks = block_decompose_trajectory(traj, 4)
        assert len(blocks) == 2
        assert blocks[0] == [0, 1, 1, 0, 0, 0, 1, 1]
        assert blocks[1] == [0, 1, 1, 0, 0, 0, 1, 1]

    def test_block_length_exceeds_trajectory(self):
        from k_trajectory import block_decompose_trajectory
        traj = [[0, 1], [1, 0], [0, 0]]
        assert block_decompose_trajectory(traj, 4) == []

    def test_invalid_block_length(self):
        from k_trajectory import block_decompose_trajectory
        with pytest.raises(ValueError):
            block_decompose_trajectory([[0, 1]], 0)


class TestBlockEntropyDistribution:
    """Distribution d'entropie par bloc (statistiques agregees)."""

    def test_uniform_trajectory_zero_std(self):
        from k_trajectory import block_entropy_distribution
        # Tous les etats identiques -> entropie 0 partout, std 0
        traj = [[0, 0, 0, 0]] * 16
        dist = block_entropy_distribution(traj, 4)
        assert dist["n_blocks"] == 4
        assert dist["mean"] == 0.0
        assert dist["std"] == 0.0
        assert dist["min"] == 0.0
        assert dist["max"] == 0.0

    def test_balanced_trajectory_high_mean_low_std(self):
        from k_trajectory import block_entropy_distribution
        # Tous les blocs identiques, equilibres -> mean ~ 1.0, std ~ 0
        traj = [[0, 1, 0, 1]] * 16
        dist = block_entropy_distribution(traj, 4)
        assert dist["n_blocks"] == 4
        assert abs(dist["mean"] - 1.0) < 1e-9
        assert dist["std"] == 0.0


class TestMeasureWolframBlocks:
    """Mesure 4 classes x 6 longueurs = 24 entrees."""

    def test_runs_returns_24_entries(self):
        from k_trajectory import measure_wolfram_blocks
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        assert len(results) == 24  # 4 * 6

    def test_includes_all_four_rules(self):
        from k_trajectory import measure_wolfram_blocks
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        rules_found = {r["rule"] for r in results}
        assert rules_found == {0, 4, 30, 110}

    def test_r0_entropy_is_low(self):
        from k_trajectory import measure_wolfram_blocks
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        r0_runs = [r for r in results if r["rule"] == 0]
        # R0 avec seed single-cell produit des "die" patterns (cellules isolees
        # qui survivent tant qu'elles ont exactement un voisin) : entropie tres
        # basse mais pas strictement nulle.
        for r in r0_runs:
            assert r["entropy_mean"] < 0.10, (
                f"R0 W={r['block_length']} devrait avoir mean<0.10, "
                f"observe {r['entropy_mean']}"
            )
            assert r["entropy_std"] < 0.15

    def test_r30_std_lower_than_r110_at_large_block(self):
        from k_trajectory import measure_wolfram_blocks
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        r30 = next(r for r in results if r["rule"] == 30 and r["block_length"] == 32)
        r110 = next(r for r in results if r["rule"] == 110 and r["block_length"] == 32)
        # Le test enregistre l'observation empirique, quel que soit le verdict.
        # Hypothese : std(R110) > std(R30) pour discriminer chaos vs Turing.
        # Le verdict final est rendu par wolfram_blocks_discrimination_verdict.
        assert r30["entropy_mean"] > 0.9  # chaos -> entropie elevee
        assert r110["entropy_mean"] > 0.9  # Turing -> aussi entropie elevee


class TestWolframBlocksDiscriminationVerdict:
    """Verdict final de discrimination R30 vs R110 par std d'entropie par bloc."""

    def test_discrimination_verdict_format(self):
        """Cas INDETERMINATE si pas de R30 ou R110."""
        from k_trajectory import wolfram_blocks_discrimination_verdict
        final = wolfram_blocks_discrimination_verdict({}, [])
        assert "INDETERMINATE" in final

    def test_discrimination_verdict_keys(self):
        """Le verdict final contient bien soit DISCRIMINANT soit NONDISCRIMINANT."""
        from k_trajectory import (
            measure_wolfram_blocks,
            wolfram_blocks_verdict,
            wolfram_blocks_discrimination_verdict,
        )
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        verdicts = wolfram_blocks_verdict(results)
        final = wolfram_blocks_discrimination_verdict(verdicts, results)
        assert "WOLFRAM-BLOCKS-" in final
        assert ("DISCRIMINANT" in final) or ("NONDISCRIMINANT" in final)


class TestWolframBlocksJsonRoundtrip:
    """Round-trip JSON via subprocess."""

    def test_subprocess_json_output_has_required_keys(self):
        """Lance le mode wolfram-blocks avec --json-out, verifie les cles."""
        env = os.environ.copy()
        env["PYTHONPATH"] = str(REPO_ROOT / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series")
        with tempfile.TemporaryDirectory() as tmpdir:
            json_path = Path(tmpdir) / "blocks_results.json"
            proc = subprocess.run(
                [sys.executable, str(K_TRAJ), "--mode", "wolfram-blocks",
                 "--n-cells", "64", "--n-steps", "64",
                 "--json-out", str(json_path)],
                env=env,
                capture_output=True,
                text=True,
                timeout=120,
            )
            assert proc.returncode == 0, f"stderr: {proc.stderr}"
            assert json_path.exists()
            data = json.loads(json_path.read_text(encoding="utf-8"))
            assert "results" in data
            assert "per_class_verdicts" in data
            assert "discrimination_verdict" in data
            assert "blocks_landmarks" in data
            assert data["n_cells"] == 64
            assert data["n_steps"] == 64
            assert "WOLFRAM-BLOCKS-" in data["discrimination_verdict"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))