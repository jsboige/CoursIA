"""Tests pli 7 -- Kolmogorov structure function Rule 30 / Rule 110.

Couvre :
- WOLFRAM_KSF_LANDMARKS : 4 entrees canoniques
- ksf_trajectory : KSF(W) sur une regle donnee
- measure_wolfram_ksf : 24 mesures (4 regles × 6 contextes)
- wolfram_ksf_verdict : verdict par regle
- wolfram_ksf_discrimination_verdict : verdict discrimination R30 vs R110
- pack_states_1d : packing MSB-first
- JSON round-trip : resultats via subprocess
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

# Permet `import k_trajectory` depuis le dossier hashlife
HASHLIFE_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = Path(__file__).resolve().parents[3]
K_TRAJ = HASHLIFE_DIR / "k_trajectory.py"
if str(HASHLIFE_DIR) not in sys.path:
    sys.path.insert(0, str(HASHLIFE_DIR))


class TestWolframKSFLandmarks:
    """Constantes canoniques des 4 classes Wolframe pour KSF."""

    def test_landmarks_has_four_entries(self):
        from k_trajectory import WOLFRAM_KSF_LANDMARKS
        assert len(WOLFRAM_KSF_LANDMARKS) == 4

    def test_landmarks_canonical_assignments(self):
        from k_trajectory import WOLFRAM_KSF_LANDMARKS
        # Format : rule -> (klass_label, klass_name, expected_ksf)
        assert WOLFRAM_KSF_LANDMARKS[0][0] == "I"
        assert WOLFRAM_KSF_LANDMARKS[4][0] == "II"
        assert WOLFRAM_KSF_LANDMARKS[30][0] == "III"
        assert WOLFRAM_KSF_LANDMARKS[110][0] == "IV"
        # Expected KSF monotone (R0/R4 nuls, R30 eleve, R110 intermediaire)
        assert WOLFRAM_KSF_LANDMARKS[0][2] == 0.0
        assert WOLFRAM_KSF_LANDMARKS[4][2] == 0.0
        assert WOLFRAM_KSF_LANDMARKS[30][2] > WOLFRAM_KSF_LANDMARKS[110][2]


class TestPackStates1D:
    """Packing MSB-first 8 cellules par octet."""

    def test_pack_single_state(self):
        from k_trajectory import pack_states_1d
        # 8 bits -> 1 octet MSB first
        states = [[1, 0, 1, 0, 1, 0, 1, 0]]
        packed = pack_states_1d(states)
        assert packed == bytes([0b10101010])

    def test_pack_two_states(self):
        from k_trajectory import pack_states_1d
        states = [
            [1, 1, 1, 1, 1, 1, 1, 1],
            [0, 0, 0, 0, 0, 0, 0, 0],
        ]
        packed = pack_states_1d(states)
        assert packed == bytes([0b11111111, 0b00000000])

    def test_pack_empty(self):
        from k_trajectory import pack_states_1d
        assert pack_states_1d([]) == b""
        assert pack_states_1d([[]]) == b""

    def test_pack_with_padding(self):
        """n_cells pas multiple de 8 : padding MSB=0 sur le dernier octet."""
        from k_trajectory import pack_states_1d
        # 5 bits -> 1 octet, 3 bits de padding MSB=0
        states = [[1, 1, 1, 1, 1]]
        packed = pack_states_1d(states)
        assert packed == bytes([0b11111000])


class TestKsfTrajectory:
    """Mesure KSF sur une trajectoire Wolframe."""

    def test_ksf_r4_class_ii_is_zero_at_large_context(self):
        """R4 (periodique) doit avoir KSF(W=4+) = 0 (contexte capture la periode)."""
        from k_trajectory import ksf_trajectory
        results = ksf_trajectory(rule=4, n_cells=64, n_steps=64, seed=33,
                                 context_sizes=(4, 8, 16, 32))
        for r in results:
            assert r["ksf_mean"] < 0.5, (
                f"R4 W={r['W_context']} devrait avoir KSF ~ 0, observe {r['ksf_mean']}"
            )

    def test_ksf_r30_class_iii_is_high(self):
        """R30 (chaotique) doit avoir KSF elevee (contexte n'aide pas)."""
        from k_trajectory import ksf_trajectory
        results = ksf_trajectory(rule=30, n_cells=64, n_steps=64, seed=33,
                                 context_sizes=(8, 16, 32))
        for r in results:
            assert r["ksf_mean"] >= 5.0, (
                f"R30 W={r['W_context']} devrait avoir KSF >= 5, observe {r['ksf_mean']}"
            )

    def test_ksf_n_measurements_decreases_with_W(self):
        """Pour W croissant, le nombre de pas mesurables (n_steps - W) doit decroitre."""
        from k_trajectory import ksf_trajectory
        results = ksf_trajectory(rule=30, n_cells=64, n_steps=64, seed=33,
                                 context_sizes=(1, 8, 32))
        n_meas = [r["n_measurements"] for r in results]
        assert n_meas == sorted(n_meas, reverse=True)


class TestMeasureWolframKSF:
    """Mesure 4 classes × 6 contextes = 24 entrees."""

    def test_runs_returns_24_entries(self):
        from k_trajectory import measure_wolfram_ksf
        results = measure_wolfram_ksf(n_cells=64, n_steps=64, seed=33)
        assert len(results) == 24  # 4 * 6

    def test_includes_all_four_rules(self):
        from k_trajectory import measure_wolfram_ksf
        results = measure_wolfram_ksf(n_cells=64, n_steps=64, seed=33)
        rules_found = {r["rule"] for r in results}
        assert rules_found == {0, 4, 30, 110}


class TestWolframKSFDiscriminationVerdict:
    """Verdict final de discrimination R30 vs R110."""

    def test_ksf_is_nondiscriminant_on_c111(self):
        """Sur c.111, R30 et R110 produisent KSF(W=32) identique -> NONDISCRIMINANT."""
        from k_trajectory import (
            measure_wolfram_ksf,
            wolfram_ksf_verdict,
            wolfram_ksf_discrimination_verdict,
        )
        results = measure_wolfram_ksf(n_cells=64, n_steps=64, seed=33)
        verdicts = wolfram_ksf_verdict(results)
        final = wolfram_ksf_discrimination_verdict(verdicts, results)
        assert "WOLFRAM-KSF-NONDISCRIMINANT" in final, (
            f"Verdict attendu NONDISCRIMINANT, observe : {final}"
        )

    def test_discrimination_verdict_format(self):
        """Cas INDETERMINATE si pas de R30 ou R110."""
        from k_trajectory import wolfram_ksf_discrimination_verdict
        final = wolfram_ksf_discrimination_verdict({}, [])
        assert "INDETERMINATE" in final


class TestWolframKSFJsonRoundtrip:
    """Round-trip JSON via subprocess."""

    def test_subprocess_json_output_has_required_keys(self):
        """Lance le mode wolfram-ksf avec --json-out, verifie les cles."""
        import os
        import tempfile
        env = os.environ.copy()
        env["PYTHONPATH"] = str(REPO_ROOT / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series")
        with tempfile.TemporaryDirectory() as tmpdir:
            json_path = Path(tmpdir) / "ksf_results.json"
            proc = subprocess.run(
                [sys.executable, str(K_TRAJ), "--mode", "wolfram-ksf",
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
            assert "ksf_landmarks" in data
            assert data["n_cells"] == 64
            assert data["n_steps"] == 64
            assert "WOLFRAM-KSF" in data["discrimination_verdict"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))