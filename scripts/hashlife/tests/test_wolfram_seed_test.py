"""Tests pli 9 -- Seed specialise R110 (0001000) + 3 complexites.

Couvre :
- WOLFRAM_SEED_PRESETS : 4 entrees canoniques
- wolfram_seed_preset : generation d'etat initial, padding, single-cell special
- wolfram_trajectory_from_state : trajectoire 1-D via wolfram_step organ
- _traj_states_to_grid : conversion vers format grid 1xN
- measure_seed_instrument_landscape : 48 mesures (4 regles x 4 presets x 3 instruments)
- seed_discrimination_verdict : verdict par preset x instrument + global
- JSON round-trip : resultats via subprocess avec PYTHONPATH
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


class TestWolframSeedPresets:
    """Constantes canoniques des 4 presets de seed pour pli 9."""

    def test_presets_has_four_entries(self):
        from k_trajectory import WOLFRAM_SEED_PRESETS
        assert len(WOLFRAM_SEED_PRESETS) == 4

    def test_presets_canonical_names(self):
        from k_trajectory import WOLFRAM_SEED_PRESETS
        assert "single-cell" in WOLFRAM_SEED_PRESETS
        assert "wolfram-0001000" in WOLFRAM_SEED_PRESETS
        assert "wolfram-defect" in WOLFRAM_SEED_PRESETS
        assert "random-dense" in WOLFRAM_SEED_PRESETS

    def test_presets_values_are_binary_strings(self):
        from k_trajectory import WOLFRAM_SEED_PRESETS
        for name, pattern in WOLFRAM_SEED_PRESETS.items():
            assert isinstance(pattern, str)
            assert all(c in "01" for c in pattern), f"{name}: not binary"


class TestWolframSeedPreset:
    """Generation d'etat initial a partir d'un preset."""

    def test_single_cell_centered(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("single-cell", 64)
        assert len(state) == 64
        n_ones = sum(state)
        assert n_ones == 1
        assert state[32] == 1
        assert sum(state[i] for i in range(64) if i != 32) == 0

    def test_single_cell_asymmetric(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("single-cell", 100)
        assert len(state) == 100
        assert sum(state) == 1
        assert state[50] == 1

    def test_wolfram_0001000_pattern(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("wolfram-0001000", 64)
        assert len(state) == 64
        # Le pattern "0001000" (7 chars) est repete puis tronque a 64.
        # "0001000" * 10 = 70 chars ; les 64 premiers sont la sortie.
        expected = ("0001000" * 10)[:64]
        assert "".join(str(c) for c in state) == expected

    def test_wolfram_0001000_truncation(self):
        from k_trajectory import wolfram_seed_preset
        # n_cells non multiple de 7 : le pattern est repete puis tronque.
        state = wolfram_seed_preset("wolfram-0001000", 32)
        assert len(state) == 32
        # "0001000" * 5 = 35 ; les 32 premiers sont la sortie.
        expected = ("0001000" * 5)[:32]
        assert "".join(str(c) for c in state) == expected

    def test_wolfram_defect_pattern(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("wolfram-defect", 64)
        assert len(state) == 64
        # Le pattern source = "0001000" repete, derniere cellule forcee a 1
        # avant troncature a 64.
        # Le pattern source : "0001000" * 8 = 56 chars + "1" = 57 chars.
        # Repete pour atteindre 64 : "0001000" * 10 = 70, mais on prend
        # la version defect : ("0001000" * 8)[:63] + "1" = 64 chars.
        # En realite la fonction repete le pattern source direct.
        expected = (("0001000" * 8)[:63] + "1")
        # La fonction repete le pattern source ; calculons :
        src = ("0001000" * 8)[:63] + "1"  # 64 chars
        # Le while repete src directement.
        out_str = ""
        while len(out_str) < 64:
            out_str += src
        out_str = out_str[:64]
        assert "".join(str(c) for c in state) == out_str

    def test_random_dense_pattern(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("random-dense", 64)
        assert len(state) == 64
        # "10110011" * 8 = 64 exactement, pas de troncature.
        expected = "10110011" * 8
        assert "".join(str(c) for c in state) == expected

    def test_unknown_preset_raises(self):
        from k_trajectory import wolfram_seed_preset
        with pytest.raises(ValueError, match="Preset inconnu"):
            wolfram_seed_preset("nonexistent", 64)


class TestWolframTrajectoryFromState:
    """Trajectoire 1-D a partir d'un etat initial explicite."""

    def test_trajectory_length(self):
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 32)
        traj = wolfram_trajectory_from_state(state, rule=30, n_steps=10)
        assert len(traj) == 10
        assert all(len(s) == 32 for s in traj)

    def test_trajectory_first_state_is_init(self):
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 32)
        traj = wolfram_trajectory_from_state(state, rule=30, n_steps=5)
        # Premier etat = init_state
        assert traj[0] == state

    def test_rule30_single_cell_chaotic(self):
        """Rule 30 single-cell : trajectoire non triviale apres quelques pas."""
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 64)
        traj = wolfram_trajectory_from_state(state, rule=30, n_steps=20)
        # Au pas 1, single-cell Rule 30 produit un triplet 0011100 (3 cellules)
        # au lieu d'1 : la propagation est visible.
        n_ones_step_0 = sum(traj[0])
        n_ones_step_1 = sum(traj[1])
        # Pas 0 = 1 cellule allumee (single-cell)
        assert n_ones_step_0 == 1
        # Pas 1 doit etre different (Rule 30 single-cell = 3 cellules)
        assert n_ones_step_1 != 1

    def test_rule0_constant(self):
        """Rule 0 (toujours 0) : trajectoire constante a zero."""
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 32)
        traj = wolfram_trajectory_from_state(state, rule=0, n_steps=10)
        # Rule 0 : tous les etats apres le pas 0 = tout a 0
        for t in range(1, len(traj)):
            assert sum(traj[t]) == 0


class TestTrajStatesToGrid:
    """Conversion trajectoire 1-D en liste de grilles 1xN."""

    def test_grid_shape(self):
        from k_trajectory import _traj_states_to_grid
        traj = [[0, 1, 0, 1], [1, 0, 1, 0]]
        grid = _traj_states_to_grid(traj)
        assert len(grid) == 2
        assert all(len(g) == 1 for g in grid)  # 1 ligne par grille
        assert all(len(g[0]) == 4 for g in grid)  # 4 colonnes

    def test_grid_packing_compatible(self):
        from k_trajectory import _traj_states_to_grid, grid_to_packed
        traj = [[1, 1, 1, 1, 1, 1, 1, 1]]
        grid = _traj_states_to_grid(traj)
        # grid_to_packed devrait fonctionner sur la grille 1xN
        packed = grid_to_packed(grid[0])
        assert len(packed) == 1
        assert packed == b"\xff"


class TestMeasureSeedInstrumentLandscape:
    """Mesure 3 complexites sur le paysage de seeds."""

    def test_landscape_size(self):
        """4 regles x 4 presets x 3 instruments = 48 mesures."""
        from k_trajectory import measure_seed_instrument_landscape
        # Utiliser n=16 pour accelerer le test.
        landscape = measure_seed_instrument_landscape(
            n_cells=16, n_steps=16,
        )
        assert len(landscape) == 48

    def test_landscape_keys(self):
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        first = landscape[0]
        for k in ("rule", "preset", "n_cells", "n_steps", "instrument", "summary"):
            assert k in first, f"Missing key: {k}"

    def test_landscape_lz_has_required_keys(self):
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        lz_rows = [r for r in landscape if r["instrument"] == "lz"]
        for r in lz_rows:
            assert "k_last" in r
            assert "k_first" in r
            assert "k_last_over_first" in r
            assert "lz_W" in r
            assert "lz_k_over_n" in r

    def test_landscape_ksf_has_required_keys(self):
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        ksf_rows = [r for r in landscape if r["instrument"] == "ksf"]
        for r in ksf_rows:
            assert "ksf_last" in r
            assert "ksf_first" in r
            assert "ksf_last_minus_first" in r
            assert "ksf_W" in r

    def test_landscape_blocks_has_required_keys(self):
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        blocks_rows = [r for r in landscape if r["instrument"] == "blocks"]
        for r in blocks_rows:
            assert "blocks_mean_at_W32" in r
            assert "blocks_std_at_W32" in r
            assert "blocks_W" in r


class TestSeedDiscriminationVerdict:
    """Verdict de discrimination R30 vs R110 sur le paysage de seeds."""

    def test_empty_landscape(self):
        from k_trajectory import seed_discrimination_verdict
        v = seed_discrimination_verdict([])
        assert v["global"] == "EMPTY"
        assert v["discriminative_presets"] == 0

    def test_full_landscape_verdict_structure(self):
        from k_trajectory import measure_seed_instrument_landscape, seed_discrimination_verdict
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        v = seed_discrimination_verdict(landscape)
        assert "per_instrument" in v
        assert "global" in v
        assert "discriminative_presets" in v
        assert "total_presets" in v
        # per_instrument : 3 instruments x 4 presets = 12 verdicts
        assert v["total_presets"] == 12
        # global : un de {DISCRIMINANT_FORT, DISCRIMINANT_FAIBLE, NONDISCRIMINANT_CONFIRME}
        assert v["global"] in (
            "DISCRIMINANT_FORT", "DISCRIMINANT_FAIBLE", "NONDISCRIMINANT_CONFIRME"
        )

    def test_verdict_values_are_valid(self):
        from k_trajectory import measure_seed_instrument_landscape, seed_discrimination_verdict
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        v = seed_discrimination_verdict(landscape)
        for instrument, verdicts in v["per_instrument"].items():
            for preset, verdict in verdicts.items():
                assert verdict in (
                    "DISCRIMINANT", "WEAK-DISCRIMINANT", "NONDISCRIMINANT", "INCOMPLETE"
                ), f"Invalid verdict: {instrument}/{preset} = {verdict}"


class TestWolframSeedTestJsonRoundtrip:
    """Round-trip JSON via subprocess avec PYTHONPATH pour ict.wolfram_step."""

    def test_subprocess_json_output_has_required_keys(self):
        """Lance le mode wolfram-seed-test avec --json-out, verifie les cles."""
        env = os.environ.copy()
        env["PYTHONPATH"] = str(REPO_ROOT / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series")
        with tempfile.TemporaryDirectory() as tmpdir:
            json_path = Path(tmpdir) / "seed_test_results.json"
            proc = subprocess.run(
                [sys.executable, str(K_TRAJ), "--mode", "wolfram-seed-test",
                 "--n-cells", "16", "--n-steps", "16",
                 "--json-out", str(json_path)],
                env=env,
                capture_output=True,
                text=True,
                timeout=120,
            )
            assert proc.returncode == 0, f"stderr: {proc.stderr}"
            assert json_path.exists()
            data = json.loads(json_path.read_text(encoding="utf-8"))
            assert "landscape" in data
            assert "verdict" in data
            assert "n_cells" in data
            assert "n_steps" in data
            assert "presets" in data
            assert "instruments" in data
            # Landscape = 4 regles x 4 presets x 3 instruments = 48
            assert len(data["landscape"]) == 48
            # Verdict global est l'un des 3 verdis possibles
            assert data["verdict"]["global"] in (
                "DISCRIMINANT_FORT", "DISCRIMINANT_FAIBLE", "NONDISCRIMINANT_CONFIRME"
            )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
