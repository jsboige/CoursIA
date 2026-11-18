"""Tests pli 9 -- Seed specialise R110 (0001000) + 3 complexites (corriges).

Couvre :
- WOLFRAM_SEED_PRESETS : 4 entrees canoniques
- wolfram_seed_preset : generation d'etat initial, padding, single-cell special
- wolfram_trajectory_from_state : trajectoire 1-D via wolfram_step organ
- _traj_states_to_grid : conversion vers format grid 1xN
- Instruments portes des correctifs plis 7/8 : lz76_factor_count,
  normalized_lz76_complexity, _bits_to_str, block_complexity_distribution
- Garde d'echelle : WOLFRAM_SEED_MIN_N_CELLS = 512, verdict SATURE + refus
  --json-out sous le plancher
- Plancher absolu du verdict : WOLFRAM_SEED_ABS_DELTA_FLOOR -- un ratio
  eleve sur un delta absolu de bruit ne fait pas un DISCRIMINANT
- measure_seed_instrument_landscape : 48 mesures (4 regles x 4 presets x 3
  instruments), unites corrigees (KSF bits/cellule, blocks LZ76)
- seed_discrimination_verdict : verdict par preset x instrument + global,
- JSON round-trip : CLI via subprocess avec PYTHONPATH
- Resultats commits : wolfram_seed_test_results.json a n=512, verdicts
  conforms au document WOLFRAM-VERDICT-SEED-TEST.md

Correctif 2026-10-09 (reserve c.6078963240) : la mesure initiale a n=64
etait un artefact de saturation (fenetre packee sous le plancher de cadrage
zlib, KSF en octets vs reperes en bits/cellule, entropie de Shannon
invariante a l'arrangement pour blocks). Ces tests couvrent les gardes qui
empechent l'artefact de revenir.
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
COMMITTED_JSON = HASHLIFE_DIR / "wolfram_seed_test_results.json"
if str(HASHLIFE_DIR) not in sys.path:
    sys.path.insert(0, str(HASHLIFE_DIR))

MEASURE_KEYS = {
    "lz": "k_last_over_first",
    "ksf": "ksf_last_bits_per_cell",
    "blocks": "blocks_lz76_std_at_Wmax",
}


def _synth_row(instrument: str, preset: str, rule: int, value: float,
               n_cells: int = 512) -> dict:
    """Rangee synthetique minimale pour seed_discrimination_verdict."""
    return {
        "instrument": instrument,
        "preset": preset,
        "rule": rule,
        "n_cells": n_cells,
        MEASURE_KEYS[instrument]: value,
    }


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


class TestScaleGuards:
    """Gardes d'echelle et plancher absolu du verdict (correctif 2026-10-09)."""

    def test_min_n_cells_constant(self):
        from k_trajectory import WOLFRAM_SEED_MIN_N_CELLS
        assert WOLFRAM_SEED_MIN_N_CELLS == 512

    def test_abs_delta_floor_constant(self):
        from k_trajectory import WOLFRAM_SEED_ABS_DELTA_FLOOR
        assert WOLFRAM_SEED_ABS_DELTA_FLOOR == 0.05

    def test_verdict_saturated_below_floor(self):
        """Sous 512 cellules, toutes les cellules du verdict sont SATUREES."""
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row(instr, preset, rule, 0.5, n_cells=64)
            for instr in ("lz", "ksf", "blocks")
            for preset in ("single-cell", "wolfram-0001000")
            for rule in (30, 110)
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["global"].startswith("WOLFRAM-SEED-SATURATED")
        assert "512" in v["global"]
        assert v["discriminative_presets"] == 0
        for verdicts in v["per_instrument"].values():
            assert all(val == "SATURATED" for val in verdicts.values())

    def test_floor_kills_fabricated_discriminant(self):
        """Contre-mesure mesuree (c.6078963240) : random-dense LZ a n=512
        porte ratio 0.307 pour un delta absolu de 0.027 -- le ratio seul
        fabriquait un DISCRIMINANT sur du bruit."""
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row("lz", "random-dense", 30, 0.088),
            _synth_row("lz", "random-dense", 110, 0.061),
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["per_instrument"]["lz"]["random-dense"] == "NONDISCRIMINANT"
        # La mesure brute reste dans le verdict : falsifiable sans relancer.
        m = v["measurements"]["lz"]["random-dense"]
        assert abs(m["abs_delta"] - 0.027) < 0.001
        assert m["ratio"] > 0.20  # le ratio seul disait DISCRIMINANT

    def test_clear_delta_still_discriminant_above_floor(self):
        """Un vrai signal (delta absolu 0.414, ratio 0.55) reste DISCRIMINANT."""
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row("lz", "wolfram-0001000", 30, 0.752),
            _synth_row("lz", "wolfram-0001000", 110, 0.338),
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["per_instrument"]["lz"]["wolfram-0001000"] == "DISCRIMINANT"

    def test_weak_band_between_floor_and_ratio_threshold(self):
        """Delta absolu >= plancher mais ratio <= 0.20 : WEAK-DISCRIMINANT."""
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row("lz", "p", 30, 1.000),
            _synth_row("lz", "p", 110, 0.850),
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["per_instrument"]["lz"]["p"] == "WEAK-DISCRIMINANT"

    def test_zero_pair_is_nondiscriminant_with_measurements(self):
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row("ksf", "p", 30, 0.0),
            _synth_row("ksf", "p", 110, 0.0),
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["per_instrument"]["ksf"]["p"] == "NONDISCRIMINANT"

    def test_global_aggregation_full_discriminant(self):
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row(instr, preset, 30, 0.90)
            for instr in ("lz", "ksf", "blocks")
            for preset in ("p1", "p2")
        ] + [
            _synth_row(instr, preset, 110, 0.10)
            for instr in ("lz", "ksf", "blocks")
            for preset in ("p1", "p2")
        ]
        # v30=0.90, v110=0.10 partout : 6/6 DISCRIMINANT
        v = seed_discrimination_verdict(landscape)
        assert v["global"] == "DISCRIMINANT_FORT"
        assert v["discriminative_presets"] == 6

    def test_missing_rule_pair_is_incomplete(self):
        from k_trajectory import seed_discrimination_verdict
        landscape = [
            _synth_row("lz", "p", 30, 0.9),
            # pas de R110
        ]
        v = seed_discrimination_verdict(landscape)
        assert v["per_instrument"]["lz"]["p"] == "INCOMPLETE"

    def test_empty_landscape(self):
        from k_trajectory import seed_discrimination_verdict
        v = seed_discrimination_verdict([])
        assert v["global"] == "EMPTY"
        assert v["discriminative_presets"] == 0


class TestPortedLZ76Instruments:
    """Fonctions portees du correctif pli 8 (recopies byte-identiques)."""

    def test_lz76_factor_count_periodic_few_factors(self):
        from k_trajectory import lz76_factor_count
        # '0101'*32 : periodique, se factorise en tres peu de phrases
        assert lz76_factor_count("01" * 64) < 10

    def test_lz76_factor_count_random_many_factors(self):
        from k_trajectory import lz76_factor_count
        # pseudo-aleatoire deterministe : beaucoup de phrases
        import random
        rng = random.Random(7)
        s = "".join(rng.choice("01") for _ in range(1024))
        assert lz76_factor_count(s) > 100

    def test_normalized_lz76_periodic_near_zero(self):
        from k_trajectory import normalized_lz76_complexity
        assert normalized_lz76_complexity("01" * 512) < 0.05

    def test_normalized_lz76_random_near_one(self):
        from k_trajectory import normalized_lz76_complexity
        import random
        rng = random.Random(42)
        s = "".join(rng.choice("01") for _ in range(4096))
        # l'estimateur vaut ~1.0 sur une chaine aleatoire (peut depasser
        # legerement sur les chaines courtes -- propriete connue)
        assert 0.9 < normalized_lz76_complexity(s) < 1.1

    def test_bits_to_str(self):
        from k_trajectory import _bits_to_str
        assert _bits_to_str([0, 1, 1, 0]) == "0110"
        assert _bits_to_str([]) == ""

    def test_shannon_invariant_vs_lz76_arrangement_sensitive(self):
        """Le temoin negatif du pli 8 : H ne voit pas l'arrangement, LZ76 oui."""
        from k_trajectory import normalized_lz76_complexity, shannon_entropy_bits
        periodic = [0, 1] * 512
        rng = __import__("random").Random(3)
        shuffled = [0, 1] * 512
        rng.shuffle(shuffled)
        # meme nombre de 1 -> meme entropie
        assert abs(shannon_entropy_bits(periodic) - shannon_entropy_bits(shuffled)) < 1e-9
        # LZ76 les separe largement
        assert normalized_lz76_complexity("".join(map(str, periodic))) < 0.1
        assert normalized_lz76_complexity("".join(map(str, shuffled))) > 0.9

    def test_block_complexity_distribution_shape(self):
        from k_trajectory import block_complexity_distribution
        # 8 etats identiques periodiques ; bloc de 8 etats x 16 cellules
        # = 128 bits parfaitement periodiques -> peu de facteurs LZ76.
        traj = [[0, 1, 0, 1] * 4] * 8
        dist = block_complexity_distribution(traj, 8)
        assert dist["n_blocks"] == 1
        assert dist["mean"] < 0.2  # periodique -> peu complexe
        assert dist["std"] == 0.0  # un seul bloc

    def test_block_complexity_distribution_empty(self):
        from k_trajectory import block_complexity_distribution
        dist = block_complexity_distribution([[0, 1]], 4)
        assert dist["n_blocks"] == 0
        assert dist["mean"] == 0.0


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
        expected = ("0001000" * 10)[:64]
        assert "".join(str(c) for c in state) == expected

    def test_wolfram_0001000_truncation(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("wolfram-0001000", 32)
        assert len(state) == 32
        expected = ("0001000" * 5)[:32]
        assert "".join(str(c) for c in state) == expected

    def test_wolfram_defect_pattern(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("wolfram-defect", 64)
        assert len(state) == 64
        src = ("0001000" * 8)[:63] + "1"  # 64 chars
        out_str = ""
        while len(out_str) < 64:
            out_str += src
        assert "".join(str(c) for c in state) == out_str[:64]

    def test_random_dense_pattern(self):
        from k_trajectory import wolfram_seed_preset
        state = wolfram_seed_preset("random-dense", 64)
        assert len(state) == 64
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
        assert traj[0] == state

    def test_rule30_single_cell_chaotic(self):
        """Rule 30 single-cell : trajectoire non triviale apres quelques pas."""
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 64)
        traj = wolfram_trajectory_from_state(state, rule=30, n_steps=20)
        n_ones_step_0 = sum(traj[0])
        n_ones_step_1 = sum(traj[1])
        assert n_ones_step_0 == 1
        assert n_ones_step_1 != 1

    def test_rule0_constant(self):
        """Rule 0 (toujours 0) : trajectoire constante a zero."""
        from k_trajectory import wolfram_seed_preset, wolfram_trajectory_from_state
        state = wolfram_seed_preset("single-cell", 32)
        traj = wolfram_trajectory_from_state(state, rule=0, n_steps=10)
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
        packed = grid_to_packed(grid[0])
        assert len(packed) == 1
        assert packed == b"\xff"


class TestMeasureSeedInstrumentLandscape:
    """Mesure 3 complexites corrigees sur le paysage de seeds (echelle
    diagnostique n=16 : le verdict est SATURE, la structure des rangees
    reste verifiable)."""

    def test_landscape_size(self):
        """4 regles x 4 presets x 3 instruments = 48 mesures."""
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
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

    def test_landscape_ksf_has_corrected_units(self):
        """Port pli 7 : KSF en bits/cellule, pas seulement en octets."""
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        ksf_rows = [r for r in landscape if r["instrument"] == "ksf"]
        for r in ksf_rows:
            assert "ksf_W" in r  # octets (trace)
            assert "ksf_W_bits_per_cell" in r  # unite corrigee
            assert "ksf_last_bits_per_cell" in r  # valeur de verdict
            # coherence : bits/cellule = octets * 8 / n_cells
            for w, bits in r["ksf_W_bits_per_cell"].items():
                octets = r["ksf_W"][w]
                assert abs(bits - octets * 8.0 / r["n_cells"]) < 0.01

    def test_landscape_blocks_uses_lz76(self):
        """Port pli 8 : la statistique de blocks est la complexite LZ76
        normalisee (sensible a l'arrangement), l'entropie reste en trace."""
        from k_trajectory import measure_seed_instrument_landscape
        landscape = measure_seed_instrument_landscape(n_cells=16, n_steps=16)
        blocks_rows = [r for r in landscape if r["instrument"] == "blocks"]
        for r in blocks_rows:
            assert "blocks_W" in r
            assert "blocks_lz76_mean_at_Wmax" in r
            assert "blocks_lz76_std_at_Wmax" in r
            for b in r["blocks_W"]:
                assert "entropy_mean" in b  # trace pli 8
                assert "complexity_mean" in b  # statistique de verdict
                assert "complexity_std" in b


class TestCommittedResultsJson:
    """Le JSON committe (regenere 2026-10-09) doit porter la mesure
    canonique n=512 et les verdicts publies par le document -- ce sont les
    claims falsifiables du pli 9 corrige."""

    @pytest.fixture(scope="class")
    def committed(self) -> dict:
        assert COMMITTED_JSON.exists(), (
            "wolfram_seed_test_results.json doit etre committe avec la PR"
        )
        return json.loads(COMMITTED_JSON.read_text(encoding="utf-8"))

    def test_canonical_scale(self, committed):
        """La mesure canonique est hors zone de saturation (garde #19826)."""
        assert committed["n_cells"] == 512
        assert committed["n_steps"] == 512

    def test_landscape_complete(self, committed):
        assert len(committed["landscape"]) == 48

    def test_verdict_refuted_both_directions(self, committed):
        """Le resultat attendu, mesure (reserve c.6078963240) : la
        discrimination de seed est refuted dans les deux sens a n=512 --
        wolfram-0001000 passe NONDISCRIMINANT -> DISCRIMINANT, random-dense
        passe DISCRIMINANT -> NONDISCRIMINANT."""
        per = committed["verdict"]["per_instrument"]
        for instr in ("lz", "ksf", "blocks"):
            assert per[instr]["wolfram-0001000"] == "DISCRIMINANT", (
                f"{instr}/wolfram-0001000 : le document publie DISCRIMINANT"
            )
            assert per[instr]["random-dense"] == "NONDISCRIMINANT", (
                f"{instr}/random-dense : le controle doit etre nondiscriminant "
                f"a n=512 (l'ancien DISCRIMINANT x3 etait un artefact d'echelle)"
            )

    def test_floor_governs_random_dense(self, committed):
        """random-dense LZ porte ratio 0.305 (> 0.20) pour abs 0.027 : sans
        le plancher absolu, le verdict serait un DISCRIMINANT fabrique."""
        m = committed["verdict"]["measurements"]["lz"]["random-dense"]
        assert m["ratio"] > 0.20
        assert m["abs_delta"] < 0.05
        assert committed["verdict"]["per_instrument"]["lz"]["random-dense"] == (
            "NONDISCRIMINANT"
        )

    def test_global_verdict(self, committed):
        assert committed["verdict"]["global"] == "DISCRIMINANT_FAIBLE"
        assert committed["verdict"]["discriminative_presets"] == 9
        assert committed["verdict"]["total_presets"] == 12

    def test_measurements_present_for_every_cell(self, committed):
        """Chaque cellule du verdict porte ses valeurs brutes : le verdict
        est falsifiable sans relancer la mesure."""
        m = committed["verdict"]["measurements"]
        for instr in ("lz", "ksf", "blocks"):
            assert set(m[instr]) == {
                "single-cell", "wolfram-0001000", "wolfram-defect", "random-dense"
            }
            for cell in m[instr].values():
                for k in ("v30", "v110", "abs_delta", "ratio"):
                    assert k in cell


class TestWolframSeedTestCli:
    """CLI : garde d'echelle sur --json-out, verdict SATURE affiche."""

    def _run(self, *extra: str) -> subprocess.CompletedProcess:
        env = os.environ.copy()
        env["PYTHONPATH"] = str(REPO_ROOT / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series")
        return subprocess.run(
            [sys.executable, str(K_TRAJ), "--mode", "wolfram-seed-test",
             "--n-cells", "16", "--n-steps", "16", *extra],
            env=env, capture_output=True, text=True, timeout=300,
        )

    def test_small_run_without_json_is_saturated_not_error(self):
        proc = self._run()
        assert proc.returncode == 0, f"stderr: {proc.stderr}"
        assert "WOLFRAM-SEED-SATURATED" in proc.stdout

    def test_json_out_refused_below_floor(self):
        """--json-out refuse sous WOLFRAM_SEED_MIN_N_CELLS : on ne publie
        pas un artefact de saturation."""
        with tempfile.TemporaryDirectory() as tmpdir:
            json_path = Path(tmpdir) / "should_not_exist.json"
            proc = self._run("--json-out", str(json_path))
            assert proc.returncode == 1
            assert not json_path.exists()
            assert "refuse" in proc.stdout


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
