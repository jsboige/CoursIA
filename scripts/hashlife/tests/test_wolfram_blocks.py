"""Tests pli 8 -- Block decomposition (Zenil 2013) Rule 30 / Rule 110.

Couvre :
- WOLFRAM_BLOCK_LANDMARKS : 4 entrees recalibrees pour l'instrument corrige
- shannon_entropy_bits : entropie Shannon base 2 (invariante a l'arrangement)
- lz76_factor_count / normalized_lz76_complexity : complexite par bloc
- block_decompose_trajectory : decomposition non-chevauchante
- block_complexity_distribution : statistiques agregees (statistique du verdict)
- measure_wolfram_blocks : 24 mesures (4 regles x 6 longueurs)
- wolfram_blocks_verdict : verdict par regle vs landmark
- wolfram_blocks_discrimination_verdict : verdict discrimination R30 vs R110
- garde UNDERPOWERED : sous 4 blocs, aucune dispersion n'est mesurable
- JSON round-trip : resultats via subprocess

Correction du 2026-10-09 : la version initiale agregeait l'entropie de Shannon
par bloc, qui est invariante a l'arrangement et ne pouvait donc pas separer une
trajectoire periodique d'une trajectoire chaotique equilibree. La statistique
du verdict est desormais la complexite LZ76 normalisee par bloc.
"""

from __future__ import annotations

import json
import os
import random
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

# Echelle canonique du pli 8 : sous 256, W=32 ne laisse que 2 blocs et le
# verdict rend UNDERPOWERED.
CANONICAL_N = 256


@pytest.fixture(scope="module")
def canonical_results():
    """Mesure canonique (n=256, seed=33), calculee une seule fois."""
    from k_trajectory import measure_wolfram_blocks
    return measure_wolfram_blocks(
        n_cells=CANONICAL_N, n_steps=CANONICAL_N, seed=33
    )


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
        # La dispersion separe III de IV : R30 homogene, R110 heterogene.
        assert WOLFRAM_BLOCK_LANDMARKS[30][3] < WOLFRAM_BLOCK_LANDMARKS[110][3]

    def test_r30_mean_is_maximal(self):
        """R30 (chaos) est le plus incompressible : moyenne la plus haute."""
        from k_trajectory import WOLFRAM_BLOCK_LANDMARKS
        means = {r: WOLFRAM_BLOCK_LANDMARKS[r][2] for r in (0, 4, 30, 110)}
        assert max(means, key=means.get) == 30


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


class TestShannonEntropyIsArrangementInvariant:
    """Temoin negatif : l'entropie de Shannon ne voit pas l'arrangement.

    C'est ce defaut qui rendait le verdict initial NONDISCRIMINANT par
    construction -- une trajectoire periodique equilibree et une trajectoire
    chaotique equilibree y sont indiscernables.
    """

    def test_periodic_and_disordered_are_indistinguishable(self):
        from k_trajectory import shannon_entropy_bits
        periodic = [0, 1] * 32                       # 0101...01, parfaitement regulier
        disordered = [1, 0, 1, 1, 0, 0, 1, 0] * 8    # 32 ones / 64, desordonne
        assert shannon_entropy_bits(periodic) == shannon_entropy_bits(disordered)

    def test_both_reach_maximum(self):
        from k_trajectory import shannon_entropy_bits
        assert abs(shannon_entropy_bits([0, 1] * 32) - 1.0) < 1e-9


class TestLz76Complexity:
    """Complexite LZ76 -- arrangement-sensible, sans plancher de cadrage."""

    def test_factor_count_on_known_periodic_string(self):
        from k_trajectory import lz76_factor_count
        # '0101010101' se factorise en '0' | '1' | '01010101' -> 3 phrases
        assert lz76_factor_count("0101010101") == 3

    def test_factor_count_on_constant_string(self):
        from k_trajectory import lz76_factor_count
        # '0'*64 -> '0' | '0'*63 -> 2 phrases
        assert lz76_factor_count("0" * 64) == 2

    def test_empty_and_single(self):
        from k_trajectory import lz76_factor_count
        assert lz76_factor_count("") == 0
        assert lz76_factor_count("1") == 1

    def test_normalized_random_exceeds_periodic(self):
        from k_trajectory import normalized_lz76_complexity
        rng = random.Random(3)
        rnd = "".join(rng.choice("01") for _ in range(1024))
        periodic = "01" * 512
        assert normalized_lz76_complexity(rnd) > normalized_lz76_complexity(periodic)
        # Un tirage equilibre approche 1.0 ; une periode courte tend vers 0.
        assert 0.8 < normalized_lz76_complexity(rnd) < 1.3
        assert normalized_lz76_complexity(periodic) < 0.1

    def test_short_strings_are_defined(self):
        from k_trajectory import normalized_lz76_complexity
        assert normalized_lz76_complexity("") == 0.0
        assert normalized_lz76_complexity("1") == 0.0


class TestBitsToStr:
    """`_bits_to_str` : le piege liste/sous-chaine qui a egare le prototype."""

    def test_conversion(self):
        from k_trajectory import _bits_to_str
        assert _bits_to_str([1, 0, 1]) == "101"
        assert _bits_to_str([0, 0, 0]) == "000"

    def test_substring_search_requires_a_string(self):
        """Sur une liste, `in` teste un ELEMENT et non une sous-sequence."""
        from k_trajectory import _bits_to_str, lz76_factor_count
        bits = [0, 1, 0, 1, 0, 1, 0, 1]
        # La forme str rend le comptage attendu...
        assert lz76_factor_count(_bits_to_str(bits)) == 3
        # ...la ou la recherche sur une liste rendrait toujours faux.
        assert [0, 1] not in [[0], [1], [0], [1]]


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


class TestBlockComplexityDistribution:
    """Distribution de complexite LZ76 par bloc (statistique du verdict)."""

    def test_uniform_trajectory_zero_std(self):
        from k_trajectory import block_complexity_distribution
        # Tous les etats identiques -> tous les blocs identiques -> std 0
        traj = [[0, 0, 0, 0]] * 16
        dist = block_complexity_distribution(traj, 4)
        assert dist["n_blocks"] == 4
        assert dist["std"] == 0.0
        assert dist["min"] == dist["max"]

    def test_periodic_scores_below_disordered(self):
        """La statistique corrigee distingue ce que Shannon confondait."""
        from k_trajectory import block_complexity_distribution
        periodic = [[0, 1, 0, 1, 0, 1, 0, 1]] * 32
        rng = random.Random(5)
        disordered = [
            [rng.randint(0, 1) for _ in range(8)] for _ in range(32)
        ]
        d_per = block_complexity_distribution(periodic, 8)
        d_dis = block_complexity_distribution(disordered, 8)
        assert d_per["mean"] < d_dis["mean"]

    def test_empty_blocks_return_zeros(self):
        from k_trajectory import block_complexity_distribution
        dist = block_complexity_distribution([], 4)
        assert dist["n_blocks"] == 0
        assert dist["mean"] == 0.0


class TestMeasureWolframBlocks:
    """Mesure 4 classes x 6 longueurs = 24 entrees."""

    def test_runs_returns_24_entries(self, canonical_results):
        assert len(canonical_results) == 24  # 4 * 6

    def test_includes_all_four_rules(self, canonical_results):
        assert {r["rule"] for r in canonical_results} == {0, 4, 30, 110}

    def test_each_entry_carries_both_statistics(self, canonical_results):
        for r in canonical_results:
            for key in ("entropy_mean", "entropy_std",
                        "complexity_mean", "complexity_std", "n_blocks"):
                assert key in r, f"cle manquante {key}"

    def test_r0_complexity_is_low(self, canonical_results):
        for r in [x for x in canonical_results if x["rule"] == 0]:
            assert r["complexity_mean"] < 0.10, (
                f"R0 W={r['block_length']} devrait avoir mean<0.10, "
                f"observe {r['complexity_mean']}"
            )

    def test_r30_homogeneous_r110_dispersed_at_large_block(
        self, canonical_results
    ):
        """Le coeur du resultat corrige : R30 homogene, R110 disperse."""
        r30 = next(r for r in canonical_results
                   if r["rule"] == 30 and r["block_length"] == 32)
        r110 = next(r for r in canonical_results
                    if r["rule"] == 110 and r["block_length"] == 32)
        assert r30["complexity_mean"] > r110["complexity_mean"]
        assert r30["complexity_std"] < r110["complexity_std"]
        assert r110["complexity_std"] - r30["complexity_std"] >= 0.05


class TestBlocksUnderpoweredGuard:
    """Sous 4 blocs, aucune dispersion n'est mesurable.

    Mesure 2026-10-09 : a n_steps=64 et W=32 il n'y a que 2 blocs -- c'est la
    zone ou la version initiale publiait un verdict de non-discrimination.
    """

    def test_min_blocks_constant(self):
        from k_trajectory import WOLFRAM_BLOCKS_MIN_N_BLOCKS
        assert WOLFRAM_BLOCKS_MIN_N_BLOCKS == 4

    def test_n64_is_underpowered(self):
        from k_trajectory import (
            measure_wolfram_blocks,
            wolfram_blocks_verdict,
            wolfram_blocks_discrimination_verdict,
        )
        results = measure_wolfram_blocks(n_cells=64, n_steps=64, seed=33)
        verdicts = wolfram_blocks_verdict(results)
        for name, verdict in verdicts.items():
            assert "UNDERPOWERED" in verdict, f"{name}: {verdict}"
        final = wolfram_blocks_discrimination_verdict(verdicts, results)
        assert "UNDERPOWERED" in final


class TestCommittedCanonicalMeasurement:
    """La mesure canonique committe (n=256) porte le verdict discriminant."""

    @staticmethod
    def _canonical() -> dict:
        return json.loads(
            (HASHLIFE_DIR / "wolfram_blocks_results.json").read_text(
                encoding="utf-8"
            )
        )

    def test_canonical_is_at_measurable_scale(self):
        data = self._canonical()
        assert data["n_cells"] >= CANONICAL_N
        assert data["n_steps"] >= CANONICAL_N

    def test_canonical_is_discriminant(self):
        data = self._canonical()
        assert "WOLFRAM-BLOCKS-DISCRIMINANT" in data["discrimination_verdict"], (
            data["discrimination_verdict"]
        )

    def test_canonical_confirms_all_four_classes(self):
        data = self._canonical()
        for name, verdict in data["per_class_verdicts"].items():
            assert "CONFIRMED" in verdict, f"{name}: {verdict}"
            assert "UNDERPOWERED" not in verdict, f"{name}: {verdict}"


class TestWolframBlocksDiscriminationVerdict:
    """Verdict final de discrimination R30 vs R110."""

    def test_discrimination_verdict_format(self):
        """Cas INDETERMINATE si pas de R30 ou R110."""
        from k_trajectory import wolfram_blocks_discrimination_verdict
        final = wolfram_blocks_discrimination_verdict({}, [])
        assert "INDETERMINATE" in final

    def test_discrimination_verdict_is_decisive_at_canonical_scale(
        self, canonical_results
    ):
        from k_trajectory import (
            wolfram_blocks_verdict,
            wolfram_blocks_discrimination_verdict,
        )
        verdicts = wolfram_blocks_verdict(canonical_results)
        final = wolfram_blocks_discrimination_verdict(verdicts, canonical_results)
        assert "WOLFRAM-BLOCKS-DISCRIMINANT" in final, final


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
                 "--n-cells", str(CANONICAL_N), "--n-steps", str(CANONICAL_N),
                 "--json-out", str(json_path)],
                env=env,
                capture_output=True,
                text=True,
                timeout=600,
            )
            assert proc.returncode == 0, f"stderr: {proc.stderr}"
            assert json_path.exists()
            data = json.loads(json_path.read_text(encoding="utf-8"))
            assert "results" in data
            assert "per_class_verdicts" in data
            assert "discrimination_verdict" in data
            assert "blocks_landmarks" in data
            assert data["n_cells"] == CANONICAL_N
            assert data["n_steps"] == CANONICAL_N
            assert "WOLFRAM-BLOCKS-" in data["discrimination_verdict"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
