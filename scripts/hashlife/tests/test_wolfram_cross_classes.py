"""Tests pli 4 -- cross-classes 4 regles Wolframe (I/II/III/IV).

Couvre :
- measure_wolfram_4classes : 28 mesures (4 regles × 7 fenetres)
- wolfram_class_verdict : classification par classe
- wolfram_4classes_cross_verdict : verdict final
- WOLFRAM_CLASS_MAP : constantes canoniques
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
REPO_ROOT = Path(__file__).resolve().parents[2]
K_TRAJ = HASHLIFE_DIR / "k_trajectory.py"
if str(HASHLIFE_DIR) not in sys.path:
    sys.path.insert(0, str(HASHLIFE_DIR))


class TestWolframClassMap:
    """Constantes canoniques des 4 classes Wolframe."""

    def test_class_map_has_four_entries(self):
        from k_trajectory import WOLFRAM_CLASS_MAP
        assert len(WOLFRAM_CLASS_MAP) == 4

    def test_class_map_canonical_assignments(self):
        from k_trajectory import WOLFRAM_CLASS_MAP
        assert WOLFRAM_CLASS_MAP[0] == ("I", "uniforme")
        assert WOLFRAM_CLASS_MAP[4] == ("II", "periodique")
        assert WOLFRAM_CLASS_MAP[30] == ("III", "chaotique")
        assert WOLFRAM_CLASS_MAP[110] == ("IV", "Turing-complet")


class TestMeasureWolfram4Classes:
    """Mesure cross-classes : 4 regles × 7 fenetres = 28 entrees."""

    def test_runs_returns_28_entries(self):
        from k_trajectory import measure_wolfram_4classes
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        assert len(results) == 28  # 4 * 7

    def test_includes_all_four_rules(self):
        from k_trajectory import measure_wolfram_4classes
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        rules_found = set()
        for r in results:
            try:
                rule = int(r["trajectory"].split("_R")[1].split("_")[0])
                rules_found.add(rule)
            except (IndexError, ValueError):
                pass
        assert rules_found == {0, 4, 30, 110}

    def test_rule0_is_class_I(self):
        from k_trajectory import measure_wolfram_4classes
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        # La derniere entree de Rule 0 (W=64) doit etre ~21 (cf. WOLFRAM-VERDICT-CROSS-CLASSES.md)
        r0_max = max(
            (r for r in results if "R0_" in r["trajectory"]),
            key=lambda r: r["n"],
        )
        assert r0_max["n"] == 6
        assert r0_max["W"] == 64
        # Tolerance : K_compressed_length est deterministic sur bytes, doit etre ~21
        assert r0_max["k_trajectory"] < 50, (
            f"R0 W=64 doit collapse < 50, observe {r0_max['k_trajectory']}"
        )


class TestWolframClassVerdictSaturation:
    """Sous le plancher, aucune classification n'est concluante.

    Mesure 2026-10-09 : a n_cells = 64, R30 et R110 rendent un ratio identique
    de 0.510 (K(W=1) = 1026, K(W=64) = 523 = 512 + 11) -- l'instrument ne voit
    que son propre cadrage. La version anterieure publiait CLASS-III-REFUTED /
    CLASS-IV-REFUTED / III/IV-INVERSE sur cette zone saturee.
    """

    def test_min_n_cells_floor_value(self):
        from k_trajectory import WOLFRAM_MIN_N_CELLS
        assert WOLFRAM_MIN_N_CELLS == 512

    def test_all_classes_saturated_at_n64(self):
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        assert cv, "aucun verdict rendu"
        for name, verdict in cv.items():
            assert "WOLFRAM-SATURATED" in verdict, f"{name}: {verdict}"

    def test_r30_and_r110_are_identical_at_n64(self):
        """Tell de saturation : les deux regles rendent la meme constante."""
        from k_trajectory import measure_wolfram_4classes
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        by_rule = {}
        for r in results:
            name = r["trajectory"]
            if "_R30_" not in name and "_R110_" not in name:
                continue
            rule = int(name.split("_R")[1].split("_")[0])
            cur = by_rule.get(rule)
            if cur is None or r["n"] > cur["n"]:
                by_rule[rule] = r
        assert by_rule[30]["k_trajectory"] == by_rule[110]["k_trajectory"]


class TestCommittedCanonicalMeasurement:
    """La mesure canonique committée (n=1024) porte la classification concluante."""

    @staticmethod
    def _canonical() -> dict:
        return json.loads(
            (HASHLIFE_DIR / "wolfram_cross_classes_results.json").read_text(encoding="utf-8")
        )

    def test_canonical_json_is_out_of_saturation(self):
        data = self._canonical()
        assert data["n_cells"] >= 512, "la mesure canonique doit etre hors saturation"
        for name, verdict in data["per_class_verdicts"].items():
            assert "WOLFRAM-SATURATED" not in verdict, f"{name}: {verdict}"

    def test_canonical_separates_r30_from_r110(self):
        data = self._canonical()
        cv = data["per_class_verdicts"]
        assert "CLASS-III-CONFIRMED" in cv["wolfram_R30_n1024_seed33"], cv
        assert "CLASS-IV-REFUTED" in cv["wolfram_R110_n1024_seed33"], cv
        # Deux classes contredisaient a n=64 ; une seule a n=1024.
        assert "1/4" in data["cross_classes_verdict"], data["cross_classes_verdict"]


class TestWolfram4ClassesCrossVerdict:
    """Verdict final cross-classes."""

    def test_cross_verdict_is_saturated_when_all_saturated(self):
        from k_trajectory import wolfram_4classes_cross_verdict
        cv = {
            "a": "WOLFRAM-SATURATED (n_cells=64 < 512)",
            "b": "WOLFRAM-SATURATED (n_cells=64 < 512)",
        }
        assert "WOLFRAM-4CLASSES-SATURATED" in wolfram_4classes_cross_verdict(cv)

    def test_cross_verdict_is_iii_iv_inverse_from_canonical_measurement(self):
        """A n=1024, seule R110 contredit encore -> III/IV-INVERSE a 1/4."""
        from k_trajectory import wolfram_4classes_cross_verdict
        data = json.loads(
            (HASHLIFE_DIR / "wolfram_cross_classes_results.json").read_text(encoding="utf-8")
        )
        cross = wolfram_4classes_cross_verdict(data["per_class_verdicts"])
        assert "WOLFRAM-4CLASSES-III/IV-INVERSE" in cross, cross

    def test_cross_verdict_format_is_string(self):
        from k_trajectory import wolfram_4classes_cross_verdict
        cross = wolfram_4classes_cross_verdict({})
        assert isinstance(cross, str)
        # Cas vide : INDETERMINATE
        assert "INDETERMINATE" in cross


class TestWolframCrossClassesJsonRoundtrip:
    """Round-trip JSON via subprocess."""

    def test_subprocess_json_output_has_required_keys(self):
        """Lance le mode wolfram-4classes avec --json-out, verifie les cles."""
        import os
        import tempfile
        env = os.environ.copy()
        env["PYTHONPATH"] = str(REPO_ROOT.parent / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series")
        with tempfile.TemporaryDirectory() as tmpdir:
            json_path = Path(tmpdir) / "results.json"
            proc = subprocess.run(
                [sys.executable, str(K_TRAJ), "--mode", "wolfram-4classes",
                 "--n-cells", "64", "--json-out", str(json_path)],
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
            assert "cross_classes_verdict" in data
            assert data["n_cells"] == 64
            assert "WOLFRAM-4CLASSES" in data["cross_classes_verdict"]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))