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


class TestWolframClassVerdict:
    """Verdict par regle : I/II CONFIRMED si COLLAPSED, III/IV CONFIRMED si non-COLLAPSED."""

    def test_rule0_class_I_confirmed_on_c110_measurement(self):
        """Verifie que R0 (I, uniforme) est CONFIRME avec le ratio c.110 (0.030)."""
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        r0_name = next(n for n in cv if "R0_n64" in n)
        assert "CLASS-I-CONFIRMED" in cv[r0_name]
        assert "COLLAPSED" in cv[r0_name]

    def test_rule4_class_II_confirmed_on_c110_measurement(self):
        """Verifie que R4 (II, periodique) est CONFIRME avec le ratio c.110 (0.027)."""
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        r4_name = next(n for n in cv if "R4_n64" in n)
        assert "CLASS-II-CONFIRMED" in cv[r4_name]
        assert "COLLAPSED" in cv[r4_name]

    def test_rule30_class_III_refuted_on_c110_measurement(self):
        """Verifie que R30 (III, chaotique) est REFUSE -- faux negatif sur entropie."""
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        r30_name = next(n for n in cv if "R30_n64" in n)
        assert "CLASS-III-REFUTED" in cv[r30_name], (
            f"R30 devrait etre REFUTED (COLLAPSED sur entropie partielle) -- "
            f"observe: {cv[r30_name]}"
        )

    def test_rule110_class_IV_refuted_on_c110_measurement(self):
        """Verifie que R110 (IV, Turing-complet) est REFUSE -- faux negatif sur auto-entretien."""
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        r110_name = next(n for n in cv if "R110_n64" in n)
        assert "CLASS-IV-REFUTED" in cv[r110_name]


class TestWolfram4ClassesCrossVerdict:
    """Verdict final cross-classes."""

    def test_cross_verdict_is_iii_iv_inverse(self):
        """Sur c.110, R30 et R110 sont REFUTES, R0 et R4 sont CONFIRMES -> III/IV-INVERSE."""
        from k_trajectory import measure_wolfram_4classes, wolfram_class_verdict, wolfram_4classes_cross_verdict
        results = measure_wolfram_4classes(n_cells=64, n_steps=64, seed=33)
        cv = wolfram_class_verdict(results)
        cross = wolfram_4classes_cross_verdict(cv)
        assert "WOLFRAM-4CLASSES-III/IV-INVERSE" in cross, (
            f"Verdict attendu III/IV-INVERSE, observe : {cross}"
        )

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