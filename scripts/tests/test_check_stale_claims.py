"""Tests de l'organe stale-claim (#18354 tranche 1).

Cas canoniques mesures sur App-4b-JobShopScheduling-CSharp (≈ 12 vs
optimum committé 11) et App-3-NurseScheduling (> 80% sans output local),
plus les gardes FP calibrees sur la mesure du 29/09 (31 -> 19 findings
sur 30 carnets sains).
"""

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_stale_claims.py"


def _nb(cells):
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _md(src):
    return {"cell_type": "markdown", "metadata": {}, "source": src}


def _code(out_text):
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": {},
        "outputs": [
            {"output_type": "stream", "name": "stdout", "text": out_text}
        ],
        "source": "print(1)",
    }


def _run(cells, tmp_path):
    p = tmp_path / "fixture.ipynb"
    p.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    return r.returncode, json.loads(r.stdout)


INTERP = "### Interprétation : preuve d'optimalité\n"


def test_canonical_stale_approx(tmp_path):
    # App-4b : « ft03 ≈ 12 » affirme, l'output committé dit 11
    rc, out = _run(
        [_code("Meilleure heuristique : MOR (makespan=11)\nMakespan = 11\n"),
         _md(INTERP + "les règles atteignent ft03 ≈ 12 ; CP-SAT prouve 11. Sur ft06 (6×6), pareil.")],
        tmp_path,
    )
    assert rc == 1
    claims = [f["claimed"] for f in out["findings"]]
    assert "12" in claims and "11" not in claims


def test_canonical_stale_threshold_table(tmp_path):
    # App-3 : « | Taux préférences | > 80% | » sans output local
    rc, out = _run(
        [_code("Charge par infirmier: 7 7 8 7 7 8 7 8 7 7 8 7 7 8 7\n"),
         _md("### Interpretation : qualite du planning\n| Taux préférences | > 80% | Bonne satisfaction |\n")],
        tmp_path,
    )
    assert rc == 1
    assert any(f["claimed"] == "80" for f in out["findings"])


def test_present_in_outputs_not_flagged(tmp_path):
    rc, out = _run(
        [_code("makespan optimal = 11\n"),
         _md(INTERP + "le moteur atteint ≈ 11 comme prouvé.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_decimal_dot_comma_symmetric(tmp_path):
    # Nit (a) review NanoClaw : un claim « 12.5 » face a un output
    # francais « 12,5 » (ou l'inverse) doit apparier, pas donner un FP.
    rc, out = _run(
        [_code("score final : 12,5\n"),
         _md(INTERP + "le score converge vers ≈ 12.5 sur cette instance.")],
        tmp_path,
    )
    assert rc == 0 and out["anomaly_count"] == 0


def test_non_interpretation_cell_ignored(tmp_path):
    rc, out = _run(
        [_code("makespan = 11\n"),
         _md("## 6. Complémentarité avec le jumeau (#3801)\natteint ≈ 12 sans preuve.")],
        tmp_path,
    )
    assert rc == 0


def test_stat_constants_guarded(tmp_path):
    rc, out = _run(
        [_code("Shapiro p=0.23\n"),
         _md(INTERP + "- **Seuil** : p > 0.05 → accepter H0\n- |r| < 0.3 : faible corrélation\n- α = 0.01 (99%)\n")],
        tmp_path,
    )
    assert rc == 0


def test_year_version_duration_guards(tmp_path):
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "En 2026, la v3.10 tourne en ~5 min et ~12 s ; ratio 6×6.\nde l'ordre de ~3300 tokens")],
        tmp_path,
    )
    assert rc == 0


def test_code_span_and_link_guarded(tmp_path):
    rc, out = _run(
        [_code("done\n"),
         _md(INTERP + "Le paramètre `≈ 42` et [voir ≈ 99](https://x.y/a?n=77) ne comptent pas.")],
        tmp_path,
    )
    assert rc == 0


def test_unreadable_notebook_reports_error(tmp_path):
    p = tmp_path / "broken.ipynb"
    p.write_text("{not json", encoding="utf-8")
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--json", str(p)],
        capture_output=True, text=True, encoding="utf-8",
    )
    assert r.returncode == 1
    out = json.loads(r.stdout)
    assert out["findings"] and "error" in out["findings"][0]
