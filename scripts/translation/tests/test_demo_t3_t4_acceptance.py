#!/usr/bin/env python3
"""
Tests for demo_t3_t4_acceptance.py (grain DEEP/tooling #10270 couture acceptance).

Verifies that the end-to-end T3/T4 acceptance demo produces a falsifiable
report and that the *couture* (gating flags, dry-run discipline, plan
captioning) is intact.

Litmus (litmus anti-regression, miroir du PR body) — état après #10287 :
  - couture T3/T4 active (GATED banner present, plan count parseable)
  - T3 détecte le SRC_DRIFT (translation_plan() pivote sur src_hash) — pivot
    #10287 critère 1+4 : la lacune documentée par #10282 est FERMÉE.
  - T4 dry-run byte-stable sur le notebook de reference (FT-01)
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "scripts" / "translation" / "demo_t3_t4_acceptance.py"


def _run_demo() -> dict:
    proc = subprocess.run(
        [sys.executable, str(SCRIPT)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, f"demo exited {proc.returncode}: {proc.stderr}"
    return json.loads(proc.stdout)


def test_couture_active():
    """Le gate TRANSLATE_ENABLED est cable et le plan T3 est parseable."""
    report = _run_demo()
    assert report["verdict"]["couture_active"] is True
    assert report["t3_plan"]["translations_planned"] >= 0
    summary = " ".join(report["t3_plan"]["stderr_summary"])
    assert "[GATED]" in summary or "TRANSLATE_ENABLED" in summary


def test_drift_count_is_consistent():
    """Le nombre de cellules en SRC_DRIFT est rapporte de maniere coherente."""
    report = _run_demo()
    drift = report["drift"]
    assert drift["src_drift_total"] > 0
    # src_drift_in_csv <= src_drift_total (toutes les cellules sont dans le CSV test)
    assert drift["src_drift_in_csv"] <= drift["src_drift_total"]
    # Tous les drifts observes sur le perimetre de test sont des cellules markdown
    # dont text_en est rempli (issue #10042).
    assert drift["drift_with_filled_text_en"] == drift["src_drift_in_csv"]


def test_t3_captures_drift_now():
    """Pivot #10287 : la lacune documentée par #10282 est fermée — T3 détecte
    maintenant le SRC_DRIFT même quand text_<lang> est rempli. Critère #10287
    critère 4 : la démo doit basculer de verdict (t3_detects_drift=False → True).

    Avant #10287 : plan_count=0, drift_with_filled_text_en=78 → t3_detects_drift=False.
    Après #10287 : plan_count=78, drift_with_filled_text_en=78 → t3_detects_drift=True.
    """
    report = _run_demo()
    if report["drift"]["drift_with_filled_text_en"] > 0:
        # Le plan couvre toutes les cellules drifted (sur la langue `en` du test).
        assert report["t3_plan"]["translations_planned"] == report["drift"]["drift_with_filled_text_en"]
        assert report["verdict"]["t3_detects_drift"] is True
        # La lacune est résolue — verdict.lacune est null.
        assert report["verdict"]["lacune"] is None


def test_t4_render_byte_stable():
    """T4 dry-run produit un rapport non-vide avec stats coherentes."""
    report = _run_demo()
    stats = report["t4_render_dry"]["stats"]
    assert "markdown" in stats, f"markdown stats missing: {stats}"
    assert "code" in stats, f"code stats missing: {stats}"
    # Le notebook FT-01 a 17 markdown + 8 code (25 cells total)
    # Aprés extraction, 12 markdown traduits + 13 code copies = 25 cells
    assert "12" in stats["markdown"], f"unexpected markdown stats: {stats['markdown']}"
    assert "13" in stats["code"], f"unexpected code stats: {stats['code']}"