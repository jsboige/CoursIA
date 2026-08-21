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


def _run_demo(*extra_args: str) -> dict:
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), *extra_args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, f"demo exited {proc.returncode}: {proc.stderr}"
    return json.loads(proc.stdout)


def _make_drifted_csv() -> Path:
    """Copie finetuning.csv en falsifiant src_hash sur 2 lignes traduites.

    Les litmus drift vivaient sur la dette REELLE du corpus (78 lignes FT-02
    derivees, cf #10282/#10287). L'amorcage T1 plein perimetre de #10329
    (etape 2) a resynchronise tous les src_hash : src_drift_total est passe a
    0 sur le CSV live, et la fixture a disparu avec la dette. Un CSV derive,
    falsifie de maniere deterministe, restitue la demonstration sans dependre
    de l'etat d'endettement du corpus.

    Le CSV derive vit sous REPO_ROOT (le demo exige un chemin relative_to la
    racine) ; l'appelant DOIT le supprimer en finally.
    """
    import csv as _csv
    import os

    src = REPO_ROOT / "translations" / "genai" / "finetuning.csv"
    dst = REPO_ROOT / f".tmp_finetuning_drifted_{os.getpid()}.csv"
    with open(src, encoding="utf-8", newline="") as f:
        rows = list(_csv.DictReader(f))
    # 2 lignes markdown avec text_fr ET text_en remplis : le drift doit etre
    # detecte ET qualifie "drift_with_filled_text_en" (le pivot #10287).
    targets = [r for r in rows if r["text_fr"] and r["text_en"]][:2]
    assert len(targets) == 2, "fixture needs 2 translated rows"
    tampered_ids = {id(r) for r in targets}
    for r in rows:
        if id(r) in tampered_ids:
            r["src_hash"] = "deadbeef" + r["src_hash"][8:]
            r["hash_fr"] = r["src_hash"]
    with open(dst, "w", encoding="utf-8", newline="") as f:
        w = _csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    return dst


def test_couture_active():
    """Le gate TRANSLATE_ENABLED est cable et le plan T3 est parseable."""
    report = _run_demo()
    assert report["verdict"]["couture_active"] is True
    assert report["t3_plan"]["translations_planned"] >= 0
    summary = " ".join(report["t3_plan"]["stderr_summary"])
    assert "[GATED]" in summary or "TRANSLATE_ENABLED" in summary


def test_drift_count_is_consistent():
    """Le nombre de cellules en SRC_DRIFT est rapporte de maniere coherente.

    Fixture synthetique (voir _make_drifted_csv) : le drift est garanti par
    falsification de 2 lignes, pas par la dette reelle du corpus.

    L'assertion porte sur le DELTA que la falsification introduit, jamais sur
    les totaux absolus. La version d'origine comparait
    ``drift_with_filled_text_en == src_drift_in_csv``, ce qui n'est vrai que si
    le corpus live porte zero dette -- l'etat du jour ou #10329 etape 2 l'a
    resynchronise, et d'aucun autre : la moindre re-execution d'un notebook
    FineTuning fait rederiver des ``src_hash`` et casse l'egalite. Mesure du
    2026-08-20 sur ``main`` : ``finetuning.csv`` reporte 3 lignes en drift dont
    1 seule avec ``text_en`` rempli, d'ou ``assert 3 == 5``.

    Le meme piege avait ete vu et desamorce dans ``test_t3_captures_drift_now``
    (#11934, commentaire « l'egalite stricte ne tenait que sur l'ancien corpus
    endette ») ; il est reste entier dans ce test-ci.
    """
    base = _run_demo("--csv", str(Path("translations") / "genai" / "finetuning.csv"))["drift"]
    drifted_csv = _make_drifted_csv()
    try:
        report = _run_demo("--csv", str(drifted_csv))
    finally:
        drifted_csv.unlink(missing_ok=True)
    drift = report["drift"]
    assert drift["src_drift_total"] > 0
    # src_drift_in_csv <= src_drift_total (toutes les cellules sont dans le CSV test)
    assert drift["src_drift_in_csv"] <= drift["src_drift_total"]
    # Les 2 lignes falsifiees ont text_fr ET text_en remplis : chacune ajoute
    # +1 a src_drift_in_csv ET +1 a drift_with_filled_text_en (pivot #10287 --
    # un drift dont la traduction est deja remplie doit etre detecte quand
    # meme). La dette preexistante s'annule dans la difference, donc le test
    # mesure la propriete voulue et rien d'autre.
    #
    # Controle negatif (2026-08-20) : en portant la fixture de 2 a 3 lignes
    # falsifiees, ce test echoue en « assert (6 - 3) == 2 ». Il mord.
    assert drift["src_drift_in_csv"] - base["src_drift_in_csv"] == 2
    assert drift["drift_with_filled_text_en"] - base["drift_with_filled_text_en"] == 2


def test_t3_captures_drift_now():
    """Pivot #10287 : la lacune documentée par #10282 est fermée — T3 détecte
    maintenant le SRC_DRIFT même quand text_<lang> est rempli. Critère #10287
    critère 4 : la démo doit basculer de verdict (t3_detects_drift=False → True).

    Avant #10287 : plan_count=0, drift_with_filled_text_en=78 → t3_detects_drift=False.
    Après #10287 : plan_count=78, drift_with_filled_text_en=78 → t3_detects_drift=True.

    Fixture synthetique depuis #10329 etape 2 (dette live payee) : le drift
    est garanti par falsification, l'assertion devient inconditionnelle.
    """
    drifted_csv = _make_drifted_csv()
    try:
        report = _run_demo("--csv", str(drifted_csv))
    finally:
        drifted_csv.unlink(missing_ok=True)
    # Le plan couvre toutes les cellules drifted (sur la langue `en` du test).
    # Sur un CSV fraichement amorce (#10329 etape 2), le plan inclut AUSSI les
    # nouvelles lignes jamais traduites (text_en vide) : l'egalite stricte
    # plan == drift_with_filled ne tenait que sur l'ancien corpus endette.
    assert report["drift"]["drift_with_filled_text_en"] > 0
    assert report["t3_plan"]["translations_planned"] >= report["drift"]["drift_with_filled_text_en"]
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