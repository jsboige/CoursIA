"""Tests unitaires de scan_slidev_gap_report.

Le scanner Playwright reste couvert par scan_slidev_composition + son
controle positif ; ici on teste la transformation JSON -> rapport structure
avec des fixtures reproduisant la structure `results[]`.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scan_slidev_gap_report import (  # noqa: E402
    _forms_triggered,
    _severity,
    _slide_row,
    build_report,
)


SAMPLE_REPORT = {
    "canvas": [980, 552],
    "n_occupation_flagged": 2,
    "controle_positif_ok": False,
    "controle_positif_warning": "scan sans contrôle positif armé",
    "baseline_slide": 5,
    "baseline_commit": "6cabc826b",
    "results": [
        # Pas d'image
        {"slide": 1, "text_head": "Sommaire", "hors_canvas": [], "chevauchements": [], "occupation": None},
        # Cas fondateur F1 (gap_left 71.4)
        {"slide": 7, "text_head": "Image collee a droite", "hors_canvas": [], "chevauchements": [],
         "occupation": {"n_images": 1, "img_span": [700, 960], "span_ratio": 0.265,
                        "gap_left_pct": 71.4, "gap_right_pct": 2.0,
                        "center_offset_pct": 34.7, "dispersion": 0,
                        "content_bottom": 400}},
        # F2 : gap moderee + offset
        {"slide": 21, "text_head": "Deux images decenter", "hors_canvas": [], "chevauchements": [],
         "occupation": {"n_images": 2, "img_span": [300, 950], "span_ratio": 0.663,
                        "gap_left_pct": 4.9, "gap_right_pct": 64.5,
                        "center_offset_pct": -29.8, "dispersion": 0.3,
                        "content_bottom": 380}},
        # F3 : image unique offset
        {"slide": 23, "text_head": "Image plaquee", "hors_canvas": [], "chevauchements": [],
         "occupation": {"n_images": 1, "img_span": [600, 980], "span_ratio": 0.388,
                        "gap_left_pct": 61.2, "gap_right_pct": 0.0,
                        "center_offset_pct": 30.1, "dispersion": 0,
                        "content_bottom": 450}},
        # F4-overflow : gap bas + hors_canvas
        {"slide": 5, "text_head": "Trois images + overflow", "hors_canvas": [{"tag": "IMG"}],
         "chevauchements": [],
         "occupation": {"n_images": 3, "img_span": [200, 700], "span_ratio": 0.510,
                        "gap_left_pct": 30.0, "gap_right_pct": 5.0,
                        "center_offset_pct": -12.5, "dispersion": 0.2,
                        "content_bottom": 350}},
        # Composition equilibree
        {"slide": 30, "text_head": "Centre equilibre", "hors_canvas": [], "chevauchements": [],
         "occupation": {"n_images": 1, "img_span": [380, 600], "span_ratio": 0.224,
                        "gap_left_pct": 10.0, "gap_right_pct": 10.0,
                        "center_offset_pct": 0.0, "dispersion": 0,
                        "content_bottom": 300}},
        # Faible gap sans offset (low severity)
        {"slide": 40, "text_head": "Image en haut a droite", "hors_canvas": [], "chevauchements": [],
         "occupation": {"n_images": 1, "img_span": [700, 850], "span_ratio": 0.153,
                        "gap_left_pct": 26.0, "gap_right_pct": 13.0,
                        "center_offset_pct": 13.5, "dispersion": 0,
                        "content_bottom": 200}},
    ],
}


def test_severity_thresholds():
    assert _severity(71.4) == "high"
    assert _severity(55.0) == "high"
    assert _severity(54.9) == "med"
    assert _severity(40.0) == "med"
    assert _severity(39.9) == "low"
    assert _severity(25.0) == "low"
    assert _severity(24.9) == "none"
    assert _severity(0.0) == "none"


def test_forms_triggered_F1_fondateur():
    r = SAMPLE_REPORT["results"][1]  # slide 7, gap_left 71.4
    forms = _forms_triggered(r, 552)
    assert "F1" in forms


def test_forms_triggered_F2_moderee_offset():
    r = SAMPLE_REPORT["results"][2]  # slide 21, gap_right 64.5 + offset -29.8
    forms = _forms_triggered(r, 552)
    assert "F1" in forms  # gap >= 55 declenche F1 aussi
    assert "F2" in forms


def test_forms_triggered_F3_single_image():
    r = SAMPLE_REPORT["results"][3]  # slide 23, n_images=1, offset 30.1
    forms = _forms_triggered(r, 552)
    assert "F1" in forms  # gap_left 61.2 >= 55
    assert "F3" in forms


def test_forms_triggered_F4_overflow():
    r = SAMPLE_REPORT["results"][4]  # slide 5, gap 30 + hors_canvas
    forms = _forms_triggered(r, 552)
    assert "F4-overflow" in forms


def test_forms_triggered_balanced_no_forms():
    r = SAMPLE_REPORT["results"][5]  # slide 30, gap 10/10
    forms = _forms_triggered(r, 552)
    assert forms == []


def test_slide_row_drops_no_images():
    r = SAMPLE_REPORT["results"][0]  # slide 1 sans image
    assert _slide_row(r, 552) is None


def test_slide_row_severity_and_flagged():
    r = SAMPLE_REPORT["results"][1]  # slide 7
    row = _slide_row(r, 552)
    assert row is not None
    assert row["slide"] == 7
    assert row["severity"] == "high"
    assert row["gap_max"] == 71.4
    assert row["flagged_by_scanner"] is True
    assert "F1" in row["forms_triggered"]


def test_build_report_summary_and_sort():
    report = build_report(SAMPLE_REPORT)
    # Source preserved
    assert report["source_n_occupation_flagged"] == 2
    assert report["source_controle_positif_ok"] is False
    assert report["canvas_h"] == 552
    # 6 slides avec images (la slide 1 n'a pas d'image)
    assert report["n_slides_with_images"] == 6
    # Severity counts
    assert report["summary_by_severity"]["high"] == 3  # slides 7, 21, 23
    assert report["summary_by_severity"]["med"] == 0
    assert report["summary_by_severity"]["low"] == 2  # slides 5, 40
    assert report["summary_by_severity"]["none"] == 1  # slide 30
    # Sorted: high d'abord par gap_max desc
    rows = report["rows"]
    assert rows[0]["severity"] == "high"
    assert rows[0]["slide"] == 7  # 71.4
    # high contigus
    high_rows = [r for r in rows if r["severity"] == "high"]
    assert {r["slide"] for r in high_rows} == {7, 21, 23}


def test_build_report_top_limit():
    report = build_report(SAMPLE_REPORT)
    # Simule l'effet de --top
    top = report["rows"][:3]
    assert len(top) == 3
    assert all(r["severity"] == "high" for r in top)


def test_csv_field_round_trip(tmp_path):
    """Le CSV doit contenir les cles de la row (forms_triggered en ';' separated)."""
    report = build_report(SAMPLE_REPORT)
    csv_path = tmp_path / "gap.csv"
    # Inline minimal CSV write pour eviter de re-tester l'enrobage argparse.
    import csv as _csv
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = _csv.DictWriter(f, fieldnames=[
            "slide", "severity", "n_images", "gap_left_pct", "gap_right_pct",
            "gap_max", "center_offset_pct", "dispersion", "flagged_by_scanner",
            "forms_triggered", "text_head",
        ])
        w.writeheader()
        for r in report["rows"]:
            r2 = dict(r)
            r2["forms_triggered"] = ";".join(r2["forms_triggered"])
            w.writerow(r2)
    # Re-lire
    with csv_path.open(encoding="utf-8") as f:
        lines = f.readlines()
    assert lines[0].startswith("slide,severity,")
    # Slide 7 en tete (high)
    assert lines[1].startswith("7,high,")
    assert "F1" in lines[1]