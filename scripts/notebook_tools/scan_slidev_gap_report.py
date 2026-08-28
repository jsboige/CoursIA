#!/usr/bin/env python3
"""scan_slidev_gap_report.py — tableau par-slide des desequilibres de composition.

Consomme le JSON produit par `scan_slidev_composition.py` et genere :

  1. Un **rapport JSON structure** (sortie par defaut stdout) avec par slide :
     - `slide` (1-based),
     - `n_images`,
     - `gap_left_pct`, `gap_right_pct`, `center_offset_pct`,
     - `gap_max` (le pire des deux cotes),
     - `severity` ("none" / "low" / "med" / "high"),
     - `forms_triggered` (liste des formes F1-F4 qui flaggent la slide),
     - `head` (60 premiers chars de innerText).

  2. Un **CSV** trie par `gap_max` decroissant (sortie --csv) avec une
     ligne par slide portant des images. Utile pour ouvrir dans un tableur
     et **piloter les tranches** du chantier composition (cf issue #13224).

Origine : #13223 a re-cable `occupation_flagged` sur 4 formes F1-F4, mais le
JSON de sortie reste un rollup (n_occupation_flagged: 2 sur 42 cas reels a
gap >= 40 %). Pour **piloter** la descente des 42 slides signalee par #13224
(par tranches, mesure avant/apres datee), il faut un **tableau par slide**.
C'est ce que ce script produit, sans rien toucher au scanner Playwright.

Usage :
    # 1. Lancer le scanner (dans un autre terminal) :
    python scripts/notebook_tools/run_composition_control.py
    # ... produit report.json dans tmp/slidev_control_xxx/

    # 2. Produire le rapport structure :
    python scripts/notebook_tools/scan_slidev_gap_report.py \\
        --in  tmp/slidev_control_xxxx/report.json \\
        --out tmp/gap_report.json

    # 3. CSV pour tableur :
    python scripts/notebook_tools/scan_slidev_gap_report.py \\
        --in tmp/.../report.json --csv tmp/gap_report.csv

Seuil de severity (calibre sur l'acceptance #13223 / #13224) :
  - "high" : gap_max >= 55          (forme F1 du scanner)
  - "med"  : gap_max >= 40          (F2 si offset cumule, sinon candidate)
  - "low"  : gap_max >= 25          (F4 si saturation verticale)
  - "none" : pas d'image ou gap < 25

Bornes identiques au scanner c.572 (#13225). Tout seuil alternatif se
justifie par ecrit dans le body de la PR consommatrice.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCANNER_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCANNER_DIR))

# Note : on importe scan_slidev_composition uniquement pour acceder aux
# memes seuils (canvas, canvas_h). Le verdict flagged_by_scanner est
# derive localement par _would_flag -- indifferent a la version du
# scanner (origin/main pre-merge #13225 vs c.572 post-merge).


SEVERITY_THRESHOLDS = (55, 40, 25)


def _severity(gap_max: float) -> str:
    if gap_max >= SEVERITY_THRESHOLDS[0]:
        return "high"
    if gap_max >= SEVERITY_THRESHOLDS[1]:
        return "med"
    if gap_max >= SEVERITY_THRESHOLDS[2]:
        return "low"
    return "none"


def _forms_triggered(slide_record: dict, canvas_h: int) -> list[str]:
    """Re-derive locally les formes F1-F4 (independamment de l'agregat)."""
    occ = slide_record.get("occupation")
    if not occ:
        return []
    out = []
    gap_left = occ.get("gap_left_pct", 0)
    gap_right = occ.get("gap_right_pct", 0)
    offset = abs(occ.get("center_offset_pct", 0))
    n_images = occ.get("n_images", 0)
    # F1
    if gap_left >= 55 or gap_right >= 55:
        out.append("F1")
    # F2
    if (gap_left >= 40 or gap_right >= 40) and offset >= 25:
        out.append("F2")
    # F3
    if n_images == 1 and offset >= 30:
        out.append("F3")
    # F4 (legere duplication avec occupation_flagged : on garde la trace)
    if (gap_left > 25 or gap_right > 25) and slide_record.get("hors_canvas"):
        out.append("F4-overflow")
    elif (gap_left > 25 or gap_right > 25) and occ.get("content_bottom", 0) > canvas_h * 0.95:
        out.append("F4-bord")
    return out


def _would_flag(slide_record: dict, canvas_h: int) -> bool:
    """Verdict 'would flag' selon les 4 formes F1-F4.

    Re-derive locale de la logique F1-F4 (cf occupation_flagged c.572).
    Independant du module occupation_flagged importé pour deux raisons :
    - le scanner origin/main peut ne pas encore porter F1-F4 (pre-merge #13225) ;
    - le tableau doit predire la composition APRES merge du scanner c.572.
    Toute slide qu'on signale ici sera signalee par le scanner post-merge.
    """
    return len(_forms_triggered(slide_record, canvas_h)) > 0


def _slide_row(slide_record: dict, canvas_h: int) -> dict | None:
    occ = slide_record.get("occupation")
    if not occ:
        return None  # pas d'image sur cette slide
    gap_left = occ.get("gap_left_pct", 0)
    gap_right = occ.get("gap_right_pct", 0)
    gap_max = max(gap_left, gap_right)
    flagged = _would_flag(slide_record, canvas_h)
    return {
        "slide": slide_record["slide"],
        "text_head": (slide_record.get("text_head") or "?")[:60],
        "n_images": occ.get("n_images", 0),
        "gap_left_pct": gap_left,
        "gap_right_pct": gap_right,
        "gap_max": gap_max,
        "center_offset_pct": occ.get("center_offset_pct", 0),
        "dispersion": occ.get("dispersion", 0),
        "severity": _severity(gap_max),
        "forms_triggered": _forms_triggered(slide_record, canvas_h),
        "flagged_by_scanner": flagged,
    }


def build_report(scanner_report: dict) -> dict:
    canvas_h = scanner_report.get("canvas", [980, 552])[1]
    rows = []
    for r in scanner_report.get("results", []):
        row = _slide_row(r, canvas_h)
        if row is not None:
            rows.append(row)
    # Tri par severity (high -> med -> low -> none) puis gap_max desc
    severity_rank = {"high": 0, "med": 1, "low": 2, "none": 3}
    rows.sort(key=lambda x: (severity_rank[x["severity"]], -x["gap_max"]))
    n = len(rows)
    n_high = sum(1 for r in rows if r["severity"] == "high")
    n_med = sum(1 for r in rows if r["severity"] == "med")
    n_low = sum(1 for r in rows if r["severity"] == "low")
    n_flagged = sum(1 for r in rows if r["flagged_by_scanner"])
    return {
        "source_n_occupation_flagged": scanner_report.get("n_occupation_flagged"),
        "source_controle_positif_ok": scanner_report.get("controle_positif_ok"),
        "source_controle_positif_warning": scanner_report.get("controle_positif_warning"),
        "source_baseline_slide": scanner_report.get("baseline_slide"),
        "source_baseline_commit": scanner_report.get("baseline_commit"),
        "canvas_h": canvas_h,
        "n_slides_with_images": n,
        "summary_by_severity": {
            "high": n_high,
            "med": n_med,
            "low": n_low,
            "none": n - n_high - n_med - n_low,
        },
        "n_flagged_by_scanner": n_flagged,
        "rows": rows,
    }


def write_csv(report: dict, csv_path: Path) -> None:
    rows = report["rows"]
    fieldnames = [
        "slide", "severity", "n_images", "gap_left_pct", "gap_right_pct",
        "gap_max", "center_offset_pct", "dispersion", "flagged_by_scanner",
        "forms_triggered", "text_head",
    ]
    with csv_path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            r2 = dict(r)
            r2["forms_triggered"] = ";".join(r2["forms_triggered"])
            w.writerow(r2)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--in", dest="input", type=Path, required=True,
                    help="JSON produit par scan_slidev_composition.py")
    ap.add_argument("--out", type=Path, default=None,
                    help="Rapport JSON structure (defaut : stdout)")
    ap.add_argument("--csv", type=Path, default=None,
                    help="CSV par slide, tri severity desc / gap_max desc")
    ap.add_argument("--top", type=int, default=0,
                    help="Limiter la sortie aux N premieres lignes (0 = toutes)")
    args = ap.parse_args()

    scanner_report = json.loads(args.input.read_text(encoding="utf-8"))
    report = build_report(scanner_report)
    if args.top > 0:
        report = dict(report)
        report["rows"] = report["rows"][: args.top]

    out_str = json.dumps(report, ensure_ascii=False, indent=2)
    if args.out:
        args.out.write_text(out_str, encoding="utf-8")
    print(out_str)

    if args.csv:
        write_csv(report, args.csv)


if __name__ == "__main__":
    main()