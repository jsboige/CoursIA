#!/usr/bin/env python3
"""Contrôle positif du garde-fou composition slides (#11923).

Matérialise le deck S3-acculturation au commit fondateur 6cabc826b (git
archive → temp), le sert via slidev dev (node_modules du dépôt, junction),
lance scan_slidev_composition.py avec --baseline-slide 5 et exige que la
slide 5 — trois images en flux au centre, tiers droit vide, débordement bas
— SOIT signalée. Un contrôle qui rend 0 constat = instrument cassé : exit 2,
jamais « RAS ».

Usage :
    python scripts/notebook_tools/run_composition_control.py [--port 8768]

Sortie : exit 0 (contrôle PASSÉ — la baseline est signalée) /
         2 (contrôle ÉCHOUÉ — instrument suspect, à ne pas merger).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
import urllib.request
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SCANNER = REPO / "scripts" / "notebook_tools" / "scan_slidev_composition.py"
BASELINE_COMMIT = "6cabc826b"
BASELINE_SLIDE = 5
ARCHIVE_PATHS = ["slides/S3-acculturation", "slides/theme-ia101", "slides/package.json", "slides/package-lock.json"]


def http_ready(url: str, timeout_s: int = 120) -> bool:
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        try:
            with urllib.request.urlopen(url, timeout=2) as resp:
                return resp.status == 200
        except Exception:
            time.sleep(2)
    return False


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8768)
    ap.add_argument("--keep", action="store_true", help="conserver le fixture (debug)")
    args = ap.parse_args()

    tmp = Path(tempfile.mkdtemp(prefix="slidev_control_"))
    # git archive du commit fondateur (objets locaux : aucun réseau)
    archive = tmp / "deck.tar"
    with open(archive, "wb") as f:
        subprocess.run(
            ["git", "-C", str(REPO), "archive", BASELINE_COMMIT] + ARCHIVE_PATHS,
            stdout=f, check=True,
        )
    subprocess.run(["tar", "-xf", str(archive), "-C", str(tmp)], check=True)
    deck = tmp / "slides" / "S3-acculturation"

    if not (deck / "slides.md").exists():
        print(f"CONTROL FAIL: fixture incomplet ({deck}/slides.md absent)")
        return 2

    # node_modules partagé du dépôt (junction Windows / lien symbolique POSIX)
    nm_target = tmp / "slides" / "node_modules"
    if not nm_target.exists():
        try:
            subprocess.run(
                ["cmd", "/c", "mklink", "/J", str(nm_target), str(REPO / "slides" / "node_modules")],
                check=True, capture_output=True,
            )
        except Exception:
            try:
                nm_target.symlink_to(REPO / "slides" / "node_modules", target_is_directory=True)
            except Exception as e:
                print(f"CONTROL FAIL: node_modules injoignable ({e})")
                return 2

    # slidev dev cherche dev.md ; copie éphémère
    (deck / "dev.md").write_bytes((deck / "slides.md").read_bytes())

    env = dict(os.environ)
    log = open(tmp / "slidev.log", "w", encoding="utf-8", errors="replace")
    slidev_bin = REPO / "slides" / "node_modules" / ".bin" / ("slidev.cmd" if os.name == "nt" else "slidev")
    serve = subprocess.Popen(
        [str(slidev_bin), "dev.md", "--port", str(args.port), "--open", "false"],
        cwd=str(deck), env=env, stdout=log, stderr=subprocess.STDOUT,
    )

    report_path = tmp / "report.json"
    try:
        if not http_ready(f"http://localhost:{args.port}/"):
            print(f"CONTROL FAIL: serveur slidev jamais prêt (log: {tmp / 'slidev.log'})")
            return 2
        r = subprocess.run(
            [sys.executable, str(SCANNER),
             "--url", f"http://localhost:{args.port}/",
             "--slides-md", str(deck / "slides.md"),
             "--baseline-slide", str(BASELINE_SLIDE),
             "--baseline-commit", BASELINE_COMMIT,
             "--out", str(report_path)],
            capture_output=True, text=True, timeout=600,
        )
        exit_code = r.returncode
        try:
            rep = json.loads(report_path.read_text(encoding="utf-8"))
        except Exception:
            rep = {}
        n_slides = rep.get("n_slides")
        ctrl_ok = rep.get("controle_positif_ok")
        s5 = next((x for x in rep.get("results", []) if x.get("slide") == BASELINE_SLIDE), None)
        print(f"fixture: {n_slides} slides | scanner exit={exit_code} | controle_positif_ok={ctrl_ok}")
        if s5:
            print(f"slide 5: head={str(s5.get('text_head'))[:50]!r} hors={len(s5.get('hors_canvas', []))} "
                  f"chev={len(s5.get('chevauchements', []))} occ={s5.get('occupation')}")
        if ctrl_ok is True and s5 is not None:
            print(f"CONTROL PASS: baseline slide {BASELINE_SLIDE} signalée comme attendu")
            return 0
        print(f"CONTROL FAIL: baseline slide {BASELINE_SLIDE} NON signalée — instrument suspect "
              f"(commit {BASELINE_COMMIT})")
        return 2
    finally:
        serve.terminate()
        try:
            serve.wait(timeout=10)
        except Exception:
            serve.kill()
        log.close()
        if args.keep:
            print(f"fixture conservé: {tmp}")


if __name__ == "__main__":
    sys.exit(main())
