#!/usr/bin/env python3
"""Telecharge les poids ZONOS3-Mini a la revision epinglee.

Les poids ne sont jamais committes ni embarques dans l'image : ce script les
pose dans un repertoire hote que le service monte en lecture seule.

Usage :
    python fetch_models.py --dest D:\\hf-models\\zonos3
    python fetch_models.py --dest ./models --with raw-reference

Le jeu par defaut suffit au service (backbone PTQ, decodeur keep2, encodeur de
locuteur, bundle de steering, voix livrees). Les compagnons optionnels sont
nommes par ce qu'ils ouvrent :
    raw-reference : zac-encoder + ssl-teacher, pour le clonage depuis un clip
                    brut (et ffmpeg dans l'image) ;
    edit          : gguf/edit/accents.gguf, pour l'edition de parole (hors
                    perimetre de la tranche 3 de #25835).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ID = "Zyphra/ZONOS3-Mini"
#: Revision HF epinglee (main du 2026-11-17T19:41:37Z). Change la valeur ici et
#: nulle part ailleurs : le README et le commentaire de service la citent.
REVISION = "2921b8821772b0bd10a04456863d21abf9d2f283"

REQUIRED = [
    "gguf/backbone-ptq.gguf",
    "gguf/zac-keep2.gguf",
    "gguf/spk-encoder.gguf",
    "gguf/steer.gguf",
]
VOICES = "gguf/voices/*"
OPTIONAL = {
    "raw-reference": ["gguf/zac-encoder.gguf", "gguf/ssl-teacher.gguf"],
    "edit": ["gguf/edit/accents.gguf"],
}


def main() -> int:
    parser = argparse.ArgumentParser(description="Poids ZONOS3-Mini (revision epinglee)")
    parser.add_argument("--dest", required=True, type=Path,
                        help="repertoire hote des poids (monte par le service)")
    parser.add_argument("--with", dest="extras", action="append", default=[],
                        choices=sorted(OPTIONAL), help="compagnons optionnels")
    args = parser.parse_args()

    patterns = REQUIRED + [VOICES]
    for name in args.extras:
        patterns += OPTIONAL[name]

    from huggingface_hub import snapshot_download

    path = snapshot_download(
        repo_id=REPO_ID,
        revision=REVISION,
        allow_patterns=patterns,
        local_dir=str(args.dest),
    )
    print(f"snapshot {REPO_ID}@{REVISION} -> {path}")

    missing = [p for p in REQUIRED if not (args.dest / p).is_file()]
    if missing:
        print("fichiers requis absents : " + ", ".join(missing), file=sys.stderr)
        return 1

    total = sum(f.stat().st_size for f in (args.dest / "gguf").rglob("*") if f.is_file())
    print(f"{len(REQUIRED)} fichiers requis presents, gguf/ = {total / 1e9:.2f} Go")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
