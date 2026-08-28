#!/usr/bin/env python3
"""clone_decisive.py — #11624 decisive experiment (ai-01 DM 2026-08-18 15:59).

Does the CLONING path reproduce the MELODY of its reference (not just the
timbre)? Route constant (Qwen3-TTS Base cloning), register constant (~110 Hz),
target text constant (the narrator A/B passage) — ONLY the reference's
prosody varies:

  witness : v4 narrator reference (monotone, DRONE-class)
  test    : G1_melodique_registre_grave (ai-01's EXPRESSIVE render at the
            SAME register, deposited in GDrive audiobook-1028-review)

  clone(G1) EXPRESSIVE -> the reference sample carries the drone; cloning
                          is saved by re-selecting/re-recording the reference.
  clone(G1) DRONE      -> the cloning path flattens whatever it gets.

Method constraints (ai-01): >= 3 draws per cell (run-to-run variance is
real); verify_prosody --single gate on EVERY output; a DRONE is never served.

Usage::

    python clone_decisive.py --ref <ref.mp3> --ref-text "<transcript of ref>" \
        --tag g1 --draws 3 [--url http://127.0.0.1:8199]
"""
from __future__ import annotations

import argparse
import base64
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import qwen_tts_client as qc  # noqa: E402
from ab_11624_voices import VOICES  # noqa: E402

LAB = Path(__file__).resolve().parent
GATE = LAB.parents[5] / "scripts" / "tts_verification" / "verify_prosody.py"
OUT_DIR = LAB.parent / "outputs" / "prosody_lab" / "11624"


def _to_data_uri(path: Path) -> str:
    return "data:audio/mp3;base64," + base64.b64encode(path.read_bytes()).decode()


def _gate(clip: Path) -> dict:
    r = subprocess.run(
        [sys.executable, str(GATE), "--single", str(clip)],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return json.loads(r.stdout)


def main() -> None:
    ap = argparse.ArgumentParser(description="Decisive cloning experiment (#11624)")
    ap.add_argument("--ref", required=True, help="reference audio (<= 10 s)")
    ap.add_argument("--ref-text", required=True, help="transcript of the reference audio")
    ap.add_argument("--tag", required=True, help="output tag (g1 / v4)")
    ap.add_argument("--draws", type=int, default=3)
    ap.add_argument("--url", default="http://127.0.0.1:8199")
    ap.add_argument("--text", default=None, help="target text (default: narrator A/B passage)")
    args = ap.parse_args()

    text = args.text or VOICES["narrateur"]["text"]
    ref = Path(args.ref)

    qc.QWEN_GATEWAY_URL = args.url
    qc.QWEN_MODEL = "Qwen/Qwen3-TTS-12Hz-1.7B-Base"
    qc._TTS_KEY = None

    rows = []
    for i in range(1, args.draws + 1):
        out = OUT_DIR / f"decisive_{args.tag}_draw{i}.mp3"
        audio = qc.qwen_tts_clone(
            text, ref_audio=_to_data_uri(ref), ref_text=args.ref_text,
        )
        if not audio:
            print(f"draw{i}: FAILED render")
            rows.append({"draw": i, "gate": "ERROR"})
            continue
        wav = out.with_suffix(".wav")
        wav.write_bytes(audio)
        subprocess.run(
            ["ffmpeg", "-y", "-loglevel", "error", "-i", str(wav), "-b:a", "128k", str(out)],
            check=True,
        )
        wav.unlink()
        g = _gate(out)
        row = {
            "draw": i,
            "gate": g["gate"],
            "reasons": g.get("reasons", []),
            "melody": g.get("melody_verdict"),
            "eff": g.get("effective_notes"),
            "top3": g.get("top3_note_pct"),
            "motifs_strict": g.get("motif3_repeat_pct"),
            "n_syll": g.get("n_syllables"),
        }
        rows.append(row)
        print(
            f"draw{i}: {row['gate']} {row['reasons']} | {row['melody']} | "
            f"eff {row['eff']} | top3 {row['top3']}% | motifs {row['motifs_strict']}%"
        )

    ok = [r for r in rows if r.get("gate") not in (None, "ERROR")]
    if ok:
        drones = sum(1 for r in ok if r["melody"] == "DRONE" or r["gate"] == "REJECT")
        print(f"\n[{args.tag}] {len(ok)} draws, {drones} DRONE/REJECT -> "
              f"{'CLONING FLATTENS' if drones > len(ok) / 2 else 'REFERENCE CARRIES' if drones == 0 else 'MIXED'}")
    summary = OUT_DIR / f"decisive_{args.tag}_summary.json"
    summary.write_text(json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"[summary] {summary}")


if __name__ == "__main__":
    main()
