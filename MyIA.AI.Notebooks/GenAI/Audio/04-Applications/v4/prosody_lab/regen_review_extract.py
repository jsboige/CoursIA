#!/usr/bin/env python3
"""regen_review_extract.py — #11624: regenerate the served review extract.

Renders the opening narrator passage of Boule de Suif (the 2:30 extract
served since May, 401 syllables, currently REJECT/MONOTONE) through the
route that won the #11624 A/B, gates it, and stages it for review ONLY if
it passes (no DRONE).

Usage::

    python regen_review_extract.py --route vd|clone [--instructions <text>]
                                   [--ref-audio <file>] [--ref-text <text>]
                                   [--url http://127.0.0.1:8199]
                                   [--text-file <path>]
                                   [--out-dir <dir>] [--stage-dir <dir>]

Default text = the first ~4 narrator segments of the v4 segmentation
(455 syllables / 1663 chars, verbatim public-domain Maupassant).
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

HERE = Path(__file__).resolve().parent
DEFAULT_TEXT_FILE = HERE.parent.parent / "outputs" / "segments_v4.json"
DEFAULT_OUT = HERE.parent / "outputs" / "prosody_lab" / "11624"


def _extract_opening_text(n_segs: int = 4) -> str:
    segs = json.loads(
        (DEFAULT_TEXT_FILE if DEFAULT_TEXT_FILE.exists() else Path(DEFAULT_TEXT_FILE)).read_text(encoding="utf-8")
    )["segments"]
    texts = []
    for s in segs:
        if s.get("speaker") != "narrateur" or not s.get("text"):
            continue
        texts.append(s["text"])
        if len(texts) >= n_segs:
            break
    return " ".join(texts)


def _to_data_uri(path: Path) -> str:
    raw = path.read_bytes()
    return "data:audio/mp3;base64," + base64.b64encode(raw).decode()


def main() -> None:
    ap = argparse.ArgumentParser(description="Regenerate the review extract (#11624)")
    ap.add_argument("--route", choices=["vd", "clone"], required=True)
    ap.add_argument("--instructions", default=None, help="VoiceDesign instructions (route=vd)")
    ap.add_argument("--ref-audio", default=None, help="clone reference audio file (route=clone)")
    ap.add_argument("--ref-text", default=None, help="clone reference transcript (route=clone)")
    ap.add_argument("--url", default="http://127.0.0.1:8199")
    ap.add_argument("--text-file", default=None, help="override the extract text file")
    ap.add_argument("--out-dir", default=str(DEFAULT_OUT))
    args = ap.parse_args()

    text = _extract_opening_text()
    if args.text_file:
        text = Path(args.text_file).read_text(encoding="utf-8").strip()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / "extrait_ouverture_regen.mp3"

    qc.QWEN_GATEWAY_URL = args.url
    qc._TTS_KEY = None  # vLLM-Omni direct has no auth middleware

    if args.route == "vd":
        qc.QWEN_MODEL = "Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign"
        audio = qc.qwen_tts_voicedesign_chunked(text, instructions=args.instructions or "")
    else:
        qc.QWEN_MODEL = "Qwen/Qwen3-TTS-12Hz-1.7B-Base"
        if not args.ref_audio:
            print("FAILED: --ref-audio required for route=clone")
            sys.exit(1)
        audio = qc.qwen_tts_clone(
            text,
            ref_audio=_to_data_uri(Path(args.ref_audio)),
            ref_text=args.ref_text or "",
        )
    if not audio:
        print("FAILED render")
        sys.exit(1)

    wav = out.with_suffix(".wav")
    wav.write_bytes(audio)
    subprocess.run(
        ["ffmpeg", "-y", "-loglevel", "error", "-i", str(wav), "-b:a", "128k", str(out)],
        check=True,
    )
    wav.unlink()
    print(f"OK {out} ({out.stat().st_size // 1024} KB)")

    # Gate the regenerated extract; refuse to serve unless it passes.
    gate_script = HERE.parents[5] / "scripts" / "tts_verification" / "verify_prosody.py"
    r = subprocess.run(
        [sys.executable, str(gate_script), "--single", str(out), "--json", str(out_dir / "gate_extrait.json")],
        capture_output=True,
        text=True,
    )
    print(r.stdout[-2000:])
    gate_json = out_dir / "gate_extrait.json"
    if gate_json.exists():
        g = json.loads(gate_json.read_text(encoding="utf-8"))
        verdict = g.get("gate") or g.get("results", [{}])[0].get("gate", "?")
        print(f"\n[gate] {verdict}")
        if verdict in ("REJECT", "ERROR"):
            print("[serve] REFUSED — extract does not pass the gate")
            sys.exit(2)
        print("[serve] extract OK to stage for review")


if __name__ == "__main__":
    main()
