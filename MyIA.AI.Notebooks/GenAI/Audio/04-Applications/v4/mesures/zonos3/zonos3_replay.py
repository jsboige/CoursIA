#!/usr/bin/env python3
"""zonos3_replay.py -- controle de rejeu (acceptance #25835 #6).

Rejoue le PREMIER morceau avec la meme graine et la meme commande que le
banc, puis compare les empreintes SHA-256 du WAV rejoue et du WAV livre.
Un rejeu bit-identique etablit que la graine fixe le rendu.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

BIN = "/home/jesse/zonos3/servers/ggml/build-cuda/zonos3-cli"
MODEL = "/mnt/d/hf-models/ZONOS3-Mini/gguf/backbone-ptq.gguf"
RUN = Path("/mnt/d/hf-models/zonos3-run")
METRICS = RUN / "zonos3-mini-a0c-metrics.json"
REPLAY = Path("/tmp/replay_chunk01.wav")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main() -> int:
    metrics = json.loads(METRICS.read_text(encoding="utf-8"))
    chunk = metrics["per_chunk"][0]
    text = chunk["text"]
    seed = metrics["seed"]
    max_frames = metrics["max_frames"]
    print(f"chunk 1 : {len(text)} car., seed={seed}, max_frames={max_frames}")
    if REPLAY.exists():
        REPLAY.unlink()
    env = dict(os.environ)
    env["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
    env["CUDA_VISIBLE_DEVICES"] = "2"
    cmd = [
        BIN, MODEL, "--gpu", "--tts", text, str(REPLAY),
        "--seed", str(seed), "--max", str(max_frames),
        "--speaker-embedding", str(RUN / "Gaspard_fr_M_1.embedding.npy"),
    ]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        print("REPLAY_FAILED", proc.stderr[-2000:], file=sys.stderr)
        return 2
    delivered = RUN / "out" / "zonos3-mini-chunk-01.wav"
    a, b = sha256(REPLAY), sha256(delivered)
    identical = a == b
    out = {
        "chunk_index": 1,
        "chars": len(text),
        "seed": seed,
        "max_frames": max_frames,
        "sha256_replay": a,
        "sha256_delivered": b,
        "bit_identical": identical,
        "note": "meme commande, meme graine, meme embedding -- WAV rejoue compare au WAV livre",
    }
    print(json.dumps(out, indent=2, ensure_ascii=False))
    (RUN / "replay-determinisme.json").write_text(
        json.dumps(out, indent=2, ensure_ascii=False), encoding="utf-8")
    return 0 if identical else 3


if __name__ == "__main__":
    sys.exit(main())
