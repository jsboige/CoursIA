#!/usr/bin/env python3
"""zonos3_silence.py -- densite de silence des deux rendus (comparaison).

Mesure, sur le rendu ZONOS3-Mini et sur le rendu de reference Zonos v0.1 :
duree totale, duree silencieuse (sous -45 dBFS, runs >= 0,3 s), nombre de
pauses, et debit de lecture (caracteres par seconde de signal).
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import soundfile as sf

THRESH_DB = -45.0
MIN_RUN_S = 0.3
SR = 44100

CASES = [
    ("ZONOS3-Mini (cette mesure)", "/mnt/d/hf-models/zonos3-run/out/A0C-zonos3-mini-chunked.wav", 1642),
    ("Zonos v0.1 (reference)", "/mnt/d/hf-models/zonos3-run/ref-A0C-zonos-chunked.wav", 1642),
]


def measure(path: str, chars: int) -> dict:
    audio, sr = sf.read(path, dtype="float32", always_2d=True)
    mono = audio.mean(axis=1)
    if sr != SR:
        raise SystemExit(f"echantillonnage inattendu : {sr}")
    frame = int(0.01 * sr)
    n = len(mono) // frame
    frames = mono[: n * frame].reshape(n, frame)
    rms = np.sqrt((frames ** 2).mean(axis=1))
    db = 20 * np.log10(np.maximum(rms, 1e-12))
    silent = db < THRESH_DB
    runs = 0
    silent_s = 0.0
    idx = 0
    while idx < n:
        if silent[idx]:
            j = idx
            while j < n and silent[j]:
                j += 1
            length = (j - idx) * 0.01
            if length >= MIN_RUN_S:
                runs += 1
                silent_s += length
            idx = j
        else:
            idx += 1
    voiced_s = n * 0.01 - silent_s
    return {
        "path": path,
        "duration_s": round(len(mono) / sr, 3),
        "silent_s": round(silent_s, 3),
        "silent_pct": round(100 * silent_s / (n * 0.01), 2),
        "n_silent_runs": runs,
        "voiced_s": round(voiced_s, 3),
        "chars_per_voiced_s": round(chars / voiced_s, 2) if voiced_s else None,
        "chars_per_total_s": round(chars / (len(mono) / sr), 2),
    }


def main() -> int:
    results = []
    for label, path, chars in CASES:
        if not Path(path).exists():
            print(f"{label} : FICHIER ABSENT {path}")
            continue
        out = measure(path, chars)
        out["label"] = label
        results.append(out)
        print(out)
    if "--out" in sys.argv:
        target = Path(sys.argv[sys.argv.index("--out") + 1])
        import json
        payload = {
            "instrument": "zonos3_silence.py -- densite de silence (seuil -45 dBFS, runs >= 0,3 s)",
            "sample_rate": SR,
            "threshold_dbfs": THRESH_DB,
            "min_run_s": MIN_RUN_S,
            "chars": 1642,
            "runs": results,
        }
        target.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"ecrit : {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
