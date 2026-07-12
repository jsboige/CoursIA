#!/usr/bin/env python3
"""Multi-engine A/B/C/D/E test for #1877 prosody comparison.

Generates clips of the same Boule de Suif passage using different TTS engines,
then measures prosody (ST-spread, CV, velocity) per engine.

Engines:
  A = FishAudio F5 (baseline, cloned voice, port 8197)
  B = Kokoro TTS (native voice, port 8191)
  C = Chatterbox TTS (native voice, port TBD — skip if unavailable)
  D = Qwen TTS (via gateway, port 8196)
  E = Higgs Audio v3 (sglang-omni, port 8199)

Usage:
    cd v4/prosody_lab/
    python ab_engine_test.py

Output:
    outputs/prosody_lab/ab_engine_*.mp3   — one clip per engine
    outputs/prosody_lab/ab_engine_metrics.json  — prosody measurements
"""
from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from fishaudio_client import fishaudio_tts

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

TEST_TEXT_FILE = Path(__file__).resolve().parent / "test_segment.txt"
OUTPUT_DIR = Path(__file__).resolve().parent.parent / "outputs" / "prosody_lab"
OUTPUT_DIR.mkdir(exist_ok=True, parents=True)

# FishAudio config
FISH_REF = "prosody_expr_voicedesign"  # expressive clone reference
FISH_PORT = 8197

# Kokoro config
KOKORO_PORT = 8191
KOKORO_KEY = os.getenv("KOKORO_API_KEY", "")
KOKORO_VOICE = "af_bella"

# Qwen TTS config (via gateway)
QWEN_PORT = 8196
QWEN_VOICE = "Chelsie"

# Chatterbox config (skip if not running)
CHATTERBOX_PORT = 8198
CHATTERBOX_VOICE = "Emily.wav"

# Higgs Audio v3 config (sglang-omni, skip if not running)
HIGGS_PORT = 8199

# FishAudio temperature/seed
TEMPERATURE = 0.8
SEED = 42

OUT_METRICS = OUTPUT_DIR / "ab_engine_metrics.json"


# ---------------------------------------------------------------------------
# Engine callers
# ---------------------------------------------------------------------------

def call_fishaudio(text: str) -> bytes | None:
    """Call FishAudio F5 TTS (port 8197)."""
    print("  [FishAudio F5] Calling...")
    t0 = time.time()
    audio = fishaudio_tts(
        text=text,
        reference_id=FISH_REF,
        temperature=TEMPERATURE,
        seed=SEED,
        format="mp3",
        timeout=300,
    )
    dt = time.time() - t0
    if audio:
        print(f"  [FishAudio F5] OK: {len(audio)/1024:.0f} KB in {dt:.1f}s")
    else:
        print("  [FishAudio F5] FAILED")
    return audio


def call_kokoro(text: str) -> bytes | None:
    """Call Kokoro TTS (port 8191, OpenAI-compat)."""
    import requests
    print("  [Kokoro] Calling...")
    try:
        t0 = time.time()
        resp = requests.post(
            f"http://localhost:{KOKORO_PORT}/v1/audio/speech",
            headers={
                "Content-Type": "application/json",
                "Authorization": f"Bearer {KOKORO_KEY}",
            },
            json={
                "model": "kokoro",
                "input": text,
                "voice": KOKORO_VOICE,
            },
            timeout=120,
        )
        dt = time.time() - t0
        if resp.status_code == 200:
            audio = resp.content
            print(f"  [Kokoro] OK: {len(audio)/1024:.0f} KB in {dt:.1f}s")
            return audio
        else:
            print(f"  [Kokoro] FAILED: HTTP {resp.status_code} — {resp.text[:200]}")
            return None
    except Exception as e:
        print(f"  [Kokoro] ERROR: {e}")
        return None


def call_qwen(text: str) -> bytes | None:
    """Call Qwen TTS via gateway (port 8196)."""
    import requests
    print("  [Qwen TTS] Calling...")
    try:
        t0 = time.time()
        resp = requests.post(
            f"http://localhost:{QWEN_PORT}/qwen/v1/audio/speech",
            headers={"Content-Type": "application/json"},
            json={
                "model": "qwen3",
                "input": text,
                "voice": QWEN_VOICE,
            },
            timeout=120,
        )
        dt = time.time() - t0
        if resp.status_code == 200:
            audio = resp.content
            print(f"  [Qwen TTS] OK: {len(audio)/1024:.0f} KB in {dt:.1f}s")
            return audio
        else:
            print(f"  [Qwen TTS] FAILED: HTTP {resp.status_code} — {resp.text[:200]}")
            return None
    except Exception as e:
        print(f"  [Qwen TTS] ERROR: {e}")
        return None


def call_chatterbox(text: str) -> bytes | None:
    """Call Chatterbox TTS (OpenAI-compat, port 8000 or as configured)."""
    import requests
    print("  [Chatterbox] Calling...")
    try:
        t0 = time.time()
        # Chatterbox TTS Server uses OpenAI-compatible API
        resp = requests.post(
            f"http://localhost:{CHATTERBOX_PORT}/v1/audio/speech",
            headers={"Content-Type": "application/json"},
            json={
                "model": "chatterbox",
                "input": text,
                "voice": CHATTERBOX_VOICE,
            },
            timeout=120,
        )
        dt = time.time() - t0
        if resp.status_code == 200:
            audio = resp.content
            print(f"  [Chatterbox] OK: {len(audio)/1024:.0f} KB in {dt:.1f}s")
            return audio
        else:
            print(f"  [Chatterbox] FAILED: HTTP {resp.status_code} — {resp.text[:200]}")
            return None
    except Exception as e:
        print(f"  [Chatterbox] SKIP (not available): {e}")
        return None


def call_higgs(text: str) -> bytes | None:
    """Call Higgs Audio v3 TTS (sglang-omni, OpenAI-compat, port 8199)."""
    import requests
    print("  [Higgs v3] Calling...")
    try:
        t0 = time.time()
        resp = requests.post(
            f"http://localhost:{HIGGS_PORT}/v1/audio/speech",
            headers={"Content-Type": "application/json"},
            json={"input": text},
            timeout=120,
        )
        dt = time.time() - t0
        if resp.status_code == 200:
            audio = resp.content
            print(f"  [Higgs v3] OK: {len(audio)/1024:.0f} KB in {dt:.1f}s")
            return audio
        else:
            print(f"  [Higgs v3] FAILED: HTTP {resp.status_code} — {resp.text[:200]}")
            return None
    except Exception as e:
        print(f"  [Higgs v3] SKIP (not available): {e}")
        return None


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------

def measure_prosody(audio_path: Path) -> dict | None:
    """Run prosody_metrics on a single clip."""
    try:
        from prosody_metrics import compute_metrics
        m = compute_metrics(str(audio_path))
        return {
            "file": audio_path.name,
            "st_range": round(m.get("f0_semitone_range", 0), 2),
            "f0_mean": round(m.get("f0_mean_hz", 0), 1),
            "f0_cv": round(m.get("f0_cv", 0), 3),
            "velocity": round(m.get("intonation_velocity_st_per_s", 0), 2),
            "voiced_frac": round(m.get("voiced_fraction", 0), 3),
            "duration_s": round(m.get("duration_s", 0), 2),
        }
    except Exception as e:
        print(f"  [Metrics] ERROR on {audio_path.name}: {e}")
        return None


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    # Load test text
    text = TEST_TEXT_FILE.read_text(encoding="utf-8").strip()
    print(f"Text ({len(text)} chars): {text[:80]}...")
    print()

    engines = [
        ("A", "FishAudio F5", "ab_engine_A_fish.mp3", call_fishaudio),
        ("B", "Kokoro", "ab_engine_B_kokoro.mp3", call_kokoro),
        ("C", "Chatterbox", "ab_engine_C_chatterbox.mp3", call_chatterbox),
        ("D", "Qwen TTS", "ab_engine_D_qwen.mp3", call_qwen),
        ("E", "Higgs Audio v3", "ab_engine_E_higgs.mp3", call_higgs),
    ]

    results = []
    metrics_all = []

    for label, name, filename, caller in engines:
        print(f"[{label}] {name}")
        audio = caller(text)
        if audio:
            out_path = OUTPUT_DIR / filename
            out_path.write_bytes(audio)
            print(f"  -> {out_path}")
            results.append({"label": label, "engine": name, "file": filename, "size_kb": len(audio) / 1024})
        else:
            print(f"  -> SKIPPED (engine unavailable)")
            results.append({"label": label, "engine": name, "file": None, "error": "unavailable"})
        print()

    # Measure prosody on all generated clips
    print("=" * 60)
    print("PROSODY MEASUREMENTS")
    print("=" * 60)
    for r in results:
        if r["file"]:
            audio_path = OUTPUT_DIR / r["file"]
            m = measure_prosody(audio_path)
            if m:
                metrics_all.append(m)
                print(f"  [{r['label']}] {r['engine']:20s} | ST={m['st_range']:5.2f} | CV={m['f0_cv']:.3f} | vel={m['velocity']:5.2f} st/s | dur={m['duration_s']:.1f}s")
            else:
                print(f"  [{r['label']}] {r['engine']:20s} | METRICS FAILED")
        else:
            print(f"  [{r['label']}] {r['engine']:20s} | NO CLIP")

    # Save
    report = {
        "test": "multi_engine_ab_prosody",
        "issue": 1877,
        "text_length": len(text),
        "results": results,
        "metrics": metrics_all,
    }
    OUT_METRICS.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"\nMetrics saved: {OUT_METRICS}")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY — ST-spread ranking (higher = more expressive)")
    print("=" * 60)
    ranked = sorted(metrics_all, key=lambda x: x["st_range"], reverse=True)
    for i, m in enumerate(ranked):
        label = next((r["label"] for r in results if r["file"] == m["file"]), "?")
        name = next((r["engine"] for r in results if r["file"] == m["file"]), "?")
        print(f"  {i+1}. [{label}] {name:20s} — ST={m['st_range']:.2f}, CV={m['f0_cv']:.3f}")


if __name__ == "__main__":
    main()
