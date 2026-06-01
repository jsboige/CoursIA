#!/usr/bin/env python3
"""Test TTS + WER for tags-only P4 output on segments 0-20.

Generates MP3s using FishAudio S2-Pro with official tags only,
then validates via Whisper STT and computes WER against reference.
"""
import json
import os
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dotenv import load_dotenv
load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")

from v4.schemas import AnnotatedSegment, ALL_PROSODY_TAGS
from v4.p5_tts import _compose_tts_text, _normalize_tags
from v4.p1_voice_cloning import SPEAKER_TO_VOICE, FIGURANT_RAW_VOICE_OVERRIDE
from v4.fishaudio_client import fishaudio_tts, audio_duration_mp3

TEST_FILE = Path(__file__).parent / "outputs" / "annotated_v4_tags_only_test.json"
TTS_DIR = Path(__file__).parent / "outputs" / "tts_tags_only_test"
WHISPER_URL = "http://localhost:8190/v1/audio/transcriptions"
THRESHOLD = 0.15


def _get_reference_id(seg: dict) -> str:
    speaker = seg.get("speaker", "narrateur")
    voice = SPEAKER_TO_VOICE.get(speaker, SPEAKER_TO_VOICE.get("figurant", ""))
    if speaker == "figurant":
        raw = seg.get("speaker_raw", "")
        voice = FIGURANT_RAW_VOICE_OVERRIDE.get(raw, voice)
    return voice


def normalize_text(t):
    t = t.lower().strip()
    t = re.sub(r"[^\w\s]", "", t)
    t = re.sub(r"\s+", " ", t)
    return t


def compute_wer(ref, hyp):
    ref_words = normalize_text(ref).split()
    hyp_words = normalize_text(hyp).split()
    if not ref_words:
        return 0.0 if not hyp_words else float("inf")
    n, m = len(ref_words), len(hyp_words)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = i
    for j in range(m + 1):
        dp[0][j] = j
    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if ref_words[i - 1] == hyp_words[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1])
    return dp[n][m] / n


def main():
    with open(TEST_FILE, encoding="utf-8") as f:
        data = json.load(f)

    segments = data["segments"]
    print(f"Loaded {len(segments)} test segments")

    TTS_DIR.mkdir(exist_ok=True, parents=True)

    # Get Whisper API key
    api_key = os.getenv("WHISPER_API_KEY", "")
    if not api_key:
        import subprocess
        result = subprocess.run(
            ["docker", "inspect", "--format", "{{range .Config.Env}}{{println .}}{{end}}", "whisper-api"],
            capture_output=True, text=True,
        )
        for line in result.stdout.splitlines():
            if line.startswith("API_KEY="):
                api_key = line.split("=", 1)[1].strip().strip('"')
                break
    print(f"Whisper API key: {'found' if api_key else 'MISSING'}")

    # Step 1: Generate TTS
    results = []
    for seg_data in segments:
        idx = seg_data["seg_index"]
        seg = AnnotatedSegment.model_validate(seg_data)
        tts_text = _compose_tts_text(seg)
        ref_id = _get_reference_id(seg_data)
        mp3_path = TTS_DIR / f"seg_{idx:04d}.mp3"

        if mp3_path.exists():
            print(f"  seg {idx}: cached")
        else:
            print(f"  seg {idx}: generating TTS ({len(tts_text)} chars, ref={ref_id})...")
            audio = fishaudio_tts(tts_text, reference_id=ref_id)
            if audio:
                mp3_path.write_bytes(audio)
                print(f"    -> {len(audio)} bytes, saved")
            else:
                print(f"    -> FAILED")
                results.append({"seg_index": idx, "tts_status": "failed"})
                continue

        duration = audio_duration_mp3(str(mp3_path)) if mp3_path.exists() else 0
        results.append({
            "seg_index": idx,
            "tts_status": "ok",
            "mp3_path": str(mp3_path),
            "duration_s": round(duration, 2),
            "tts_text": tts_text[:100],
        })

    # Step 2: WER validation
    print(f"\n--- WER Validation ---")
    wer_results = []
    verified = 0
    passed = 0
    wer_sum = 0.0
    import requests as req

    for r in results:
        if r["tts_status"] != "ok":
            continue
        idx = r["seg_index"]
        mp3_path = r["mp3_path"]
        ref_text = next(s["text"] for s in segments if s["seg_index"] == idx)

        try:
            with open(mp3_path, "rb") as af:
                resp = req.post(
                    WHISPER_URL,
                    headers={"Authorization": f"Bearer {api_key}"},
                    files={"file": ("audio.mp3", af, "audio/mpeg")},
                    data={"model": "large-v3-turbo", "language": "fr"},
                    timeout=30,
                )
            if resp.status_code != 200:
                print(f"  seg {idx}: API error {resp.status_code}")
                continue
            transcription = resp.json().get("text", "")
        except Exception as e:
            print(f"  seg {idx}: error {e}")
            continue

        wer = compute_wer(ref_text, transcription)
        verified += 1
        wer_sum += wer
        conform = wer <= THRESHOLD
        if conform:
            passed += 1

        wer_results.append({
            "seg_index": idx,
            "wer": round(wer, 4),
            "conform": conform,
            "ref": ref_text[:80],
            "hyp": transcription[:80],
        })
        status = "PASS" if conform else "FAIL"
        print(f"  seg {idx}: WER={wer*100:.1f}% [{status}]")

    avg_wer = wer_sum / verified if verified > 0 else 0
    pass_rate = 100 * passed / verified if verified > 0 else 0

    print(f"\n=== TAGS-ONLY TEST RESULTS ===")
    print(f"Segments: {len(segments)}")
    print(f"TTS generated: {sum(1 for r in results if r['tts_status'] == 'ok')}")
    print(f"WER verified: {verified}")
    print(f"Passed (WER<={THRESHOLD*100:.0f}%): {passed}/{verified} ({pass_rate:.1f}%)")
    print(f"Mean WER: {avg_wer*100:.2f}%")

    # Compare with POST-fix baseline (from wer_validation_post_fix.json)
    baseline_path = Path(__file__).parent / "outputs" / "wer_validation_post_fix.json"
    if baseline_path.exists():
        with open(baseline_path, encoding="utf-8") as f:
            baseline = json.load(f)
        test_indices = set(s["seg_index"] for s in segments)
        baseline_subset = [
            r for r in baseline["results"]
            if r["seg_index"] in test_indices
        ]
        if baseline_subset:
            bl_passed = sum(1 for r in baseline_subset if r["conform"])
            bl_avg = sum(r["wer"] for r in baseline_subset) / len(baseline_subset)
            print(f"\n--- Baseline comparison (same {len(baseline_subset)} segments) ---")
            print(f"  Baseline: {bl_passed}/{len(baseline_subset)} passed ({100*bl_passed/len(baseline_subset):.1f}%), avg WER={bl_avg*100:.2f}%")
            print(f"  Tags-only: {passed}/{verified} passed ({pass_rate:.1f}%), avg WER={avg_wer*100:.2f}%")

    out = {
        "methodology": "P4 re-run with 29 official tags only + P5 TTS + Whisper WER",
        "test_segments": list(range(0, 21)),
        "threshold": THRESHOLD,
        "verified": verified,
        "passed": passed,
        "pass_rate_pct": round(pass_rate, 1),
        "avg_wer_pct": round(avg_wer * 100, 2),
        "wer_results": wer_results,
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    out_path = Path(__file__).parent / "outputs" / "wer_tags_only_test.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2)
    print(f"\nSaved: {out_path}")


if __name__ == "__main__":
    main()
