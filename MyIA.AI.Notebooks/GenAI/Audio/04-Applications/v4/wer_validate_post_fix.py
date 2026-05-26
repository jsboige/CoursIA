#!/usr/bin/env python3
"""WER validation on POST-fix MP3s — same methodology as wer_validation_full.json"""
import json, os, time, re, sys
import requests

WHISPER_URL = "http://localhost:8190/v1/audio/transcriptions"
API_KEY = "ucoQtp68sir65NNPmxP-Ef_BOKNsEebDlHTB9ytCKT_UYR6HQ7yDXF9lgR5zz6R6"
THRESHOLD = 0.15

script_dir = os.path.dirname(os.path.abspath(__file__))
outputs_dir = os.path.join(script_dir, "outputs")

with open(os.path.join(outputs_dir, "annotated_v4.json"), encoding="utf-8") as f:
    data = json.load(f)
segments = data["segments"]

with open(os.path.join(outputs_dir, "tts_results.json"), encoding="utf-8") as f:
    tts_results = json.load(f)

mp3_map = {}
for r in tts_results:
    mp3_map[r["seg_index"]] = r.get("mp3_path", r.get("output_path", ""))


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


results = []
verified = 0
passed = 0
failed = 0
errors = 0
wer_sum = 0.0
wer_above_100 = 0
total = len(segments)
print(f"Starting WER validation on {total} segments...", flush=True)

for i, seg in enumerate(segments):
    idx = seg["seg_index"]
    ref_text = seg.get("text", "")
    mp3_path = mp3_map.get(idx, "")

    if not mp3_path or not os.path.exists(mp3_path):
        errors += 1
        continue

    try:
        with open(mp3_path, "rb") as audio_f:
            resp = requests.post(
                WHISPER_URL,
                headers={"Authorization": f"Bearer {API_KEY}"},
                files={"file": ("audio.mp3", audio_f, "audio/mpeg")},
                data={"model": "large-v3-turbo", "language": "fr"},
                timeout=30,
            )
        if resp.status_code != 200:
            errors += 1
            if (i + 1) % 50 == 0:
                print(f"  seg {idx}: API error {resp.status_code}", flush=True)
            continue
        transcription = resp.json().get("text", "")
    except Exception as e:
        errors += 1
        continue

    wer = compute_wer(ref_text, transcription)
    verified += 1
    wer_sum += wer
    if wer <= THRESHOLD:
        passed += 1
    else:
        failed += 1
    if wer > 1.0:
        wer_above_100 += 1

    results.append(
        {
            "seg_index": idx,
            "speaker": seg.get("speaker", ""),
            "wer": round(wer, 4),
            "conform": wer <= THRESHOLD,
        }
    )

    if (i + 1) % 50 == 0:
        pr = 100 * passed / verified if verified else 0
        print(
            f"Progress: {i+1}/{total} verified={verified} passed={passed} ({pr:.1f}%) wer>100={wer_above_100}",
            flush=True,
        )

avg_wer = wer_sum / verified if verified > 0 else 0
pass_rate = 100 * passed / verified if verified > 0 else 0

summary = {
    "methodology": "Whisper large-v3-turbo + Levenshtein word-level WER",
    "threshold": THRESHOLD,
    "total_segments": total,
    "verified": verified,
    "passed": passed,
    "failed": failed,
    "errors": errors,
    "pass_rate_pct": round(pass_rate, 1),
    "avg_wer_pct": round(avg_wer * 100, 2),
    "wer_above_100_count": wer_above_100,
    "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "results": results,
}

outpath = os.path.join(outputs_dir, "wer_validation_post_fix.json")
with open(outpath, "w", encoding="utf-8") as f:
    json.dump(summary, f, ensure_ascii=False, indent=2)

print(flush=True)
print("=== POST-FIX WER VALIDATION RESULTS ===", flush=True)
print(f"Total: {total}, Verified: {verified}, Errors: {errors}", flush=True)
print(f"Passed: {passed} ({pass_rate:.1f}%), Failed: {failed}", flush=True)
print(f"Mean WER: {avg_wer*100:.2f}%", flush=True)
print(f"WER > 100%: {wer_above_100}", flush=True)
print(f"Saved: {outpath}", flush=True)
