#!/usr/bin/env python3
"""Stage 1: Transcription conformity verification via Whisper API.

Compares TTS-generated audio against original text using:
- Word Error Rate (WER)
- Character Error Rate (CER) via Levenshtein distance
- Semantic flagging for segments above threshold

Usage:
    python verify_transcript.py --audio-dir outputs/tts_v4 \
        --metadata outputs/annotated_v4.json \
        --threshold 0.15
    python verify_transcript.py --single outputs/tts_v4/seg_0012_narrateur.mp3 \
        --text "Le devoir commençait..."
"""

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path
from difflib import SequenceMatcher

WHISPER_URL = os.getenv("WHISPER_API_URL", "http://localhost:8190")
WHISPER_KEY = os.getenv("WHISPER_API_KEY", "")


def _normalize_text(text: str) -> str:
    """Normalize text for comparison: lowercase, strip punctuation, collapse whitespace."""
    text = text.lower().strip()
    text = re.sub(r"[^\w\sàâéèêëïîôùûüÿçœæ-]", " ", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def _levenshtein_distance(s1: str, s2: str) -> int:
    """Compute Levenshtein edit distance between two strings."""
    if len(s1) < len(s2):
        return _levenshtein_distance(s2, s1)
    if len(s2) == 0:
        return len(s1)
    prev_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        curr_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = prev_row[j + 1] + 1
            deletions = curr_row[j] + 1
            substitutions = prev_row[j] + (c1 != c2)
            curr_row.append(min(insertions, deletions, substitutions))
        prev_row = curr_row
    return prev_row[-1]


def compute_wer(reference: str, hypothesis: str) -> float:
    """Compute Word Error Rate: (S + D + I) / N."""
    ref_words = _normalize_text(reference).split()
    hyp_words = _normalize_text(hypothesis).split()

    if not ref_words:
        return 0.0 if not hyp_words else 1.0

    n = len(ref_words)
    d = [[0] * (len(hyp_words) + 1) for _ in range(n + 1)]

    for i in range(n + 1):
        d[i][0] = i
    for j in range(len(hyp_words) + 1):
        d[0][j] = j

    for i in range(1, n + 1):
        for j in range(1, len(hyp_words) + 1):
            if ref_words[i - 1] == hyp_words[j - 1]:
                d[i][j] = d[i - 1][j - 1]
            else:
                d[i][j] = 1 + min(d[i - 1][j], d[i][j - 1], d[i - 1][j - 1])

    return d[n][len(hyp_words)] / n


def compute_cer(reference: str, hypothesis: str) -> float:
    """Compute Character Error Rate."""
    ref_norm = _normalize_text(reference)
    hyp_norm = _normalize_text(hypothesis)
    if not ref_norm:
        return 0.0 if not hyp_norm else 1.0
    return _levenshtein_distance(ref_norm, hyp_norm) / len(ref_norm)


def compute_similarity(reference: str, hypothesis: str) -> float:
    """Compute SequenceMatcher ratio (0-1, higher = more similar)."""
    return SequenceMatcher(None, _normalize_text(reference), _normalize_text(hypothesis)).ratio()


def transcribe_audio(audio_path: str) -> dict:
    """Transcribe audio file via Whisper API."""
    import urllib.request
    import urllib.error

    url = f"{WHISPER_URL}/v1/audio/transcriptions"
    boundary = "----WebKitFormBoundary7MA4YWxkTrZu0gW"

    with open(audio_path, "rb") as f:
        audio_data = f.read()

    filename = Path(audio_path).name
    body = (
        f"--{boundary}\r\n"
        f'Content-Disposition: form-data; name="file"; filename="{filename}"\r\n'
        f"Content-Type: audio/mpeg\r\n\r\n".encode()
        + audio_data
        + f"\r\n--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="model"\r\n\r\nwhisper-1\r\n'
        + f"--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="language"\r\n\r\nfr\r\n'
        + f"--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="response_format"\r\n\r\nverbose_json\r\n'
        + f"--{boundary}--\r\n".encode()
    )

    req = urllib.request.Request(
        url,
        data=body,
        headers={
            "Content-Type": f"multipart/form-data; boundary={boundary}",
            "Authorization": f"Bearer {WHISPER_KEY}",
        },
        method="POST",
    )

    try:
        with urllib.request.urlopen(req, timeout=120) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        error_body = e.read().decode() if e.fp else ""
        return {"error": f"HTTP {e.code}: {error_body[:200]}"}
    except Exception as e:
        return {"error": str(e)[:200]}


def verify_single(audio_path: str, reference_text: str) -> dict:
    """Verify a single audio file against reference text."""
    result = transcribe_audio(audio_path)

    if "error" in result:
        return {
            "audio_path": audio_path,
            "transcription": "",
            "error": result["error"],
            "wer": 1.0,
            "cer": 1.0,
            "similarity": 0.0,
            "duration_s": 0.0,
            "conform": False,
        }

    transcript = result.get("text", "")
    duration = result.get("duration", 0.0)

    wer = compute_wer(reference_text, transcript)
    cer = compute_cer(reference_text, transcript)
    sim = compute_similarity(reference_text, transcript)

    return {
        "audio_path": audio_path,
        "transcription": transcript[:500],
        "reference": reference_text[:500],
        "wer": round(wer, 4),
        "cer": round(cer, 4),
        "similarity": round(sim, 4),
        "duration_s": round(duration, 2),
        "conform": None,
    }


def verify_batch(
    audio_dir: str,
    metadata_path: str,
    threshold: float = 0.15,
    max_segments: int = 0,
    output_path: str | None = None,
) -> dict:
    """Verify batch of TTS segments against annotated metadata.

    Returns summary with per-segment results and aggregate stats.
    """
    with open(metadata_path, encoding="utf-8") as f:
        metadata = json.load(f)

    segments = metadata.get("segments", [])
    if max_segments > 0:
        segments = segments[:max_segments]

    results = []
    passed = 0
    failed = 0
    errors = 0
    total_wer = 0.0
    total_cer = 0.0

    for i, seg in enumerate(segments):
        seg_idx = seg.get("seg_index", i)
        speaker = seg.get("speaker", "unknown")
        reference = seg.get("text", "")

        if not reference:
            continue

        audio_name = f"seg_{seg_idx:04d}_{speaker}.mp3"
        audio_path = os.path.join(audio_dir, audio_name)

        if not os.path.exists(audio_path):
            results.append({
                "seg_index": seg_idx,
                "speaker": speaker,
                "audio_path": audio_name,
                "error": "audio file not found",
                "wer": 1.0,
                "conform": False,
            })
            errors += 1
            continue

        print(f"  [{i+1}/{len(segments)}] {audio_name}...", end=" ", flush=True)
        t0 = time.time()
        r = verify_single(audio_path, reference)
        elapsed = time.time() - t0

        r["seg_index"] = seg_idx
        r["speaker"] = speaker
        r["conform"] = r["wer"] <= threshold
        results.append(r)

        status = "OK" if r["conform"] else "FLAG"
        if "error" in r and r.get("wer", 1.0) == 1.0 and not r.get("transcription"):
            status = "ERR"
            errors += 1
        elif r["conform"]:
            passed += 1
        else:
            failed += 1

        total_wer += r.get("wer", 0.0)
        total_cer += r.get("cer", 0.0)

        print(f"WER={r.get('wer', 0):.2%} CER={r.get('cer', 0):.2%} [{status}] ({elapsed:.1f}s)")

    n_verified = passed + failed
    summary = {
        "total_segments": len(segments),
        "verified": n_verified,
        "passed": passed,
        "failed": failed,
        "errors": errors,
        "threshold": threshold,
        "avg_wer": round(total_wer / n_verified, 4) if n_verified > 0 else 0.0,
        "avg_cer": round(total_cer / n_verified, 4) if n_verified > 0 else 0.0,
        "pass_rate": round(passed / n_verified * 100, 1) if n_verified > 0 else 0.0,
        "results": results,
    }

    if output_path:
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {output_path}")

    return summary


def print_report(summary: dict):
    """Print human-readable verification report."""
    print(f"\n{'=' * 60}")
    print(f"TRANSCRIPT CONFORMITY REPORT")
    print(f"{'=' * 60}")
    print(f"Segments verified: {summary['verified']}/{summary['total_segments']}")
    print(f"Threshold: WER <= {summary['threshold']:.0%}")
    print(f"Pass rate: {summary['pass_rate']:.1f}%")
    print(f"Avg WER: {summary['avg_wer']:.2%}")
    print(f"Avg CER: {summary['avg_cer']:.2%}")
    print(f"Passed: {summary['passed']} | Failed: {summary['failed']} | Errors: {summary['errors']}")

    flagged = [r for r in summary["results"] if not r.get("conform", True)]
    if flagged:
        print(f"\n--- FLAGGED SEGMENTS ({len(flagged)}) ---")
        for r in sorted(flagged, key=lambda x: x.get("wer", 0), reverse=True)[:20]:
            print(
                f"  seg_{r.get('seg_index', '?'):04d}_{r.get('speaker', '?')}: "
                f"WER={r.get('wer', 0):.2%} CER={r.get('cer', 0):.2%} "
                f"{'[' + r.get('error', '') + ']' if r.get('error') else ''}"
            )
            if r.get("transcription"):
                print(f"    transcript: {r['transcription'][:80]}")
                print(f"    reference:  {r.get('reference', '')[:80]}")


def main():
    parser = argparse.ArgumentParser(description="Stage 1: Transcript conformity verification")
    parser.add_argument("--audio-dir", required=True, help="Directory with TTS audio files")
    parser.add_argument("--metadata", help="Annotated segments JSON (for batch mode)")
    parser.add_argument("--single", help="Single audio file to verify")
    parser.add_argument("--text", help="Reference text (for --single mode)")
    parser.add_argument("--threshold", type=float, default=0.15, help="WER threshold (default: 0.15)")
    parser.add_argument("--max-segments", type=int, default=0, help="Max segments to verify (0=all)")
    parser.add_argument("--output", help="Save results JSON to this path")
    parser.add_argument("--whisper-url", default="", help="Override Whisper API URL")
    parser.add_argument("--whisper-key", default="", help="Override Whisper API key")
    args = parser.parse_args()

    if args.whisper_url:
        global WHISPER_URL
        WHISPER_URL = args.whisper_url
    if args.whisper_key:
        global WHISPER_KEY
        WHISPER_KEY = args.whisper_key

    if not WHISPER_KEY:
        print("Error: WHISPER_API_KEY env var or --whisper-key required")
        sys.exit(1)

    if args.single:
        if not args.text:
            print("Error: --text required with --single")
            sys.exit(1)
        result = verify_single(args.single, args.text)
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return

    if not args.metadata:
        print("Error: --metadata required for batch mode (or use --single)")
        sys.exit(1)

    summary = verify_batch(
        audio_dir=args.audio_dir,
        metadata_path=args.metadata,
        threshold=args.threshold,
        max_segments=args.max_segments,
        output_path=args.output,
    )
    print_report(summary)


if __name__ == "__main__":
    main()
