#!/usr/bin/env python3
"""Stage 2: Speaker diarization verification via Whisper WebUI.

Uses real speaker diarization (pyannote via Whisper WebUI Gradio API) to verify:
- Speaker clustering matches expected voice attribution
- Voice purity: % of segments where dominant speaker matches expected voice
- Cross-contamination detection (wrong speaker detected in a segment)

Requires:
- Whisper WebUI running with diarization enabled (pyannote + HF_TOKEN)
- Or standard Whisper API for fallback (text-matching only, no real diarization)

Usage:
    # Real diarization (recommended)
    python verify_diarization.py --audio-dir outputs/tts_v4 \
        --metadata outputs/annotated_v4.json --mode gradio

    # Fallback: Whisper transcription API (no real speaker labels)
    python verify_diarization.py --audio-dir outputs/tts_v4 \
        --metadata outputs/annotated_v4.json --mode whisper

    # Single segment test
    python verify_diarization.py --single outputs/tts_v4/seg_0012_narrateur.mp3 \
        --expected-speaker narrateur --mode gradio
"""

import argparse
import json
import os
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

WHISPER_URL = os.getenv("WHISPER_API_URL", "http://localhost:8190")
WHISPER_KEY = os.getenv("WHISPER_API_KEY", "")
WHISPER_WEBUI_URL = os.getenv("WHISPER_WEBUI_URL", "http://localhost:36540")
WHISPER_WEBUI_USER = os.getenv("WHISPER_WEBUI_USER", "admin")
WHISPER_WEBUI_PASSWORD = os.getenv("WHISPER_WEBUI_PASSWORD", "changeme")


# ---------------------------------------------------------------------------
# Diarization backends
# ---------------------------------------------------------------------------

def _gradio_login() -> "requests.Session":
    """Authenticate with Whisper WebUI Gradio app."""
    import requests
    s = requests.Session()
    r = s.post(
        f"{WHISPER_WEBUI_URL}/login",
        data={"username": WHISPER_WEBUI_USER, "password": WHISPER_WEBUI_PASSWORD},
    )
    if r.status_code != 200:
        raise RuntimeError(f"Whisper WebUI login failed ({r.status_code}): {r.text[:200]}")
    return s


def _gradio_upload(session: "requests.Session", file_path: str) -> str:
    """Upload a file to Gradio and return server path."""
    with open(file_path, "rb") as f:
        r = session.post(
            f"{WHISPER_WEBUI_URL}/gradio_api/upload",
            files={"files": (Path(file_path).name, f, "audio/mpeg")},
        )
    if r.status_code != 200:
        raise RuntimeError(f"Upload failed ({r.status_code}): {r.text[:200]}")
    return r.json()[0]


def diarize_gradio(audio_path: str, session: "requests.Session") -> dict:
    """Run real diarization via Whisper WebUI Gradio API.

    Returns dict with keys: detected_speakers, segments, dominant_speaker, srt_raw.
    Each segment has: speaker, start, end, text.
    """
    import requests

    uploaded = _gradio_upload(session, audio_path)

    prepend_punc = "\"'" + "“¿([{-"
    append_punc = "\"'" + ".。,，!！?？:：”)]}、"

    payload = {
        "data": [
            [{"path": uploaded, "meta": {"_type": "gradio.FileData"}}],
            "", False, True, "SRT", False,
            "large-v3-turbo", "french", False,
            5, -1, 0.6, "float32", 5, 1, True, 0.5, "", 0,
            2.4, 1, 1, 0, "", True, "[-1]", 1, False,
            prepend_punc, append_punc,
            None, 30, None, "", 0.5, 1, 24, True,
            False, 0.5, 250, 9999, 1000, 2000,
            True, "cuda", os.getenv("HF_TOKEN", ""), True,
            False, "UVR-MDX-NET-Inst_HQ_4", "cuda", 256, False, True,
        ]
    }

    r = session.post(
        f"{WHISPER_WEBUI_URL}/gradio_api/call/transcribe_file",
        json=payload,
    )
    if r.status_code != 200:
        return {"error": f"Gradio call failed ({r.status_code}): {r.text[:300]}"}

    event_id = r.json().get("event_id")
    if not event_id:
        return {"error": f"No event_id in response: {r.text[:200]}"}

    # Stream SSE result
    r2 = session.get(
        f"{WHISPER_WEBUI_URL}/gradio_api/call/transcribe_file/{event_id}",
        stream=True, timeout=600,
    )
    result_data = None
    error_msg = None
    for line in r2.iter_lines(decode_unicode=True):
        if not line:
            continue
        if line.startswith("event:"):
            evt = line[6:].strip()
            if evt == "error":
                error_msg = "server error in SSE stream"
        elif line.startswith("data:"):
            raw = line[5:].strip()
            try:
                result_data = json.loads(raw)
            except json.JSONDecodeError:
                error_msg = raw

    if error_msg and not result_data:
        return {"error": f"Diarization SSE failed: {error_msg[:300]}"}

    srt_text = ""
    if result_data and isinstance(result_data, list) and len(result_data) > 0:
        srt_text = str(result_data[0])

    # Parse SRT
    segments = _parse_srt(srt_text)
    speakers = list(set(s["speaker"] for s in segments)) if segments else []
    speaker_durations = defaultdict(float)
    for seg in segments:
        speaker_durations[seg["speaker"]] += seg["end"] - seg["start"]
    dominant = max(speaker_durations, key=speaker_durations.get) if speaker_durations else ""

    return {
        "detected_speakers": speakers,
        "segments": segments,
        "dominant_speaker": dominant,
        "srt_raw": srt_text,
    }


def _parse_srt(srt_content: str) -> list[dict]:
    """Parse SRT with speaker labels into structured segments."""
    if not srt_content:
        return []
    segments = []
    blocks = srt_content.strip().split("\n\n")
    for block in blocks:
        lines = block.strip().split("\n")
        if len(lines) < 3:
            continue
        text = " ".join(lines[2:])
        speaker = "UNKNOWN"
        if "|" in text and text.startswith("SPEAKER_"):
            pipe_idx = text.index("|")
            speaker = text[:pipe_idx]
            text = text[pipe_idx + 1:].strip()
        try:
            parts = lines[1].split(" --> ")
            start_str = parts[0].strip().replace(",", ".")
            end_str = parts[1].strip().replace(",", ".")
            start_h, start_m, start_s = start_str.split(":")
            end_h, end_m, end_s = end_str.split(":")
            start_time = int(start_h) * 3600 + int(start_m) * 60 + float(start_s)
            end_time = int(end_h) * 3600 + int(end_m) * 60 + float(end_s)
        except (ValueError, IndexError):
            start_time = 0.0
            end_time = 0.0
        segments.append({
            "speaker": speaker,
            "start": start_time,
            "end": end_time,
            "text": text,
        })
    return segments


def diarize_whisper_fallback(audio_path: str) -> dict:
    """Fallback: standard Whisper transcription API (no real speaker labels).

    Returns timing segments without speaker attribution.
    """
    import urllib.request
    import urllib.error

    url = f"{WHISPER_URL}/v1/audio/transcriptions"
    boundary = "----WebKitFormBoundary7MA4YWxkTrZu0gW"

    with open(audio_path, "rb") as f:
        audio_data = f.read()

    filename = Path(audio_path).name
    body = (
        f"--{boundary}\r\n".encode()
        + f'Content-Disposition: form-data; name="file"; filename="{filename}"\r\n'.encode()
        + b"Content-Type: audio/mpeg\r\n\r\n"
        + audio_data
        + f"\r\n--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="model"\r\n\r\nwhisper-1\r\n'
        + f"--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="language"\r\n\r\nfr\r\n'
        + f"--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="response_format"\r\n\r\nverbose_json\r\n'
        + f"--{boundary}\r\n".encode()
        + b'Content-Disposition: form-data; name="timestamp_granularities[]"\r\n\r\nsegment\r\n'
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
        with urllib.request.urlopen(req, timeout=300) as resp:
            result = json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        error_body = e.read().decode() if e.fp else ""
        return {"error": f"HTTP {e.code}: {error_body[:200]}"}
    except Exception as e:
        return {"error": str(e)[:200]}

    whisper_segments = result.get("segments", [])
    segments = []
    for ws in whisper_segments:
        segments.append({
            "speaker": "SPEAKER_UNKNOWN",
            "start": ws.get("start", 0.0),
            "end": ws.get("end", 0.0),
            "text": ws.get("text", ""),
        })

    return {
        "detected_speakers": [],
        "segments": segments,
        "dominant_speaker": "",
        "transcript": result.get("text", ""),
        "duration": result.get("duration", 0.0),
    }


# ---------------------------------------------------------------------------
# Voice purity scoring
# ---------------------------------------------------------------------------

def build_speaker_mapping(
    results: list[dict],
    expected_speakers: list[str],
) -> dict[str, str]:
    """Build mapping from detected speaker labels to expected speakers.

    Uses co-occurrence: if SPEAKER_00 appears most often in segments
    expected to be "narrateur", map SPEAKER_00 -> narrateur.
    """
    co_occurrence = defaultdict(Counter)

    for r in results:
        detected = r.get("dominant_speaker", "")
        expected = r.get("expected_speaker", "")
        if detected and expected and not r.get("error"):
            co_occurrence[detected][expected] += 1

    mapping = {}
    for detected_label, expected_counts in co_occurrence.items():
        best_expected = expected_counts.most_common(1)[0][0]
        mapping[detected_label] = best_expected

    return mapping


def compute_voice_purity(
    results: list[dict],
    speaker_mapping: dict[str, str],
) -> dict:
    """Compute voice purity metrics.

    For each segment, check if the mapped dominant speaker matches expected.
    Also detect cross-contamination: non-dominant speakers in a segment.
    """
    total = 0
    pure = 0
    contaminated = 0
    contamination_details = []

    for r in results:
        if r.get("error"):
            continue
        dominant = r.get("dominant_speaker", "")
        expected = r.get("expected_speaker", "")
        if not dominant or not expected:
            continue

        total += 1
        mapped = speaker_mapping.get(dominant, dominant)

        if mapped == expected:
            pure += 1
        else:
            contamination_details.append({
                "seg_index": r.get("seg_index"),
                "expected": expected,
                "detected_dominant": dominant,
                "detected_mapped": mapped,
            })

        # Check for cross-contamination: multiple speakers in a segment
        all_speakers = r.get("detected_speakers", [])
        if len(all_speakers) > 1:
            non_dominant = [s for s in all_speakers if s != dominant]
            non_dominant_mapped = [speaker_mapping.get(s, s) for s in non_dominant]
            foreign = [s for s in non_dominant_mapped if s != expected]
            if foreign:
                contaminated += 1
                r["cross_contamination"] = True
                r["foreign_speakers"] = foreign

    purity_rate = round(pure / total * 100, 1) if total > 0 else 0.0
    contamination_rate = round(contaminated / total * 100, 1) if total > 0 else 0.0

    return {
        "total_scored": total,
        "pure_segments": pure,
        "purity_rate": purity_rate,
        "cross_contaminated": contaminated,
        "contamination_rate": contamination_rate,
        "contamination_details": contamination_details[:20],
    }


# ---------------------------------------------------------------------------
# Batch verification
# ---------------------------------------------------------------------------

def verify_diarization_batch(
    audio_dir: str,
    metadata_path: str,
    mode: str = "gradio",
    max_segments: int = 0,
    output_path: str | None = None,
) -> dict:
    """Run diarization verification on batch of TTS segments.

    Args:
        mode: "gradio" for real diarization, "whisper" for fallback.
    """
    with open(metadata_path, encoding="utf-8") as f:
        metadata = json.load(f)

    segments = metadata.get("segments", [])
    if max_segments > 0:
        segments = segments[:max_segments]

    session = None
    if mode == "gradio":
        try:
            session = _gradio_login()
            print(f"Connected to Whisper WebUI at {WHISPER_WEBUI_URL}")
        except Exception as e:
            print(f"Warning: Gradio login failed ({e}), falling back to whisper mode")
            mode = "whisper"

    results = []
    passed = 0
    failed = 0
    errors = 0

    for i, seg in enumerate(segments):
        seg_idx = seg.get("seg_index", i)
        speaker = seg.get("speaker", "unknown")
        reference = seg.get("text", "")

        audio_name = f"seg_{seg_idx:04d}_{speaker}.mp3"
        audio_path = os.path.join(audio_dir, audio_name)

        if not os.path.exists(audio_path):
            errors += 1
            results.append({
                "seg_index": seg_idx,
                "expected_speaker": speaker,
                "error": "audio file not found",
            })
            continue

        print(f"  [{i+1}/{len(segments)}] {audio_name}...", end=" ", flush=True)
        t0 = time.time()

        try:
            if mode == "gradio":
                dia_result = diarize_gradio(audio_path, session)
            else:
                dia_result = diarize_whisper_fallback(audio_path)
        except Exception as e:
            elapsed = time.time() - t0
            print(f"ERR ({elapsed:.1f}s)")
            errors += 1
            results.append({
                "seg_index": seg_idx,
                "expected_speaker": speaker,
                "error": str(e)[:200],
            })
            continue

        elapsed = time.time() - t0

        if "error" in dia_result:
            print(f"ERR: {dia_result['error'][:60]} ({elapsed:.1f}s)")
            errors += 1
            results.append({
                "seg_index": seg_idx,
                "expected_speaker": speaker,
                "error": dia_result["error"],
            })
            continue

        detected_speakers = dia_result.get("detected_speakers", [])
        dominant = dia_result.get("dominant_speaker", "")
        dia_segments = dia_result.get("segments", [])
        n_subsegments = len(dia_segments) if dia_segments else 1

        # Duration from diarization segments
        if dia_segments:
            duration = round(dia_segments[-1]["end"] - dia_segments[0]["start"], 2)
        else:
            duration = dia_result.get("duration", 0.0)

        entry = {
            "seg_index": seg_idx,
            "expected_speaker": speaker,
            "dominant_speaker": dominant,
            "detected_speakers": detected_speakers,
            "duration_s": duration,
            "n_subsegments": n_subsegments,
            "elapsed_s": round(elapsed, 1),
        }

        # Light transcript check via WER if we have text
        from verify_transcript import compute_wer
        dia_text = " ".join(s["text"] for s in dia_segments).strip()
        if dia_text and reference:
            wer = compute_wer(reference, dia_text)
            entry["wer"] = round(wer, 4)

        results.append(entry)
        passed += 1

        speakers_str = ",".join(detected_speakers) if detected_speakers else "none"
        print(f"dur={duration:.1f}s dom={dominant} spks=[{speakers_str}] ({elapsed:.1f}s)")

    # Build speaker mapping and voice purity
    expected_speakers = list(set(r.get("expected_speaker", "") for r in results if r.get("expected_speaker")))
    speaker_mapping = build_speaker_mapping(results, expected_speakers)
    purity = compute_voice_purity(results, speaker_mapping)

    summary = {
        "mode": mode,
        "total_segments": len(segments),
        "verified": passed + failed,
        "passed": passed,
        "failed": failed,
        "errors": errors,
        "speaker_mapping": speaker_mapping,
        "voice_purity": purity,
        "results": results,
    }

    if output_path:
        with open(output_path, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        print(f"\nResults saved to {output_path}")

    return summary


def print_diarization_report(summary: dict):
    """Print human-readable diarization report."""
    mode = summary.get("mode", "unknown")
    print(f"\n{'=' * 60}")
    print(f"SPEAKER DIARIZATION REPORT (mode: {mode})")
    print(f"{'=' * 60}")
    print(f"Segments verified: {summary['verified']}/{summary['total_segments']}")
    print(f"Passed: {summary['passed']} | Failed: {summary['failed']} | Errors: {summary['errors']}")

    # Speaker mapping
    mapping = summary.get("speaker_mapping", {})
    if mapping:
        print(f"\n--- Speaker Mapping ---")
        for detected, expected in sorted(mapping.items()):
            print(f"  {detected} -> {expected}")

    # Voice purity
    purity = summary.get("voice_purity", {})
    if purity.get("total_scored", 0) > 0:
        print(f"\n--- Voice Purity ---")
        print(f"  Purity rate: {purity['purity_rate']:.1f}% ({purity['pure_segments']}/{purity['total_scored']})")
        print(f"  Cross-contamination: {purity['contamination_rate']:.1f}% ({purity['cross_contaminated']} segments)")

        contamination = purity.get("contamination_details", [])
        if contamination:
            print(f"\n  --- Contamination Details (top {min(len(contamination), 10)}) ---")
            for c in contamination[:10]:
                print(
                    f"  seg_{c.get('seg_index', '?'):04d}: "
                    f"expected={c['expected']} got={c['detected_mapped']} "
                    f"(raw: {c['detected_dominant']})"
                )

    # Cross-contamination flagged segments
    x_contam = [r for r in summary["results"] if r.get("cross_contamination")]
    if x_contam:
        print(f"\n--- Cross-Contamination ({len(x_contam)} segments) ---")
        for r in x_contam[:10]:
            print(
                f"  seg_{r.get('seg_index', '?'):04d}_{r.get('expected_speaker', '?')}: "
                f"foreign={r.get('foreign_speakers', [])}"
            )

    # Multi-speaker segments
    multi = [r for r in summary["results"] if r.get("n_subsegments", 1) > 2]
    if multi:
        print(f"\n--- Multi-Speaker Segments ({len(multi)}) ---")
        for r in multi[:10]:
            print(
                f"  seg_{r.get('seg_index', '?'):04d}_{r.get('expected_speaker', '?')}: "
                f"{r.get('n_subsegments')} sub-segments"
            )


def main():
    parser = argparse.ArgumentParser(description="Stage 2: Speaker diarization verification")
    parser.add_argument("--audio-dir", help="Directory with TTS audio files")
    parser.add_argument("--metadata", help="Annotated segments JSON")
    parser.add_argument("--single", help="Single audio file to verify")
    parser.add_argument("--expected-speaker", help="Expected speaker (for --single mode)")
    parser.add_argument("--mode", choices=["gradio", "whisper"], default="gradio",
                        help="Diarization mode (default: gradio)")
    parser.add_argument("--max-segments", type=int, default=0, help="Max segments (0=all)")
    parser.add_argument("--output", help="Save results JSON to this path")
    parser.add_argument("--whisper-url", default="", help="Override Whisper API URL")
    parser.add_argument("--whisper-key", default="", help="Override Whisper API key")
    parser.add_argument("--webui-url", default="", help="Override Whisper WebUI URL")
    args = parser.parse_args()

    if args.whisper_url:
        global WHISPER_URL
        WHISPER_URL = args.whisper_url
    if args.whisper_key:
        global WHISPER_KEY
        WHISPER_KEY = args.whisper_key
    if args.webui_url:
        global WHISPER_WEBUI_URL
        WHISPER_WEBUI_URL = args.webui_url

    if args.single:
        if not args.expected_speaker:
            print("Error: --expected-speaker required with --single")
            sys.exit(1)

        if args.mode == "gradio":
            session = _gradio_login()
            result = diarize_gradio(args.single, session)
        else:
            if not WHISPER_KEY:
                print("Error: WHISPER_API_KEY env var or --whisper-key required")
                sys.exit(1)
            result = diarize_whisper_fallback(args.single)

        result["expected_speaker"] = args.expected_speaker
        result["audio_path"] = args.single
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return

    if not args.audio_dir or not args.metadata:
        print("Error: --audio-dir and --metadata required for batch mode (or use --single)")
        sys.exit(1)

    if args.mode == "whisper" and not WHISPER_KEY:
        print("Error: WHISPER_API_KEY env var or --whisper-key required for whisper mode")
        sys.exit(1)

    summary = verify_diarization_batch(
        audio_dir=args.audio_dir,
        metadata_path=args.metadata,
        mode=args.mode,
        max_segments=args.max_segments,
        output_path=args.output,
    )
    print_diarization_report(summary)


if __name__ == "__main__":
    main()
