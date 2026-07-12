"""E2E validation test for the v4 audiobook pipeline.

Runs P4 (annotation) + P5 (TTS) + P7 (verification) on a small subset
of segments to validate the entire pipeline end-to-end.

Test segments cover:
- Narration (0-11): Act 1 opening, pure narration
- Dialogue multi-speaker (72-75): comte + elisabeth_rousset
- Dialogue figurant/officier (96-97): figurant + officier

Usage:
    cd MyIA.AI.Notebooks/GenAI/Audio/04-Applications
    python -m v4.e2e_test --force
"""
from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

# Ensure parent directory is on path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from dotenv import load_dotenv

from .schemas import (
    Segment,
    SegmentBatch,
    DramaticContext,
    DramaticContextBatch,
    AnnotatedSegment,
    AnnotatedBatch,
    TTSResult,
)
from .p4_annotation import (
    annotate_batch,
    convert_tags_for_fishaudio,
    build_segment_block,
    NARRATOR_SYSTEM_PROMPT,
    DIALOGUE_SYSTEM_PROMPT,
)
from .p5_tts import _compose_tts_text, _resolve_voice, _synthesize_segment
from .fishaudio_client import audio_duration_mp3
from .diarization_client import login_session, diarize_segment

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
TTS_DIR = BASE_DIR / "outputs" / "tts_v4"

# Test segment indices
TEST_SEGMENTS = list(range(0, 12)) + [72, 73, 74, 75, 96, 97]


def load_test_data() -> tuple[list[Segment], dict[int, DramaticContext]]:
    """Load and filter test segments + dramatic context."""
    seg_data = json.loads(
        (OUTPUTS / "segments_v4.json").read_text(encoding="utf-8")
    )
    all_segments = [
        Segment(**s)
        for s in (seg_data if isinstance(seg_data, list) else seg_data["segments"])
    ]

    ctx_data = json.loads(
        (OUTPUTS / "dramatic_context.json").read_text(encoding="utf-8")
    )
    all_contexts = {
        c.seg_index: c
        for c in (
            DramaticContext(**c)
            for c in (
                ctx_data if isinstance(ctx_data, list) else ctx_data["contexts"]
            )
        )
    }

    test_segs = [s for s in all_segments if s.seg_index in TEST_SEGMENTS]
    test_ctx = {s.seg_index: all_contexts[s.seg_index] for s in test_segs if s.seg_index in all_contexts}

    print(f"[E2E] Test set: {len(test_segs)} segments, {len(test_ctx)} contexts")
    for s in test_segs:
        ctx_str = ""
        c = test_ctx.get(s.seg_index)
        if c:
            ctx_str = f" | tension={c.tension_0_10}"
        print(f"  seg {s.seg_index}: {s.type} | {s.speaker}{ctx_str}")

    return test_segs, test_ctx


def step_p4_annotation(
    segments: list[Segment],
    contexts: dict[int, DramaticContext],
) -> list[AnnotatedSegment]:
    """Step 1: Run P4 annotation on test segments."""
    print("\n" + "=" * 60)
    print("[E2E] STEP 1: P4 — Prosodic Annotation")
    print("=" * 60)

    all_annotated: list[AnnotatedSegment] = []

    # Split into sub-batches of 3 to avoid JSON truncation on OpenRouter
    _SUB_BATCH = 3
    batch_idx = 0
    for i in range(0, len(segments), _SUB_BATCH):
        sub = segments[i:i + _SUB_BATCH]
        batch_idx += 1
        idx_range = f"{sub[0].seg_index}-{sub[-1].seg_index}"
        print(f"\n  Sub-batch {batch_idx}: {len(sub)} segments ({idx_range})")
        try:
            annotated = annotate_batch(sub, contexts, batch_idx=batch_idx)
            all_annotated.extend(annotated)
        except Exception as e:
            print(f"  FAILED: {e}")
            raise

    # Save test output
    test_output = OUTPUTS / "e2e_annotated_test.json"
    batch_result = AnnotatedBatch(segments=all_annotated)
    test_output.write_text(batch_result.model_dump_json(indent=2), encoding="utf-8")

    # Validation checks
    print(f"\n[P4] Results:")
    for seg in all_annotated:
        official = len(seg.prosody_tags)
        total = len(seg.tags_used)
        prefix = seg.tts_context_prefix[:50] if seg.tts_context_prefix else "(none)"
        print(f"  seg {seg.seg_index}: {official} official tags, {total} total | "
              f"tags={seg.prosody_tags} | prefix={prefix}")

    # Check for invalid tags in prosody_tags
    from .schemas import ALL_PROSODY_TAGS
    invalid = []
    for seg in all_annotated:
        for tag in seg.prosody_tags:
            if tag not in ALL_PROSODY_TAGS:
                invalid.append((seg.seg_index, tag))

    if invalid:
        print(f"\n  WARNING: {len(invalid)} invalid official tags found:")
        for idx, tag in invalid:
            print(f"    seg {idx}: '{tag}' not in official set")
    else:
        print(f"\n  All prosody_tags are official S2-Pro tags.")

    return all_annotated


def step_p5_tts(annotated: list[AnnotatedSegment]) -> list[dict]:
    """Step 2: Run P5 TTS generation on annotated segments."""
    print("\n" + "=" * 60)
    print("[E2E] STEP 2: P5 — TTS Generation")
    print("=" * 60)

    results: list[dict] = []

    for seg in annotated:
        tts_text = _compose_tts_text(seg)
        voice = _resolve_voice(seg)

        print(f"\n  seg {seg.seg_index} ({seg.speaker}):")
        print(f"    voice: {voice}")
        print(f"    tts_text ({len(tts_text)} chars): {tts_text[:120]}{'...' if len(tts_text) > 120 else ''}")

        try:
            result = _synthesize_segment(seg, tts_text)
            print(f"    status: {result.status} | duration: {result.duration_s:.1f}s | "
                  f"attempts: {result.attempts}")
            results.append({
                "seg_index": result.seg_index,
                "speaker": result.speaker,
                "voice": voice,
                "status": result.status,
                "mp3_path": result.mp3_path,
                "duration_s": result.duration_s,
                "attempts": result.attempts,
                "tts_text": tts_text,
            })
        except Exception as e:
            print(f"    FAILED: {e}")
            results.append({
                "seg_index": seg.seg_index,
                "speaker": seg.speaker,
                "voice": voice,
                "status": "error",
                "mp3_path": "",
                "duration_s": 0,
                "attempts": 0,
                "error": str(e),
            })

    return results


def step_p7_verify(results: list[dict]) -> list[dict]:
    """Step 3: Verify generated audio via Whisper transcription + audio analysis."""
    print("\n" + "=" * 60)
    print("[E2E] STEP 3: P7 — Verification")
    print("=" * 60)

    verified: list[dict] = []

    for r in results:
        if r["status"] not in ("generated", "cached"):
            print(f"  seg {r['seg_index']}: SKIPPED (status={r['status']})")
            continue

        mp3_path = Path(r["mp3_path"])
        if not mp3_path.exists():
            print(f"  seg {r['seg_index']}: MP3 NOT FOUND at {mp3_path}")
            continue

        mp3_bytes = mp3_path.read_bytes()
        file_size_kb = len(mp3_bytes) / 1024
        duration = audio_duration_mp3(mp3_bytes)

        # Whisper transcription
        transcription = ""
        wer = -1.0
        try:
            import requests
            resp = requests.post(
                "http://localhost:8190/v1/audio/transcriptions",
                files={"file": (mp3_path.name, mp3_bytes, "audio/mpeg")},
                data={"language": "fr", "model": "large-v3-turbo"},
                headers={"Authorization": f"Bearer {os.getenv('WHISPER_API_KEY', '')}"},
                timeout=30,
            )
            if resp.status_code == 200:
                transcription = resp.json().get("text", "")
            else:
                transcription = f"(STT error {resp.status_code})"
        except Exception as e:
            transcription = f"(STT failed: {e})"

        # Load original text for comparison
        seg_data = json.loads(
            (OUTPUTS / "segments_v4.json").read_text(encoding="utf-8")
        )
        segs_list = seg_data if isinstance(seg_data, list) else seg_data["segments"]
        original_text = ""
        for s in segs_list:
            if s["seg_index"] == r["seg_index"]:
                original_text = s["text"]
                break

        # Simple WER calculation
        if transcription and original_text and not transcription.startswith("("):
            wer = _compute_wer(original_text, transcription)

        # Audio quality checks
        quality = {
            "has_audio": len(mp3_bytes) > 1000,
            "file_size_kb": round(file_size_kb, 1),
            "duration_s": round(duration, 1),
            "duration_plausible": 0.3 < duration < 120.0,
            "transcription": transcription[:200],
            "wer": round(wer, 3) if wer >= 0 else -1,
            "original_text": original_text[:200],
        }

        verdict = "PASS"
        reasons = []
        if not quality["has_audio"]:
            verdict = "FAIL"
            reasons.append("empty/tiny audio")
        if not quality["duration_plausible"]:
            verdict = "FAIL"
            reasons.append(f"suspicious duration {duration:.1f}s")
        if wer > 0.5:
            verdict = "NEEDS_REVIEW"
            reasons.append(f"high WER={wer:.2f}")

        quality["verdict"] = verdict
        quality["reasons"] = reasons

        print(f"\n  seg {r['seg_index']} ({r['speaker']}): {verdict}")
        print(f"    file: {file_size_kb:.1f}KB | duration: {duration:.1f}s")
        print(f"    WER: {wer:.3f}" if wer >= 0 else "    WER: N/A")
        print(f"    transcription: {transcription[:100]}")
        print(f"    original: {original_text[:100]}")
        if reasons:
            print(f"    reasons: {reasons}")

        verified.append({**r, **quality})

    return verified


def _compute_wer(reference: str, hypothesis: str) -> float:
    """Compute Word Error Rate between reference and hypothesis."""
    import re

    def normalize(text: str) -> list[str]:
        text = text.lower()
        text = re.sub(r"[^\w\s'àâéèêëïîôùûüçœæ-]", "", text)
        return text.split()

    ref_words = normalize(reference)
    hyp_words = normalize(hypothesis)

    if not ref_words:
        return 1.0

    # Levenshtein distance at word level
    n = len(ref_words)
    m = len(hyp_words)
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


def step_p7b_diarization(results: list[dict]) -> list[dict]:
    """Step 4: Diarization check on generated MP3s via Whisper WebUI."""
    print("\n" + "=" * 60)
    print("[E2E] STEP 4: P7b — Diarization")
    print("=" * 60)

    diag_results: list[dict] = []

    try:
        session = login_session()
    except Exception as e:
        print(f"  Cannot connect to Whisper WebUI: {e}")
        print("  Skipping diarization.")
        return diag_results

    for r in results:
        if r["status"] not in ("generated", "cached"):
            continue

        mp3_path = Path(r["mp3_path"])
        if not mp3_path.exists():
            continue

        seg_idx = r["seg_index"]
        speaker = r["speaker"]
        print(f"\n  seg {seg_idx} ({speaker}): diarizing...")

        try:
            diag = diarize_segment(str(mp3_path), seg_idx, session=session)
            n_speakers = diag["speaker_count"]
            dominant = diag["dominant_speaker"]
            elapsed = diag["elapsed_s"]
            print(f"    {n_speakers} speaker(s), dominant={dominant} ({elapsed:.1f}s)")

            if diag["segments"]:
                for seg in diag["segments"][:3]:
                    print(f"      {seg['speaker']}: [{seg['start']:.1f}-{seg['end']:.1f}s] "
                          f"{seg['text'][:60]}")

            diag_results.append(diag)
        except Exception as e:
            print(f"    FAILED: {e}")
            diag_results.append({
                "seg_index": seg_idx,
                "mp3_path": str(mp3_path),
                "detected_speakers": [],
                "segments": [],
                "speaker_count": 0,
                "dominant_speaker": "",
                "elapsed_s": 0.0,
                "error": str(e),
            })

    # Summary
    successful = [d for d in diag_results if not d.get("error")]
    if successful:
        from collections import Counter
        all_counts = Counter(d["speaker_count"] for d in successful)
        print(f"\n  Diarization summary: {len(successful)}/{len(diag_results)} successful")
        print(f"  Speaker distribution: {dict(all_counts)}")
    else:
        print(f"\n  No successful diarization results.")

    return diag_results


def run_e2e(force: bool = False):
    """Run full E2E test pipeline."""
    # Ensure .env is loaded (may not happen when called from __main__ after module imports)
    _genai_dir = Path(__file__).resolve().parents[3]
    load_dotenv(_genai_dir / ".env", override=False)

    print("=" * 60)
    print("[E2E] Audiobook Pipeline v4 — End-to-End Validation")
    print("=" * 60)
    print(f"Test segments: {TEST_SEGMENTS}")
    print(f"Total: {len(TEST_SEGMENTS)} segments")

    # Load test data
    segments, contexts = load_test_data()

    # Step 1: P4 annotation
    annotated = step_p4_annotation(segments, contexts)

    # Step 2: P5 TTS
    tts_results = step_p5_tts(annotated)

    # Step 3: P7 verification
    verified = step_p7_verify(tts_results)

    # Step 4: P7b diarization
    diarization_results = step_p7b_diarization(tts_results)

    # Summary
    print("\n" + "=" * 60)
    print("[E2E] SUMMARY")
    print("=" * 60)

    passed = sum(1 for v in verified if v.get("verdict") == "PASS")
    needs_review = sum(1 for v in verified if v.get("verdict") == "NEEDS_REVIEW")
    failed = sum(1 for v in verified if v.get("verdict") == "FAIL")
    skipped = len(TEST_SEGMENTS) - len(verified)

    print(f"  PASS: {passed}")
    print(f"  NEEDS_REVIEW: {needs_review}")
    print(f"  FAIL: {failed}")
    print(f"  SKIPPED: {skipped}")
    print(f"  Total: {len(TEST_SEGMENTS)}")

    # Save full results
    results_path = OUTPUTS / "e2e_results.json"
    results_path.write_text(
        json.dumps(verified, indent=2, ensure_ascii=False, default=str),
        encoding="utf-8",
    )
    print(f"\n  Results saved to: {results_path}")

    # Save diarization results
    if diarization_results:
        diag_path = OUTPUTS / "e2e_diarization.json"
        diag_path.write_text(
            json.dumps(diarization_results, indent=2, ensure_ascii=False, default=str),
            encoding="utf-8",
        )
        print(f"  Diarization saved to: {diag_path}")

    # Compile MP3 list for human review
    mp3_files = [v["mp3_path"] for v in verified if v.get("mp3_path") and Path(v["mp3_path"]).exists()]
    if mp3_files:
        print(f"\n  MP3 files for human review ({len(mp3_files)}):")
        for p in mp3_files:
            print(f"    {p}")

    return verified


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    force = "--force" in sys.argv
    run_e2e(force=force)
