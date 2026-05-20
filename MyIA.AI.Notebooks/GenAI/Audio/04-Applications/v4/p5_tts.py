"""P5 — TTS Generation for the v4 audiobook pipeline.

Generates MP3 audio for each annotated segment using FishAudio S2-Pro
with cloned voice references from P1.

Uses concurrent batch processing (ThreadPoolExecutor) to saturate the
FishAudio server and reduce generation time from ~19h (sequential) to
~3-4h.
"""
from __future__ import annotations

import json
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

from dotenv import load_dotenv

from .schemas import AnnotatedSegment, AnnotatedBatch, TTSResult
from .p1_voice_cloning import SPEAKER_TO_VOICE
from .fishaudio_client import (
    fishaudio_tts,
    thermal_wait,
    audio_duration_mp3,
    fishaudio_tts_batch,
    OUTPUT_DIR,
)

BASE_DIR = Path(__file__).parent
TTS_DIR = OUTPUT_DIR
TTS_DIR.mkdir(exist_ok=True, parents=True)

_MAX_WORDS_PER_CALL = 55
_BATCH_SIZE = 8
_MAX_WORKERS = 4


def _split_long_text(text: str, max_words: int = _MAX_WORDS_PER_CALL) -> list[str]:
    """Split text at sentence boundaries if it exceeds max_words."""
    words = text.split()
    if len(words) <= max_words:
        return [text]

    chunks: list[str] = []
    current: list[str] = []
    for word in words:
        current.append(word)
        if len(current) >= max_words and word.endswith((".", "!", "?", ";")):
            chunks.append(" ".join(current))
            current = []
    if current:
        if chunks:
            chunks[-1] += " " + " ".join(current)
        else:
            chunks.append(" ".join(current))
    return chunks


def _concat_audio_parts(audio_parts: list[bytes]) -> bytes:
    """Concatenate multiple MP3 chunks into a single MP3."""
    if len(audio_parts) == 1:
        return audio_parts[0]

    try:
        import io

        from pydub import AudioSegment

        combined = AudioSegment.from_file(
            io.BytesIO(audio_parts[0]), format="mp3"
        )
        for part in audio_parts[1:]:
            combined += AudioSegment.from_file(io.BytesIO(part), format="mp3")
        buf = io.BytesIO()
        combined.export(buf, format="mp3", bitrate="192k")
        return buf.getvalue()
    except ImportError:
        return b"".join(audio_parts)


def _synthesize_segment(seg: AnnotatedSegment, fishaudio_text: str) -> TTSResult:
    """Synthesize a single segment, handling long text by splitting."""
    reference_id = SPEAKER_TO_VOICE.get(seg.speaker, "v4_narrator_male_neutral")
    seed = 42 + seg.seg_index
    mp3_path = TTS_DIR / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"

    if mp3_path.exists():
        size = mp3_path.stat().st_size
        duration = audio_duration_mp3(mp3_path.read_bytes()) if size > 0 else 0.0
        return TTSResult(
            seg_index=seg.seg_index,
            speaker=seg.speaker,
            reference_id=reference_id,
            mp3_path=str(mp3_path),
            duration_s=duration,
            seed=seed,
            status="cached",
            attempts=0,
        )

    chunks = _split_long_text(fishaudio_text)

    # Build TTS requests for each chunk
    tts_requests = []
    for chunk in chunks:
        tts_requests.append({
            "text": chunk,
            "reference_id": reference_id,
            "seed": seed,
            "temperature": 0.7,
            "top_p": 0.9,
            "format": "mp3",
            "timeout": 300,
        })

    # If single chunk, use direct call
    if len(tts_requests) == 1:
        audio = fishaudio_tts(**tts_requests[0])
        attempts = 1
        if audio is None:
            thermal_wait()
            audio = fishaudio_tts(**tts_requests[0])
            attempts = 2
        audio_parts = [audio] if audio else []
    else:
        # Multi-chunk: use batch for chunks
        audio_results = fishaudio_tts_batch(tts_requests, max_workers=2)
        attempts = len(tts_requests)

        # Retry failed chunks
        failed_indices = [i for i, a in enumerate(audio_results) if a is None]
        if failed_indices:
            thermal_wait()
            retry_results = fishaudio_tts_batch(
                [tts_requests[i] for i in failed_indices], max_workers=2
            )
            attempts += len(failed_indices)
            for j, orig_idx in enumerate(failed_indices):
                audio_results[orig_idx] = retry_results[j]

        audio_parts = [a for a in audio_results if a is not None]

    if not audio_parts:
        return TTSResult(
            seg_index=seg.seg_index,
            speaker=seg.speaker,
            reference_id=reference_id,
            mp3_path="",
            duration_s=0.0,
            seed=seed,
            status="failed",
            attempts=attempts,
        )

    final_audio = _concat_audio_parts(audio_parts)
    mp3_path.write_bytes(final_audio)
    duration = audio_duration_mp3(final_audio)

    return TTSResult(
        seg_index=seg.seg_index,
        speaker=seg.speaker,
        reference_id=reference_id,
        mp3_path=str(mp3_path),
        duration_s=duration,
        seed=seed,
        status="generated",
        attempts=attempts,
    )


def _synthesize_batch(
    segments: list[tuple[AnnotatedSegment, str]],
) -> list[TTSResult]:
    """Process a batch of segments concurrently.

    Filters out cached segments first, then dispatches uncached
    segments to the TTS server via ThreadPoolExecutor.
    """
    results: dict[int, TTSResult] = {}

    # Separate cached vs uncached
    to_generate: list[tuple[int, AnnotatedSegment, str]] = []
    for seg, text in segments:
        reference_id = SPEAKER_TO_VOICE.get(seg.speaker, "v4_narrator_male_neutral")
        seed = 42 + seg.seg_index
        mp3_path = TTS_DIR / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"

        if mp3_path.exists():
            size = mp3_path.stat().st_size
            duration = audio_duration_mp3(mp3_path.read_bytes()) if size > 0 else 0.0
            results[seg.seg_index] = TTSResult(
                seg_index=seg.seg_index,
                speaker=seg.speaker,
                reference_id=reference_id,
                mp3_path=str(mp3_path),
                duration_s=duration,
                seed=seed,
                status="cached",
                attempts=0,
            )
        else:
            to_generate.append((seg.seg_index, seg, text))

    if not to_generate:
        return [results[seg.seg_index] for seg, _ in segments]

    # Check thermal before batch
    thermal_wait()

    # Generate uncached segments concurrently
    def _gen(item: tuple[int, AnnotatedSegment, str]) -> TTSResult:
        _, seg, text = item
        return _synthesize_segment(seg, text)

    with ThreadPoolExecutor(max_workers=_MAX_WORKERS) as pool:
        futures = {pool.submit(_gen, item): item[0] for item in to_generate}
        for future in as_completed(futures):
            seg_idx = futures[future]
            try:
                results[seg_idx] = future.result()
            except Exception as exc:
                results[seg_idx] = TTSResult(
                    seg_index=seg_idx,
                    speaker="",
                    reference_id="",
                    mp3_path="",
                    duration_s=0.0,
                    seed=0,
                    status="failed",
                    attempts=0,
                )

    return [results[seg.seg_index] for seg, _ in segments]


def run(force: bool = False) -> Path:
    """Run P5 — TTS generation with concurrent batching.

    Returns path to tts_results.json.
    """
    results_path = BASE_DIR / "outputs" / "tts_results.json"
    annotated_path = BASE_DIR / "outputs" / "annotated_v4.json"

    if not annotated_path.exists():
        raise FileNotFoundError(
            f"annotated_v4.json not found: {annotated_path}\n"
            "Run P4 (annotation) first."
        )

    if results_path.exists() and not force:
        print(f"[P5] Cached: {results_path}")
        return results_path

    print(f"[P5] Running TTS generation (batch_size={_BATCH_SIZE}, workers={_MAX_WORKERS})...")

    batch = AnnotatedBatch.model_validate_json(
        annotated_path.read_text(encoding="utf-8")
    )
    print(f"  Loaded {len(batch.segments)} annotated segments")

    results: list[TTSResult] = []
    generated = 0
    cached = 0
    failed = 0

    # Process in batches for progress reporting
    total = len(batch.segments)
    for batch_start in range(0, total, _BATCH_SIZE):
        batch_end = min(batch_start + _BATCH_SIZE, total)
        batch_segs = [
            (batch.segments[i], batch.segments[i].fishaudio_text
             or batch.segments[i].annotated_text
             or batch.segments[i].text)
            for i in range(batch_start, batch_end)
        ]

        batch_results = _synthesize_batch(batch_segs)
        results.extend(batch_results)

        for r in batch_results:
            if r.status == "cached":
                cached += 1
            elif r.status == "generated":
                generated += 1
            else:
                failed += 1

        if generated > 0 and generated % 50 < _BATCH_SIZE:
            print(f"  [P5] Progress: {batch_end}/{total} "
                  f"(gen={generated}, cached={cached}, fail={failed})")

    results_path.write_text(
        json.dumps([r.model_dump() for r in results], indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    total_duration = sum(r.duration_s for r in results if r.duration_s > 0)
    print(f"[P5] Done: {results_path}")
    print(f"  Generated: {generated}, Cached: {cached}, Failed: {failed}")
    print(f"  Total duration: {total_duration:.1f}s ({total_duration/60:.1f}min)")

    return results_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
