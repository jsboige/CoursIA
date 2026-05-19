"""P5 — TTS Generation for the v4 audiobook pipeline.

Generates MP3 audio for each annotated segment using FishAudio S2-Pro
with cloned voice references from P1.
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import AnnotatedSegment, AnnotatedBatch, TTSResult
from .p1_voice_cloning import SPEAKER_TO_VOICE
from .fishaudio_client import (
    fishaudio_tts,
    thermal_wait,
    audio_duration_mp3,
    OUTPUT_DIR,
)

BASE_DIR = Path(__file__).parent
TTS_DIR = OUTPUT_DIR
TTS_DIR.mkdir(exist_ok=True, parents=True)

_MAX_WORDS_PER_CALL = 55


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

    thermal_wait()
    chunks = _split_long_text(fishaudio_text)
    audio_parts: list[bytes] = []
    attempts = 0

    for chunk in chunks:
        audio = fishaudio_tts(
            text=chunk,
            reference_id=reference_id,
            seed=seed,
            temperature=0.7,
            top_p=0.9,
            format="mp3",
            timeout=300,
        )
        attempts += 1
        if audio:
            audio_parts.append(audio)
        else:
            # Retry once
            thermal_wait()
            audio = fishaudio_tts(
                text=chunk,
                reference_id=reference_id,
                seed=seed,
                temperature=0.7,
                top_p=0.9,
                format="mp3",
                timeout=300,
            )
            attempts += 1
            if audio:
                audio_parts.append(audio)

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

    # Concatenate chunks if split
    final_audio = audio_parts[0]
    if len(audio_parts) > 1:
        try:
            from pydub import AudioSegment
            combined = AudioSegment.from_mp3(AudioSegment.from_file(
                __import__("io").BytesIO(audio_parts[0]), format="mp3"
            ))
            for part in audio_parts[1:]:
                combined += AudioSegment.from_file(
                    __import__("io").BytesIO(part), format="mp3"
                )
            buf = __import__("io").BytesIO()
            combined.export(buf, format="mp3", bitrate="192k")
            final_audio = buf.getvalue()
        except ImportError:
            final_audio = b"".join(audio_parts)

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


def run(force: bool = False) -> Path:
    """Run P5 — TTS generation. Returns path to tts_results.json."""
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

    print("[P5] Running TTS generation...")

    batch = AnnotatedBatch.model_validate_json(
        annotated_path.read_text(encoding="utf-8")
    )
    print(f"  Loaded {len(batch.segments)} annotated segments")

    results: list[TTSResult] = []
    generated = 0
    cached = 0
    failed = 0

    for i, seg in enumerate(batch.segments):
        fishaudio_text = seg.fishaudio_text or seg.annotated_text or seg.text

        result = _synthesize_segment(seg, fishaudio_text)
        results.append(result)

        if result.status == "cached":
            cached += 1
        elif result.status == "generated":
            generated += 1
            if generated % 50 == 0:
                print(f"  [P5] Progress: {generated}/{len(batch.segments)}")
        else:
            failed += 1
            print(f"  [P5] FAILED seg {seg.seg_index}: {seg.speaker}")

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
