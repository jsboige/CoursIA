"""P5 — TTS Generation for the v4 audiobook pipeline.

Generates MP3 audio for each annotated segment using FishAudio S2-Pro
with cloned voice references from P1.

Uses concurrent batch processing (ThreadPoolExecutor) to saturate the
FishAudio server and reduce generation time from ~19h (sequential) to
~3-4h.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import re

from dotenv import load_dotenv

from .schemas import AnnotatedSegment, AnnotatedBatch, TTSResult
from .p1_voice_cloning import SPEAKER_TO_VOICE, FIGURANT_RAW_VOICE_OVERRIDE
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
_MAX_TTS_CHARS = 500  # FishAudio OOMs on long composed texts (>1000 chars)
_BATCH_SIZE = 8
_MAX_WORKERS = 1  # FishAudio S2-Pro is single-threaded; concurrent requests cause timeouts

# Mapping non-official tags → closest official S2-Pro tag
# S2-Pro only reliably handles the 29 official tags. Free-form tags
# (French, adverbs, multi-word descriptions) are silently ignored.
_NON_OFFICIAL_TAG_MAP: dict[str, str] = {
    "firmly": "emphasis",
    "firm": "emphasis",
    "mockingly": "emphasis",
    "indignantly": "angry",
    "angrily": "angry",
    "sadly": "sad",
    "excitedly": "excited",
    "gently": "soft voice",
    "timidly": "soft voice",
    "coldly": "low voice",
    "speaking slowly": "pause",
    "speaking quickly": "excited",
    "taking a breath": "inhale",
    "in a cold tone": "low voice",
    "in a warm tone": "soft voice",
    "in a smooth, ingratiating tone": "soft voice",
}


def _text_hash(text: str) -> str:
    return hashlib.md5(text.encode()).hexdigest()[:12]


def _compose_tts_text(seg: AnnotatedSegment) -> str:
    """Compose the final TTS text with context prefix and dramatic prompt.

    FishAudio S2-Pro interprets [bracketed] text as voice instructions.
    S2-Pro ONLY reliably handles its 29 official tags. French text and
    free-form descriptions in brackets are silently ignored.
    A space after ] is MANDATORY — ]X causes the tag to be ignored.

    Composition order:
    1. Official S2-Pro tag(s) mapped from tts_context_prefix / dramatic context
    2. The annotated text with sanitized inline tags
    """
    parts: list[str] = []

    # Collect official S2-Pro tags from context prefix and dramatic prompt
    tags: list[str] = []

    if seg.tts_context_prefix:
        tags.extend(_extract_official_tags(seg.tts_context_prefix))

    if seg.dramatic_prompt and seg.type != "narration":
        tags.extend(_extract_official_tags(seg.dramatic_prompt))

    # Deduplicate tags while preserving order
    seen: set[str] = set()
    unique_tags: list[str] = []
    for t in tags:
        if t not in seen:
            seen.add(t)
            unique_tags.append(t)

    # Max 2 tags to avoid confusing the model
    if unique_tags:
        parts.append(" ".join(f"[{t}]" for t in unique_tags[:2]))

    base_text = seg.fishaudio_text or seg.annotated_text or seg.text
    base_text = _normalize_tags(base_text)

    parts.append(base_text)
    result = " ".join(parts)

    # CRITICAL: ensure space after every ] — S2-Pro ignores tags without trailing space
    result = re.sub(r"\](?=\S)", "] ", result)

    if len(result) > _MAX_TTS_CHARS:
        result = result[:_MAX_TTS_CHARS].rsplit(" ", 1)[0] + "..."

    return result


def _extract_official_tags(text: str) -> list[str]:
    """Extract and map tags to official S2-Pro tags from context text.

    Checks both the official tag set and the non-official mapping.
    Returns a list of official tag names (without brackets).
    """
    from .schemas import ALL_PROSODY_TAGS

    found: list[str] = []
    # Match [bracketed] content
    for match in re.finditer(r"\[([^\]]+)\]", text):
        content = match.group(1).strip().lower()
        # Direct official tag?
        if content in ALL_PROSODY_TAGS:
            found.append(content)
        # Mapped non-official tag?
        elif content in _NON_OFFICIAL_TAG_MAP:
            mapped = _NON_OFFICIAL_TAG_MAP[content]
            if mapped in ALL_PROSODY_TAGS:
                found.append(mapped)
    return found


def _normalize_tags(text: str) -> str:
    """Normalize all inline tags in text to official S2-Pro tags with space after ].

    1. Convert (parenthetical voice instructions) to [brackets]
    2. Map non-official [tags] to closest official equivalent
    3. Ensure space after every ]
    """
    text = _sanitize_voice_instructions(text)

    def _normalize_one(match: re.Match) -> str:
        content = match.group(1).strip()
        lower = content.lower()
        from .schemas import ALL_PROSODY_TAGS
        if lower in ALL_PROSODY_TAGS:
            return f"[{lower}] "
        if lower in _NON_OFFICIAL_TAG_MAP:
            mapped = _NON_OFFICIAL_TAG_MAP[lower]
            if mapped in ALL_PROSODY_TAGS:
                return f"[{mapped}] "
        # Unknown/free-form tag — strip it entirely (S2-Pro ignores these)
        return ""

    text = re.sub(r"\[([^\]]+)\]", _normalize_one, text)
    return text


def _sanitize_voice_instructions(text: str) -> str:
    """Convert parenthetical voice instructions to FishAudio S2-Pro bracket syntax.

    S2-Pro speaks parenthetical text literally. Voice instructions must be
    in [brackets]. This converts known instruction patterns from legacy outputs:
      (whispering) -> [whispering]
      (sad) -> [sad]
      (laughing) -> [laughing]
    Preserves legitimate parenthetical content in the narrative text.
    """
    _KNOWN_INSTRUCTIONS = [
        # Official S2-Pro tags (from fish.audio blog)
        # Breathing & vocal reactions
        "clears throat", "inhale", "inhalation", "exhale", "sigh",
        "panting", "breathing", "gasp",
        # Vocal sounds
        "groan", "moaning", "sobbing", "crying", "laughing",
        "chuckling", "giggle",
        # Pacing
        "pause", "short pause", "long pause",
        # Voice style
        "whispering", "whispering voice", "soft voice", "low voice",
        "loud voice", "shouting",
        # Emotion (3 official + free-form)
        "excited", "angry", "sad",
        # Other official
        "emphasis", "rustling sound",
        # Common free-form descriptions (S2-Pro accepts natural language)
        "happy", "calm", "nervous", "confident", "surprised",
        "scared", "worried", "sarcastic", "contemptuous", "anxious",
        "indifferent", "uncertain", "confused", "disappointed",
        "regretful", "guilty", "hopeful", "nostalgic", "lonely",
        "bored", "determined", "resigned", "compassionate",
        "disdainful", "empathetic",
        # Legacy patterns from previous pipeline runs (backward compat)
        "in a cold tone", "in a warm tone",
        "in a smooth, ingratiating tone",
        "indignantly", "mockingly", "angrily",
        "sadly", "nervously", "excitedly",
        "gently", "firmly", "timidly",
        "taking a breath", "speaking slowly", "speaking quickly",
    ]
    result = text
    for instr in _KNOWN_INSTRUCTIONS:
        result = result.replace(f"({instr})", f"[{instr}]")
    return result


def _resolve_voice(seg: AnnotatedSegment) -> str:
    """Resolve the FishAudio reference_id for a segment.

    For figurants, checks FIGURANT_RAW_VOICE_OVERRIDE using speaker_raw
    to pick a more appropriate voice than the default gruff male.
    """
    if seg.speaker == "figurant" and seg.speaker_raw:
        override = FIGURANT_RAW_VOICE_OVERRIDE.get(seg.speaker_raw.lower().strip())
        if override:
            return override
    return SPEAKER_TO_VOICE.get(seg.speaker, "v4_narrator_male_neutral")


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
    reference_id = _resolve_voice(seg)
    seed = 42 + seg.seg_index
    mp3_path = TTS_DIR / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"
    current_hash = _text_hash(fishaudio_text)

    if mp3_path.exists():
        # Check if TTS text changed since last generation
        cached_hash = ""
        results_path = BASE_DIR / "outputs" / "tts_results.json"
        if results_path.exists():
            try:
                results_data = json.loads(results_path.read_text(encoding="utf-8"))
                for r in results_data:
                    if r.get("seg_index") == seg.seg_index:
                        cached_hash = r.get("text_hash", "")
                        break
            except (json.JSONDecodeError, KeyError):
                pass

        if cached_hash == current_hash:
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
                text_hash=current_hash,
            )
        # Text changed — delete stale MP3 and regenerate
        print(f"    [P5] seg {seg.seg_index}: text changed, regenerating")
        mp3_path.unlink(missing_ok=True)

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
            "timeout": 600,
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
            text_hash=current_hash,
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
        text_hash=current_hash,
    )


def _synthesize_batch(
    segments: list[tuple[AnnotatedSegment, str]],
) -> list[TTSResult]:
    """Process a batch of segments concurrently.

    Delegates cache checking to _synthesize_segment (which does text-hash
    invalidation). Only truly cached segments skip the thread pool.
    """
    results: dict[int, TTSResult] = {}

    # Quick first pass: check which are truly cached (hash matches)
    to_generate: list[tuple[int, AnnotatedSegment, str]] = []
    for seg, text in segments:
        reference_id = _resolve_voice(seg)
        seed = 42 + seg.seg_index
        mp3_path = TTS_DIR / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"
        current_hash = _text_hash(text)

        if mp3_path.exists():
            # Check hash from previous results
            cached_hash = ""
            results_path = BASE_DIR / "outputs" / "tts_results.json"
            if results_path.exists():
                try:
                    results_data = json.loads(results_path.read_text(encoding="utf-8"))
                    for r in results_data:
                        if r.get("seg_index") == seg.seg_index:
                            cached_hash = r.get("text_hash", "")
                            break
                except (json.JSONDecodeError, KeyError):
                    pass

            if cached_hash == current_hash:
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
                    text_hash=current_hash,
                )
                continue
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
                    text_hash="",
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
            (batch.segments[i], _compose_tts_text(batch.segments[i]))
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
