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
    OUTPUT_DIR,
)

BASE_DIR = Path(__file__).parent
TTS_DIR = OUTPUT_DIR
TTS_DIR.mkdir(exist_ok=True, parents=True)

_MAX_TTS_CHARS = 500  # Truncation limit for the composed text
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
    S2-Pro accepts both official tags and free-form natural language in brackets.
    A space after ] is MANDATORY — ]X causes the tag to be ignored.

    Composition order:
    1. Voice instruction prefix from tts_context_prefix (natural language)
    2. The annotated text with all tags preserved (official + free-form)
    """
    parts: list[str] = []

    # Use tts_context_prefix directly as voice instruction.
    # S2-Pro accepts natural language in brackets — no need to extract
    # official tags. The prefix is the PRIMARY source of prosody diversity.
    if seg.tts_context_prefix:
        prefix = seg.tts_context_prefix.strip()
        # Strip surrounding brackets if present (we add our own)
        if prefix.startswith("[") and prefix.endswith("]"):
            prefix = prefix[1:-1].strip()
        parts.append(f"[{prefix}] ")

    base_text = seg.fishaudio_text or seg.annotated_text or seg.text
    base_text = _normalize_tags(base_text)

    # Inject mid-segment prosody tags for long texts (>200 chars)
    # S2-Pro tags affect what follows them, so inserting at punctuation
    # boundaries creates natural variation within a single segment.
    if len(base_text) > 200:
        base_text = _inject_mid_segment_tags(base_text)

    parts.append(base_text)
    result = " ".join(parts)

    # CRITICAL: ensure space after every ] — S2-Pro ignores tags without trailing space
    result = re.sub(r"\](?=\S)", "] ", result)

    if len(result) > _MAX_TTS_CHARS:
        result = result[:_MAX_TTS_CHARS].rsplit(" ", 1)[0] + "..."

    return result


def _inject_mid_segment_tags(text: str) -> str:
    """Insert prosody variation tags at natural punctuation boundaries.

    S2-Pro tags affect what FOLLOWS them. By inserting tags at sentence
    boundaries, we create prosody variation within a single long segment.
    Strategy:
    - After semicolons: [short pause] (natural breath point)
    - Before exclamations: [emphasis]
    - After ellipsis (...): [pause] (dramatic beat)
    - Every ~3rd sentence boundary: [short pause] (pacing variation)
    Only injects if there isn't already a tag nearby (within 20 chars).
    """
    result = text
    injections: list[tuple[int, str]] = []

    # Count existing tags to avoid over-tagging
    existing_tag_count = len(re.findall(r"\[[^\]]+\]", text))

    # After semicolons followed by space: [short pause]
    for m in re.finditer(r";\s+", result):
        pos = m.end()
        if not _has_nearby_tag(result, pos):
            injections.append((pos, "[short pause] "))

    # After ellipsis: [pause]
    for m in re.finditer(r"\.\.\.\s*", result):
        pos = m.end()
        if not _has_nearby_tag(result, pos):
            injections.append((pos, "[pause] "))

    # Before exclamation marks (on sentences ending with !):
    for m in re.finditer(r"!\s", result):
        # Insert emphasis before the exclamation sentence
        sentence_start = result.rfind(". ", 0, m.start())
        if sentence_start == -1:
            sentence_start = 0
        else:
            sentence_start += 2
        if not _has_nearby_tag(result, sentence_start):
            injections.append((sentence_start, "[emphasis] "))

    # Apply injections in reverse order to preserve positions
    for pos, tag in sorted(injections, key=lambda x: -x[0]):
        total_tags = existing_tag_count + len(injections)
        if total_tags <= 8:  # Cap total tags to avoid over-tagging
            result = result[:pos] + tag + result[pos:]

    return result


def _has_nearby_tag(text: str, pos: int, window: int = 25) -> bool:
    """Check if there's already a [tag] within `window` chars of position."""
    start = max(0, pos - window)
    end = min(len(text), pos + window)
    return bool(re.search(r"\[[^\]]+\]", text[start:end]))


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
    """Normalize inline tags in text for FishAudio S2-Pro.

    1. Convert (parenthetical voice instructions) to [brackets]
    2. Map known non-official tags to closest official equivalent
    3. KEEP free-form / natural-language tags — S2-Pro accepts them
    4. Ensure space after every ]
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
        # Free-form / natural-language tag — S2-Pro accepts these.
        # Preserve them as-is (they are the primary source of prosody diversity).
        return f"[{content}] "

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


_MAX_CHUNK_CHARS = 220  # ~40 words in French; safe for FishAudio with tags


def _split_long_text(text: str, max_chars: int = _MAX_CHUNK_CHARS) -> list[str]:
    """Split text into chunks safe for FishAudio S2-Pro (~220 chars each).

    Multi-strategy splitting for French text that may lack sentence-ending
    punctuation at convenient positions:
      1. Prefer sentence boundaries (. ! ? ;)
      2. Fall back to commas/colons
      3. Last resort: split at space nearest to target length
    """
    if len(text) <= max_chars:
        return [text]

    chunks: list[str] = []
    remaining = text

    while len(remaining) > max_chars:
        # Find the best split point in the range [max_chars*0.5, max_chars*1.2]
        search_start = max_chars // 2
        search_end = min(len(remaining), int(max_chars * 1.2))
        window = remaining[search_start:search_end]

        split_pos = -1

        # Strategy 1: sentence-ending punctuation (. ! ? ;)
        for punct in (". ", "! ", "? ", "; "):
            idx = window.rfind(punct)
            if idx != -1:
                candidate = search_start + idx + len(punct)
                if split_pos == -1 or candidate > split_pos:
                    split_pos = candidate

        # Strategy 2: comma or colon (sub-sentence break)
        if split_pos == -1:
            for punct in (", ", ": ", " — ", " – "):
                idx = window.rfind(punct)
                if idx != -1:
                    candidate = search_start + idx + len(punct)
                    if split_pos == -1 or candidate > split_pos:
                        split_pos = candidate

        # Strategy 3: nearest space to max_chars
        if split_pos == -1:
            space_pos = remaining.rfind(" ", search_start, search_end)
            if space_pos != -1:
                split_pos = space_pos + 1
            else:
                split_pos = max_chars

        chunks.append(remaining[:split_pos].strip())
        remaining = remaining[split_pos:].strip()

    if remaining:
        chunks.append(remaining)

    return chunks if chunks else [text]


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

    # Extract the leading tag prefix (e.g. "[emphasis] ") to prepend to each chunk.
    # This ensures every chunk carries the segment's prosody tag.
    tag_prefix = ""
    tag_match = re.match(r"(\[[^\]]+\]\s+)+", fishaudio_text)
    if tag_match:
        tag_prefix = tag_match.group(0)
        # Remove tag prefix from chunks (it's only in the first one)
        if chunks:
            chunks[0] = chunks[0][len(tag_prefix):].strip()

    # Build TTS requests for each chunk, prepending the tag prefix
    tts_requests = []
    for chunk in chunks:
        chunk_text = f"{tag_prefix}{chunk}" if tag_prefix else chunk
        tts_requests.append({
            "text": chunk_text,
            "reference_id": reference_id,
            "seed": seed,
            "temperature": 0.7,
            "top_p": 0.9,
            "format": "mp3",
            "timeout": 120,
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
        # Multi-chunk: synthesize SEQUENTIALLY (FishAudio is single-threaded)
        audio_results: list[bytes | None] = []
        attempts = 0
        for req in tts_requests:
            audio = fishaudio_tts(**req)
            attempts += 1
            if audio is None:
                thermal_wait()
                audio = fishaudio_tts(**req)
                attempts += 1
            audio_results.append(audio)

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
