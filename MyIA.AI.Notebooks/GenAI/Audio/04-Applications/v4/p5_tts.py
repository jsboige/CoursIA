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
import logging
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import re

logger = logging.getLogger(__name__)

from dotenv import load_dotenv

from .schemas import AnnotatedSegment, AnnotatedBatch, TTSResult
from .p1_voice_cloning import SPEAKER_TO_VOICE, FIGURANT_RAW_VOICE_OVERRIDE
from .fishaudio_client import (
    fishaudio_tts,
    thermal_wait,
    thermal_backoff,
    audio_duration_mp3,
    OUTPUT_DIR,
)

BASE_DIR = Path(__file__).parent
TTS_DIR = OUTPUT_DIR
TTS_DIR.mkdir(exist_ok=True, parents=True)

_MAX_TTS_CHARS = 500  # Truncation limit for the composed text
_BATCH_SIZE = 8
_MAX_WORKERS = 1  # FishAudio S2-Pro is single-threaded; concurrent requests cause timeouts
_MAX_PREFIX_TAGS = 4  # Max prosody tags prepended before segment text.
# S2-Pro processes bracketed tags sequentially; beyond ~4, later tags tend to
# be ignored or to degrade prosody quality (observed during Act 2 multi-tag
# testing, session 25/05/2026). The cap also keeps the prefix short enough
# that S2-Pro interprets it as instruction rather than vocalizing it.

# F1 (Issue #1600): S2-Pro accepts free-form natural language in [brackets]
# (per fish.audio blog). Collapsing 16 descriptive tags to 4 official tags
# destroyed prosody diversity. Keep empty — free-form tags pass through.
_NON_OFFICIAL_TAG_MAP: dict[str, str] = {}


def _text_hash(text: str) -> str:
    return hashlib.md5(text.encode()).hexdigest()[:12]


# ---------------------------------------------------------------------------
# F5 — Dramatic prompt translation (prosody regression fix)
# ---------------------------------------------------------------------------
# P4 produces rich French dramatic prompts (avg 186 chars) like:
#   "Le récit s'ouvre sobrement... Installez une voix posée, sans émotion"
# S2-Pro vocalizes French text in brackets (WER #1277/#1485). We translate
# these prompts to short English instructions S2-Pro interprets rather than
# reads aloud.
#
# Two strategies:
#   1. LLM batch translation (preferred, cached in dramatic_translations.json)
#   2. Keyword-based heuristic fallback (no LLM cost, deterministic)

# Global cache: seg_index → English instruction string
_dramatic_translations: dict[int, str] = {}

# LLM batch size for translation (gpt-4o-mini, cheap)
_TRANSLATION_BATCH_SIZE = 40

_DRAMATIC_KEYWORD_MAP: list[tuple[list[str], str]] = [
    # (French keywords, English S2-Pro instruction)
    # Order matters: first match wins. More specific patterns first.
    (["ironie", "ironique", "sarcast"], "ironic and dry, with a smirk"),
    (["murmur", "chuchot"], "whispering, conspiratorial"),
    (["suspen", "attente", "retenue"], "building suspense, slow and tense"),
    (["menace", "menaç", "violent", "sauvage"], "dark and menacing, low and slow"),
    (["colère", "courrouc", "furieux", "rage"], "angry, voice rising"),
    (["peur", "terrif", "effroi", "angoiss", "panique"], "fearful, voice trembling"),
    (["triste", "tristess", "désol", "chagrin", "mélancol"], "sad, voice dropping"),
    (["douleur", "souffran", "déchir"], "pained, voice breaking"),
    (["amer", "amertume", "rancun", "rancœur"], "bitter and resentful"),
    (["rage", "fureur"], "furious, barely contained"),
    (["tendu", "tension", "nerf"], "tense, voice tight"),
    (["froid", "glac", "glacé"], "cold and detached, clinical"),
    (["calme", "serein", "paisib", "apais"], "calm and measured, steady pace"),
    (["lent", "lenteur", "ralenti"], "slow and deliberate, weighing each word"),
    (["douc", "tendre", "affectueux"], "soft and gentle, warm tone"),
    (["fort", "puissant", "violemment"], "loud and forceful, commanding"),
    (["posée", "sobriété", " sobre"], "composed and neutral, even pace"),
    (["fatigu", "épuis", "las", "lass"], "weary, voice trailing off"),
    (["résign", "abandon", "défait"], "resigned, quiet acceptance"),
    (["excit", "vif", "animé", "exalt"], "excited, quickening pace"),
    (["sec", "sèchement", "coupant"], "dry and clipped, no warmth"),
    (["chaud", "chaleureux", "bonhom"], "warm and friendly, inviting"),
    (["lourd", "pesant", "accabl"], "heavy and oppressive, slow rhythm"),
    (["emphat", "solennel"], "emphatic and deliberate, each word clear"),
    (["moqueur", "railleur", "dédain", "mépris"], "mocking and contemptuous"),
    (["souffl", "essouffl"], "breathless, hurried"),
    (["brave", "courage", "héroï"], "brave and determined, steady voice"),
    (["souri", "joie", "riant", "gaieté"], "light and cheerful, smiling tone"),
    (["contemplat", "rêverie", "lointain"], "contemplative, dreamy and distant"),
    (["pressé", "urgent", "précipit"], "urgent, speaking fast"),
    (["ferme", "détermin", "résolu"], "firm and resolute, unwavering"),
]

# Vocal reinforcement map: adds an official S2-Pro tag alongside the
# dramatic instruction to amplify the prosody effect.  Based on
# spectrographic A/B testing (session 31/05/2026):
#   - [sad] alone: +22% ZCR (subtle)
#   - [sad] + [whispering]: -47% RMS (clearly audible)
#   - [angry] + [shouting]: +702% RMS (massive)
# Maps dramatic instruction substrings → official tag to inject.
_VOCAL_REINFORCEMENT_MAP: list[tuple[list[str], str]] = [
    # (substrings of translated instruction, official S2-Pro tag)
    (["sad", "dropping", "sorrow"], "whispering"),
    (["angry", "furious", "rage"], "loud voice"),
    (["fearful", "trembling", "afraid"], "whispering"),
    (["excited", "quickening"], "emphasis"),
    (["whispering", "conspiratorial"], "whispering"),
    (["shouting", "forceful", "commanding"], "shouting"),
    (["sobbing", "crying", "break"], "sigh"),
    (["menacing", "dark", "low"], "low voice"),
    (["cold", "detached", "clinical"], "low voice"),
    (["ironic", "smirk", "mocking", "contemptuous"], "emphasis"),
    (["weary", "trailing", "resigned"], "sigh"),
    (["breathless", "hurried"], "panting"),
    (["emphatic", "deliberate"], "emphasis"),
    (["gentle", "warm", "soft"], "soft voice"),
]


def _translate_dramatic_prompt(prompt: str) -> str | None:
    """Translate a French dramatic prompt to a short English S2-Pro instruction.

    Returns a string of ≤60 chars suitable for use inside [brackets], or None
    if no matching pattern is found.  The translation is keyword-based (no LLM
    call) and deterministic — same prompt always produces the same instruction.
    """
    if not prompt:
        return None
    lower = prompt.lower()
    for keywords, instruction in _DRAMATIC_KEYWORD_MAP:
        for kw in keywords:
            if kw in lower:
                return instruction
    return None


def _get_dramatic_instruction(seg_index: int, prompt: str) -> str | None:
    """Get the translated dramatic instruction for a segment.

    Checks the LLM cache first, falls back to keyword matching.
    """
    if seg_index in _dramatic_translations:
        return _dramatic_translations[seg_index]
    return _translate_dramatic_prompt(prompt)


def _get_vocal_reinforcement(instruction: str) -> str | None:
    """Return an official S2-Pro tag that reinforces a dramatic instruction.

    Based on spectrographic A/B testing: combining an emotion instruction
    with a vocal-style tag amplifies the prosody effect.  For example,
    "sad, voice dropping" → [whispering] produces -47% RMS (vs -16% for
    [sad] alone on the same cloned voice).

    Returns the tag name (e.g. "whispering") or None if no reinforcement
    matches.
    """
    if not instruction:
        return None
    lower = instruction.lower()
    for substrings, tag in _VOCAL_REINFORCEMENT_MAP:
        for sub in substrings:
            if sub in lower:
                return tag
    return None


def _translate_prompts_batch(
    segments: list[AnnotatedSegment],
) -> dict[int, str]:
    """Translate all dramatic prompts via LLM (gpt-4o-mini) in batches.

    Returns {seg_index: english_instruction} mapping.  Results are cached
    to ``outputs/dramatic_translations.json`` — subsequent runs skip the LLM.
    """
    cache_path = BASE_DIR / "outputs" / "dramatic_translations.json"
    if cache_path.exists():
        try:
            cached = json.loads(cache_path.read_text(encoding="utf-8"))
            logger.info("Loaded %d cached dramatic translations", len(cached))
            return {int(k): v for k, v in cached.items()}
        except (json.JSONDecodeError, ValueError):
            logger.warning("Corrupt translations cache, regenerating")

    translations: dict[int, str] = {}
    prompts_to_translate: list[tuple[int, str]] = []
    for seg in segments:
        if seg.dramatic_prompt:
            prompts_to_translate.append((seg.seg_index, seg.dramatic_prompt))

    if not prompts_to_translate:
        return translations

    try:
        from openai import OpenAI
        import os

        client = OpenAI()  # Uses OPENAI_API_KEY from env
        model = os.getenv("TRANSLATION_MODEL", "gpt-4o-mini")

        system_msg = (
            "You are a voice direction translator. Convert French dramatic "
            "prompts for audiobook narration into SHORT English voice "
            "instructions for TTS. Each instruction must be ≤60 characters, "
            "in plain English (no brackets), describing HOW the narrator "
            "should sound. Examples:\n"
            "- 'calm and measured, steady pace'\n"
            "- 'building suspense, slow and tense'\n"
            "- 'ironic and dry, with a smirk'\n"
            "- 'cold and detached, clinical'\n"
            "- 'weary, voice trailing off'\n\n"
            "Return a JSON object mapping segment index to instruction. "
            "Example: {\"0\": \"composed and neutral, even pace\", \"1\": ...}"
        )

        total_batches = (
            len(prompts_to_translate) + _TRANSLATION_BATCH_SIZE - 1
        ) // _TRANSLATION_BATCH_SIZE
        print(
            f"  [P5] Translating {len(prompts_to_translate)} dramatic prompts "
            f"via {model} ({total_batches} batches)..."
        )

        for batch_idx in range(total_batches):
            start = batch_idx * _TRANSLATION_BATCH_SIZE
            end = min(start + _TRANSLATION_BATCH_SIZE, len(prompts_to_translate))
            batch_items = prompts_to_translate[start:end]

            user_msg = "Translate these dramatic prompts:\n"
            for idx, prompt in batch_items:
                user_msg += f'\n{idx}: "{prompt}"'

            try:
                resp = client.chat.completions.create(
                    model=model,
                    messages=[
                        {"role": "system", "content": system_msg},
                        {"role": "user", "content": user_msg},
                    ],
                    temperature=0.3,
                    response_format={"type": "json_object"},
                )
                batch_result = json.loads(resp.choices[0].message.content)
                for k, v in batch_result.items():
                    idx = int(k)
                    instruction = str(v).strip()
                    if instruction and len(instruction) <= 80:
                        translations[idx] = instruction
                    elif instruction:
                        # Truncate to 60 chars at word boundary
                        truncated = instruction[:60].rsplit(" ", 1)[0]
                        translations[idx] = truncated
                print(
                    f"    Batch {batch_idx + 1}/{total_batches}: "
                    f"{len(batch_result)} translations"
                )
            except Exception as exc:
                logger.error(
                    "LLM translation batch %d failed: %s", batch_idx + 1, exc
                )
                # Fall back to keyword matching for this batch
                for idx, prompt in batch_items:
                    kw = _translate_dramatic_prompt(prompt)
                    if kw:
                        translations[idx] = kw

    except ImportError:
        logger.warning("openai not available, using keyword fallback")
        for idx, prompt in prompts_to_translate:
            kw = _translate_dramatic_prompt(prompt)
            if kw:
                translations[idx] = kw

    # Cache results
    cache_path.parent.mkdir(exist_ok=True, parents=True)
    cache_path.write_text(
        json.dumps(translations, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"  [P5] Cached {len(translations)} dramatic translations")

    return translations


def _extract_prefix_tags(prefix: str) -> list[str]:
    """Extract prosody tags from a natural-language prefix for S2-Pro.

    Strategy:
      1. If any official English tag substring is present → use those (up to 3).
      2. Otherwise → wrap the whole prefix as ONE free-form bracketed tag,
         provided it is short enough to be interpreted (not vocalized).
    """
    from .schemas import ALL_PROSODY_TAGS

    lower = prefix.lower().strip()
    if not lower:
        return []
    official: list[str] = []
    for tag in sorted(ALL_PROSODY_TAGS, key=len, reverse=True):
        if tag in lower:
            official.append(tag)
    if official:
        return official[:3]
    # Free-form fallback: keep prefix as a single bracketed instruction.
    # S2-Pro tolerates up to ~80 chars of natural language inside []
    # (per fish.audio blog examples: "speaking slowly, almost hesitant" ~50 chars).
    # Longer instructions risk being vocalized literally rather than interpreted.
    cleaned = lower.rstrip(".,:; ").strip()
    if 0 < len(cleaned) <= 80:
        return [cleaned]
    return []


# Backwards-compatible alias (kept for callers; new logic above).
import warnings as _warnings


def _extract_official_tags(prefix: str) -> list[str]:
    """Deprecated alias for _extract_prefix_tags.

    Behaviour changed: this now extracts free-form tags in addition to
    official ones (F2 fix, Issue #1600).
    """
    _warnings.warn(
        "_extract_official_tags is deprecated; use _extract_prefix_tags. "
        "Behaviour changed: now extracts free-form tags too (F2, #1600).",
        DeprecationWarning,
        stacklevel=2,
    )
    return _extract_prefix_tags(prefix)


def _compose_tts_text(seg: AnnotatedSegment) -> str:
    """Compose the final TTS text for S2-Pro.

    F5 (prosody regression fix): dramatic_prompt (French, ~186 chars avg) cannot
    go in brackets directly — S2-Pro vocalizes French text (WER #1277/#1485).
    Instead, we translate the dramatic intent to a short English instruction
    that S2-Pro interprets as a voice direction.

    Composition order:
    1. Translated dramatic_prompt → short English [instruction]
    2. Vocal reinforcement tag (official S2-Pro tag that amplifies the emotion)
    3. Official tags from tts_context_prefix (if any)
    4. The annotated text with normalized inline tags
    """
    prefix_parts: list[str] = []
    seen_tags: set[str] = set()  # Track tags already added to avoid duplicates

    # F5: translate dramatic prompt to short English instruction
    translated: str | None = None
    if seg.dramatic_prompt:
        translated = _get_dramatic_instruction(seg.seg_index, seg.dramatic_prompt)
        if translated:
            prefix_parts.append(f"[{translated}]")

    # Vocal reinforcement: add an official S2-Pro tag that amplifies
    # the dramatic instruction's effect on cloned voices.
    if translated:
        vocal_tag = _get_vocal_reinforcement(translated)
        if vocal_tag:
            seen_tags.add(vocal_tag)
            prefix_parts.append(f"[{vocal_tag}]")

    # Add official tags from tts_context_prefix (if any)
    if seg.tts_context_prefix:
        for tag in _extract_prefix_tags(seg.tts_context_prefix):
            if tag not in seen_tags:
                prefix_parts.append(f"[{tag}]")
                seen_tags.add(tag)
            if len(prefix_parts) >= _MAX_PREFIX_TAGS:
                break

    prefix_block = " ".join(prefix_parts)
    if prefix_block:
        prefix_block = prefix_block + " "
    result_parts = [prefix_block] if prefix_block else []

    base_text = seg.fishaudio_text or seg.annotated_text or seg.text
    base_text = _normalize_tags(base_text)

    # Remove duplicate official tags from base text that are already in prefix.
    # S2-Pro processes tags sequentially; duplicate tags are redundant and waste
    # the prefix slot budget (_MAX_PREFIX_TAGS).
    from .schemas import ALL_PROSODY_TAGS as _ALL_TAGS
    for tag in seen_tags:
        if tag in _ALL_TAGS:
            base_text = base_text.replace(f"[{tag}] ", "", 1)

    # Inject mid-segment prosody tags for long texts (>200 chars)
    # S2-Pro tags affect what follows them, so inserting at punctuation
    # boundaries creates natural variation within a single segment.
    if len(base_text) > 200:
        base_text = _inject_mid_segment_tags(base_text)

    result_parts.append(base_text)
    result = " ".join(result_parts)

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


def _normalize_tags(text: str) -> str:
    """Normalize inline tags in text for FishAudio S2-Pro.

    1. Convert (parenthetical voice instructions) to [brackets]
    2. Map known non-official tags to closest official equivalent
    3. REMOVE free-form / natural-language tags — S2-Pro vocalizes them
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
        # Free-form tag — S2-Pro VOCALIZES it (proven WER #1277/#1485).
        # Remove it entirely to prevent extra spoken words.
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

    # F4 (Issue #1600): modulate temperature by P3 dramatic tension instead of
    # hardcoded 0.7. Low tension → more controlled delivery (~0.5), high
    # tension → more expressive variation (~0.9). Voice identity remains stable
    # because reference_id + seed are unchanged; only sampling diversity moves.
    #
    # Rationale for the linear mapping and range:
    #   - S2-Pro default temperature is 0.7 (neutral). Values < 0.5 produce
    #     near-identical outputs across seeds (observed during WER testing,
    #     session 23/05/2026, Act 1 narrator segments). Values > 0.95 produce
    #     unstable prosody with occasional word drops.
    #   - The range [0.4, 0.95] was chosen to avoid these extremes while giving
    #     meaningful variation. The slope 0.04/point maps tension 0→0.5 and
    #     tension 10→0.9, centered around the S2-Pro default.
    #   - This is a FIRST-PASS heuristic. Empirical validation via WER on a
    #     held-out set (e.g. Act 3 segments) would strengthen confidence.
    tension = 5
    if seg.dramatic_ref is not None:
        tension = max(0, min(10, seg.dramatic_ref.tension_0_10))
    temperature = max(0.4, min(0.95, 0.5 + 0.04 * tension))

    # Build TTS requests for each chunk, prepending the tag prefix
    tts_requests = []
    for chunk in chunks:
        chunk_text = f"{tag_prefix}{chunk}" if tag_prefix else chunk
        tts_requests.append({
            "text": chunk_text,
            "reference_id": reference_id,
            "seed": seed,
            "temperature": temperature,
            "top_p": 0.9,
            "format": "mp3",
            "timeout": 300,
        })

    # Thermal backoff: pause between segments to prevent GPU overheating.
    # target 72C = light 3s pause, up to 30s pause at 80C+, full cooldown above.
    thermal_backoff(target_temp=72, max_temp=80, base_sleep=3.0, max_sleep=30.0)

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


def _load_cached_hashes() -> dict[int, str]:
    """Load text hashes from tts_results.json once (O(N) not O(N²))."""
    results_path = BASE_DIR / "outputs" / "tts_results.json"
    if not results_path.exists():
        return {}
    try:
        data = json.loads(results_path.read_text(encoding="utf-8"))
        return {r["seg_index"]: r.get("text_hash", "") for r in data}
    except (json.JSONDecodeError, KeyError):
        return {}


def _synthesize_batch(
    segments: list[tuple[AnnotatedSegment, str]],
    cached_hashes: dict[int, str] | None = None,
) -> list[TTSResult]:
    """Process a batch of segments concurrently.

    Delegates cache checking to _synthesize_segment (which does text-hash
    invalidation). Only truly cached segments skip the thread pool.
    """
    if cached_hashes is None:
        cached_hashes = {}
    results: dict[int, TTSResult] = {}

    # Quick first pass: check which are truly cached (hash matches)
    to_generate: list[tuple[int, AnnotatedSegment, str]] = []
    for seg, text in segments:
        reference_id = _resolve_voice(seg)
        seed = 42 + seg.seg_index
        mp3_path = TTS_DIR / f"seg_{seg.seg_index:04d}_{seg.speaker}.mp3"
        current_hash = _text_hash(text)

        if mp3_path.exists() and cached_hashes.get(seg.seg_index) == current_hash:
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

    # F5: Pre-translate dramatic prompts to short English instructions.
    # Cached in outputs/dramatic_translations.json — only calls LLM once.
    global _dramatic_translations
    _dramatic_translations = _translate_prompts_batch(batch.segments)
    translated_count = len(_dramatic_translations)
    print(f"  Dramatic translations: {translated_count}/{len(batch.segments)}")

    results: list[TTSResult] = []
    generated = 0
    cached = 0
    failed = 0

    # Preload cached hashes once (O(N) instead of O(N²))
    cached_hashes = _load_cached_hashes()
    print(f"  Cache: {len(cached_hashes)} entries preloaded")

    # Process in batches for progress reporting
    total = len(batch.segments)
    for batch_start in range(0, total, _BATCH_SIZE):
        batch_end = min(batch_start + _BATCH_SIZE, total)
        batch_segs = [
            (batch.segments[i], _compose_tts_text(batch.segments[i]))
            for i in range(batch_start, batch_end)
        ]

        batch_results = _synthesize_batch(batch_segs, cached_hashes)
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
