"""P6 — MP3 Compilation for the v4 audiobook pipeline.

Concatenates individual segment MP3s into a single audiobook file
using pydub with crossfade and act-boundary silence.
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import AnnotatedBatch, DramaticContextBatch

BASE_DIR = Path(__file__).parent

SEGMENT_GAP_MS = 400
ACT_GAP_MS = 1500
CROSSFADE_MS = 20
BITRATE = "192k"


def _detect_act_boundaries(dramatic_path: Path) -> dict[int, str]:
    """Build seg_index -> act label mapping for act boundary detection."""
    if not dramatic_path.exists():
        return {}

    batch = DramaticContextBatch.model_validate_json(
        dramatic_path.read_text(encoding="utf-8")
    )
    return {ctx.seg_index: ctx.act for ctx in batch.contexts}


def run(force: bool = False) -> Path:
    """Run P6 — MP3 compilation. Returns path to audiobook MP3."""
    output_path = BASE_DIR / "outputs" / "boule_de_suif_v4.mp3"
    tts_path = BASE_DIR / "outputs" / "tts_results.json"
    annotated_path = BASE_DIR / "outputs" / "annotated_v4.json"
    dramatic_path = BASE_DIR / "outputs" / "dramatic_context.json"

    if not tts_path.exists():
        raise FileNotFoundError(
            f"tts_results.json not found: {tts_path}\n"
            "Run P5 (TTS generation) first."
        )

    if output_path.exists() and not force:
        print(f"[P6] Cached: {output_path}")
        return output_path

    print("[P6] Compiling audiobook...")

    try:
        from pydub import AudioSegment
    except ImportError:
        raise ImportError("pydub is required for MP3 compilation. Install with: pip install pydub")

    tts_data = json.loads(tts_path.read_text(encoding="utf-8"))
    tts_by_idx = {r["seg_index"]: r for r in tts_data}

    act_map = _detect_act_boundaries(dramatic_path)

    # Build ordered list of MP3 segments
    segments_ordered = sorted(tts_data, key=lambda r: r["seg_index"])
    total = len(segments_ordered)

    print(f"  Segments to compile: {total}")

    audiobook = AudioSegment.silent(duration=500)  # Opening silence
    prev_act: str | None = None
    compiled = 0
    skipped = 0

    for entry in segments_ordered:
        seg_idx = entry["seg_index"]
        mp3_path = entry.get("mp3_path", "")

        if not mp3_path or not Path(mp3_path).exists():
            skipped += 1
            continue

        try:
            seg_audio = AudioSegment.from_mp3(mp3_path)
        except Exception as e:
            print(f"  [P6] Error loading seg {seg_idx}: {e}")
            skipped += 1
            continue

        # Act boundary detection
        current_act = act_map.get(seg_idx)
        if prev_act is not None and current_act != prev_act:
            audiobook += AudioSegment.silent(duration=ACT_GAP_MS)
            print(f"  Act boundary: {prev_act} -> {current_act} at seg {seg_idx}")
        prev_act = current_act

        # Add segment with gap and crossfade
        gap = AudioSegment.silent(duration=SEGMENT_GAP_MS)
        audiobook += gap.append(seg_audio, crossfade=CROSSFADE_MS)
        compiled += 1

        if compiled % 100 == 0:
            print(f"  Progress: {compiled}/{total}")

    # Export
    audiobook.export(
        str(output_path),
        format="mp3",
        bitrate=BITRATE,
        tags={
            "title": "Boule de Suif",
            "artist": "Guy de Maupassant",
            "comment": "v4 FishAudio S2-Pro audiobook pipeline",
        },
    )

    duration_s = len(audiobook) / 1000.0
    size_mb = output_path.stat().st_size / (1024 * 1024)

    print(f"[P6] Done: {output_path}")
    print(f"  Compiled: {compiled}, Skipped: {skipped}")
    print(f"  Duration: {duration_s:.1f}s ({duration_s/60:.1f}min)")
    print(f"  Size: {size_mb:.1f} MB")

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
