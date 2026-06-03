"""
Generate MP3s for 3 dialogue scenes for user validation.
Uses existing annotations but normalizes to official S2-Pro tags only.
"""
from __future__ import annotations

import json
import re
import time
import logging
from pathlib import Path

import requests

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s")
logger = logging.getLogger(__name__)

BASE_DIR = Path(__file__).parent
OUTPUTS = BASE_DIR / "outputs"
FISHAUDIO_URL = "http://localhost:8197"

REFS_MANIFEST = OUTPUTS / "fishaudio_references" / "manifest.json"


def load_speaker_mapping() -> dict[str, str]:
    """Build speaker -> reference_id mapping from cloning manifest."""
    if not REFS_MANIFEST.exists():
        logger.warning("No manifest at %s; voices will be default", REFS_MANIFEST)
        return {}
    refs = json.load(open(REFS_MANIFEST, encoding="utf-8"))
    mapping: dict[str, str] = {}
    for entry in refs:
        if entry.get("status") != "cloned":
            continue
        ref_id = entry["reference_id"]
        for spk in entry.get("speakers", []):
            mapping[spk] = ref_id
    return mapping


SPEAKER_TO_REF = load_speaker_mapping()
print(f"Loaded {len(SPEAKER_TO_REF)} speaker -> reference_id mappings")

# Official S2-Pro tags (29 total)
OFFICIAL_TAGS = {
    "clears throat", "inhale", "inhalation", "exhale", "sigh",
    "panting", "breathing", "gasp",
    "groan", "moaning", "sobbing", "crying", "laughing",
    "chuckling", "giggle",
    "pause", "short pause", "long pause",
    "whispering", "whispering voice", "soft voice", "low voice",
    "loud voice", "shouting",
    "excited", "angry", "sad",
    "emphasis", "rustling sound",
}

# Dialogue scenes
SCENES = {
    "scene1_appel_elisabeth": list(range(90, 101)),
    "scene2_debat_follenvie_cornudet": list(range(115, 123)),
    "scene3_cocher_comte": list(range(134, 143)),
}

ALL_INDICES = sorted(set(seg for scene in SCENES.values() for seg in scene))

print(f"Segments to generate: {len(ALL_INDICES)}")
print(f"Indices: {ALL_INDICES}")

# Load segments
seg_data = json.load(open(OUTPUTS / "segments_v4.json", encoding="utf-8"))
seg_map = {s["seg_index"]: s for s in seg_data["segments"]}

# Load original annotations (may contain free-form tags)
annot_data = json.load(open(OUTPUTS / "annotated_v4.json", encoding="utf-8"))
annot_map = {}
for seg in annot_data.get("segments", []):
    annot_map[seg["seg_index"]] = seg

# Also load tags-only annotations if available
for fname in ["annotated_v4_tags_only_test.json", "annotated_v4_tags_only_act2.json"]:
    fpath = OUTPUTS / fname
    if fpath.exists():
        data = json.load(open(fpath, encoding="utf-8"))
        for seg in data.get("segments", []):
            annot_map[seg["seg_index"]] = seg  # Override with tags-only version


def normalize_to_official_tags(text: str) -> str:
    """Strip non-official tags from text, keep only official S2-Pro tags."""
    def replace_tag(match):
        content = match.group(1).strip().lower()
        if content in OFFICIAL_TAGS:
            return f"[{content}]"
        return ""  # Remove non-official tags

    result = re.sub(r"\[([^\]]+)\]", replace_tag, text)
    # Clean up double spaces
    result = re.sub(r"\s+", " ", result).strip()
    return result


def compose_tts_text(seg: dict, annotation: dict | None) -> str:
    """Compose TTS text from segment + annotation with official tags only."""
    if annotation and annotation.get("fishaudio_text"):
        raw = annotation["fishaudio_text"]
    elif annotation and annotation.get("annotated_text"):
        raw = annotation["annotated_text"]
    else:
        raw = seg["text"]

    # Normalize: keep only official tags
    return normalize_to_official_tags(raw)


# Output directory
out_dir = OUTPUTS / "tts_dialogue_validation"
out_dir.mkdir(exist_ok=True, parents=True)

# Wait for service
print("\nChecking FishAudio service...")
for attempt in range(60):
    try:
        resp = requests.get(f"{FISHAUDIO_URL}/", timeout=5)
        if resp.status_code == 200:
            print("FishAudio ready!")
            break
    except Exception:
        if attempt < 59:
            time.sleep(5)
        else:
            raise RuntimeError("FishAudio not ready after 300s")

# Generate MP3s
print(f"\nGenerating {len(ALL_INDICES)} segments...")
generated = 0
failed = 0
skipped = 0

for idx in ALL_INDICES:
    seg = seg_map.get(idx)
    if not seg:
        print(f"  seg_{idx}: SKIP (not in segments_v4)")
        skipped += 1
        continue

    annotation = annot_map.get(idx)
    tts_text = compose_tts_text(seg, annotation)
    speaker = seg.get("speaker", "narrateur")

    output_file = out_dir / f"seg_{idx:04d}.mp3"
    if output_file.exists() and output_file.stat().st_size > 1000:
        print(f"  seg_{idx}: EXISTS ({output_file.stat().st_size // 1024}KB)")
        generated += 1
        continue

    ref_id = SPEAKER_TO_REF.get(speaker, "")
    try:
        payload = {
            "text": tts_text[:500],  # Truncate to 500 chars
            "seed": 42,
            "temperature": 0.7,
            "top_p": 0.9,
            "format": "mp3",
        }
        if ref_id:
            payload["reference_id"] = ref_id
        resp = requests.post(
            f"{FISHAUDIO_URL}/v1/tts",
            json=payload,
            timeout=600,
        )
        resp.raise_for_status()

        with open(output_file, "wb") as f:
            f.write(resp.content)

        size_kb = len(resp.content) // 1024
        ref_tag = ref_id or "DEFAULT"
        print(f"  seg_{idx}: OK ({size_kb}KB, {speaker}->{ref_tag}) [{tts_text[:50]}...]")
        generated += 1

    except Exception as e:
        print(f"  seg_{idx}: FAIL - {e}")
        failed += 1

print(f"\nDone: {generated} generated, {failed} failed, {skipped} skipped")
print(f"Output: {out_dir}")

# Compile scene MP3s
print("\nCompiling scene MP3s...")
try:
    from pydub import AudioSegment

    for scene_name, indices in SCENES.items():
        audio_parts = []
        for idx in indices:
            fpath = out_dir / f"seg_{idx:04d}.mp3"
            if fpath.exists():
                audio_parts.append(AudioSegment.from_mp3(str(fpath)))
            else:
                print(f"  Warning: {fpath.name} missing for {scene_name}")

        if audio_parts:
            combined = audio_parts[0]
            for part in audio_parts[1:]:
                # Add 300ms silence between segments
                combined += AudioSegment.silent(duration=300) + part

            scene_file = out_dir / f"{scene_name}.mp3"
            combined.export(str(scene_file), format="mp3", bitrate="128k")
            duration_s = len(combined) / 1000
            print(f"  {scene_name}: {duration_s:.1f}s ({scene_file.name})")
        else:
            print(f"  {scene_name}: NO AUDIO PARTS")

except ImportError:
    print("  pydub not installed - skipping compilation")
    print("  Install with: pip install pydub")
    print("  Individual segment MP3s are still available in: " + str(out_dir))
