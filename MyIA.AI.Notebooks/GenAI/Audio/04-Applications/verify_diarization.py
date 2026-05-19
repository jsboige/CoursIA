"""Verify audiobook speaker placement using Whisper WebUI diarization.

Compares detected speakers from Whisper+pyannote diarization against
the expected speakers from segments_annotated.json.

Two modes:
  --per-segment  (default): Verify individual WAV segments
  --full-audiobook: Verify the compiled audiobook (detect speaker changes)

Usage:
    python verify_diarization.py --sample 20
    python verify_diarization.py --full-audiobook audiobook.wav
"""
import json
import os
import sys
import time
import argparse
from collections import Counter
from pathlib import Path

from gradio_client import Client, handle_file

BASE_DIR = Path(__file__).parent
OUTPUT_DIR = BASE_DIR / "tts_output_fishaudio"
ANNOTATED_FILE = OUTPUT_DIR / "segments_annotated.json"

WHISPER_WEBUI_URL = os.getenv("WHISPER_WEBUI_URL", "http://localhost:7860")
WHISPER_USER = os.getenv("WHISPER_WEBUI_USER", "whisper")
WHISPER_PASSWORD = os.getenv("WHISPER_WEBUI_PASSWORD")
HF_TOKEN = os.getenv("HF_TOKEN", "")

# Default Gradio params for transcribe_file (all 54 positional args)
DEFAULT_GRADIO_PARAMS = [
    "",         # input_folder_path
    False,      # include_subdirectory
    True,       # save_same_dir
    "SRT",      # file_format
    False,      # add_timestamp
    "large-v3-turbo",  # model
    "french",   # language
    False,      # translate
    5,          # beam_size
    -1,         # log_prob_threshold
    0.6,        # no_speech_threshold
    "float32",  # compute_type
    5,          # best_of
    1,          # patience
    True,       # condition_on_previous_text
    0.5,        # prompt_reset_on_temperature
    "",         # initial_prompt
    0,          # temperature
    2.4,        # compression_ratio_threshold
    1,          # length_penalty
    1,          # repetition_penalty
    0,          # no_repeat_ngram_size
    "",         # prefix
    True,       # suppress_blank
    "[-1]",     # suppress_tokens
    1,          # max_initial_timestamp
    False,      # word_timestamps
    "\"'“¿([{-",  # prepend_punctuations
    "\"'.。,，!！?？:：”)]}、",  # append_punctuations
    None,       # max_new_tokens
    30,         # chunk_length
    None,       # hallucination_silence_threshold
    "",         # hotwords
    0.5,        # language_detection_threshold
    1,          # language_detection_segments
    24,         # batch_size
    True,       # offload whisper sub model
    False,      # Enable Silero VAD Filter
    0.5,        # VAD threshold
    250,        # min_speech_duration_ms
    9999,       # max_speech_duration_s
    1000,       # min_silence_duration_ms
    2000,       # speech_pad_ms
    True,       # Enable Diarization
    "cuda",     # diarization device
    os.getenv("HF_TOKEN", ""),  # HF Token
    True,       # offload diarization model
    False,      # Enable BGM Filter
    "UVR-MDX-NET-Inst_HQ_4",  # BGM model
    "cuda",     # BGM device
    256,        # BGM segment_size
    False,      # BGM save_file
    True,       # BGM offload
]


def create_client():
    """Create authenticated Gradio client."""
    return Client(WHISPER_WEBUI_URL, auth=(WHISPER_USER, WHISPER_PASSWORD))


def transcribe_with_diarization(client, wav_path):
    """Send a WAV file to Whisper WebUI with diarization enabled.

    Returns (srt_text: str, srt_file_path: str|None).
    """
    params = [[handle_file(str(wav_path))]] + DEFAULT_GRADIO_PARAMS
    result = client.predict(*params, api_name="/transcribe_file")

    srt_text = ""
    srt_file = None
    if result:
        if isinstance(result[0], str):
            srt_text = result[0]
        if isinstance(result, tuple) and len(result) > 1 and isinstance(result[1], list):
            srt_file = result[1][0] if result[1] else None

    return srt_text, srt_file


def parse_srt_diarization(srt_content):
    """Parse SRT content with diarization to extract speaker segments.

    Returns list of (speaker_label, start_time, end_time, text).
    """
    if not srt_content:
        return []

    segments = []
    blocks = srt_content.strip().split("\n\n")
    for block in blocks:
        lines = block.strip().split("\n")
        if len(lines) < 3:
            continue

        text_lines = lines[2:]
        text = " ".join(text_lines)

        # Extract speaker label: SPEAKER_00|text or [SPEAKER_00] text
        speaker = "UNKNOWN"
        if "|" in text and text.startswith("SPEAKER_"):
            pipe_idx = text.index("|")
            speaker = text[:pipe_idx]
            text = text[pipe_idx + 1:].strip()
        else:
            for prefix in ["[SPEAKER_", "[Speaker "]:
                if prefix in text:
                    idx = text.index(prefix)
                    end = text.index("]", idx) + 1
                    speaker = text[idx:end]
                    text = text[end:].strip()
                    break

        # Parse timestamps
        time_line = lines[1]
        try:
            parts = time_line.split(" --> ")
            start_str = parts[0].strip().replace(",", ".")
            end_str = parts[1].strip().replace(",", ".")
            start_h, start_m, start_s = start_str.split(":")
            end_h, end_m, end_s = end_str.split(":")
            start_time = int(start_h) * 3600 + int(start_m) * 60 + float(start_s)
            end_time = int(end_h) * 3600 + int(end_m) * 60 + float(end_s)
        except (ValueError, IndexError):
            start_time = 0
            end_time = 0

        segments.append((speaker, start_time, end_time, text))

    return segments


def verify_segments(client, annotated, args):
    """Run diarization verification on individual WAV segments."""
    total = len(annotated)
    start = args.start or 0
    end = min(args.end or total, total)

    indices = list(range(start, end))
    if args.sample and args.sample < len(indices):
        step = len(indices) / args.sample
        indices = [indices[int(i * step)] for i in range(args.sample)]

    results = {
        "verified": 0, "match": 0, "mismatch": 0, "errors": 0,
        "details": [],
    }

    for i, seg_idx in enumerate(indices):
        seg = annotated[seg_idx]
        wav_files = list(OUTPUT_DIR.glob(f"fish_seg_{seg_idx:03d}_*.wav"))

        if not wav_files:
            results["errors"] += 1
            continue

        expected_speaker = seg.get("speaker", "Narrateur")

        try:
            srt_text, _ = transcribe_with_diarization(client, wav_files[0])
            diar_segments = parse_srt_diarization(srt_text)

            if not diar_segments:
                results["errors"] += 1
                results["details"].append({
                    "seg_index": seg_idx, "expected": expected_speaker,
                    "status": "no_diarization_output",
                })
                continue

            speaker_counts = Counter(s for s, _, _, _ in diar_segments)
            all_speakers = list(speaker_counts.keys())
            dominant = speaker_counts.most_common(1)[0][0]

            # Single-speaker segments should have exactly 1 speaker
            match = len(all_speakers) == 1
            results["verified"] += 1
            if match:
                results["match"] += 1
            else:
                results["mismatch"] += 1

            results["details"].append({
                "seg_index": seg_idx, "expected": expected_speaker,
                "detected_speakers": all_speakers, "dominant": dominant,
                "status": "MATCH" if match else "MISMATCH",
            })

            status = "MATCH" if match else "MISMATCH"
            print(f"  [{i+1}/{len(indices)}] Seg {seg_idx:03d} ({expected_speaker[:15]:15s}): "
                  f"{status} speakers={all_speakers}")

        except Exception as e:
            results["errors"] += 1
            results["details"].append({
                "seg_index": seg_idx, "expected": expected_speaker,
                "status": "error", "error": str(e),
            })
            print(f"  [{i+1}/{len(indices)}] Seg {seg_idx:03d}: ERROR {e}")

        time.sleep(1)

    return results


def verify_full_audiobook(client, audiobook_path, annotated):
    """Run diarization on the full compiled audiobook."""
    print(f"\nProcessing full audiobook: {audiobook_path}")
    print(f"File size: {Path(audiobook_path).stat().st_size / 1024 / 1024:.1f} MB")
    print("This may take 10-30 minutes depending on length...\n")

    srt_text, srt_file = transcribe_with_diarization(client, audiobook_path)
    diar_segments = parse_srt_diarization(srt_text)

    if not diar_segments:
        print("ERROR: No diarization output from Whisper WebUI")
        return {"error": "no_output"}

    # Analyze speaker distribution
    speaker_counts = Counter(s for s, _, _, _ in diar_segments)
    total_segments = len(diar_segments)
    total_duration = sum(end - start for _, start, end, _ in diar_segments)

    print(f"Total diarized segments: {total_segments}")
    print(f"Total duration: {total_duration:.1f}s ({total_duration/60:.1f}min)")
    print(f"Unique speakers detected: {len(speaker_counts)}")
    print(f"\nSpeaker distribution:")
    for speaker, count in speaker_counts.most_common():
        duration = sum(end - start for s, start, end, _ in diar_segments if s == speaker)
        print(f"  {speaker}: {count} segments ({duration:.1f}s, {duration/total_duration*100:.1f}%)")

    # Map expected speakers from annotations
    expected_counts = Counter(seg.get("speaker", "Narrateur") for seg in annotated)
    print(f"\nExpected speakers from annotations: {len(expected_counts)} unique")
    for speaker, count in expected_counts.most_common():
        print(f"  {speaker}: {count} segments")

    # Check if speaker count matches
    num_expected = len(expected_counts)
    num_detected = len(speaker_counts)

    # Compute a rough mapping: FishAudio uses ~6 distinct voice presets
    # Narrator male, expressive_male_cold, expressive_male_neutral, neutral_male
    # expressive_female_warm, expressive_female_cold, neutral_female
    voice_presets = set()
    for seg in annotated:
        spk = seg.get("speaker", "Narrateur").lower()
        if spk in ("narrateur", "le narrateur"):
            voice_presets.add("narrator_male")
        elif "rousset" in spk or "boule" in spk:
            voice_presets.add("expressive_female_warm")
        elif "comtesse" in spk:
            voice_presets.add("expressive_female_cold")
        elif "cornudet" in spk:
            voice_presets.add("expressive_male_neutral")
        elif "officier" in spk:
            voice_presets.add("expressive_male_cold")
        elif "loiseau" in spk and "madame" not in spk and "mme" not in spk:
            voice_presets.add("neutral_male")
        elif "loiseau" in spk:
            voice_presets.add("neutral_female")
        elif "comte" in spk:
            voice_presets.add("expressive_male_cold")
        elif "carre" in spk or "lamadon" in spk:
            voice_presets.add("neutral_male")
        elif "soeur" in spk:
            voice_presets.add("expressive_female_warm")
        elif "follenvie" in spk:
            voice_presets.add("neutral_male")

    print(f"\nDistinct voice presets used: {len(voice_presets)}")
    for vp in sorted(voice_presets):
        print(f"  {vp}")

    result = {
        "total_segments": total_segments,
        "total_duration": total_duration,
        "speakers_detected": num_detected,
        "speakers_expected": num_expected,
        "voice_presets_count": len(voice_presets),
        "speaker_distribution": {
            s: {"count": c, "duration": sum(
                end - start for sp, start, end, _ in diar_segments if sp == s
            )} for s, c in speaker_counts.most_common()
        },
        "diar_segments": [
            {"speaker": s, "start": start, "end": end, "text": text}
            for s, start, end, text in diar_segments
        ],
    }

    # Save full SRT
    if srt_file:
        import shutil
        dst = OUTPUT_DIR / "audiobook_diarized.srt"
        shutil.copy2(srt_file, dst)
        print(f"\nDiarized SRT saved to {dst}")

    return result


def main():
    parser = argparse.ArgumentParser(description="Verify audiobook speaker placement")
    parser.add_argument("--sample", type=int, default=20,
                        help="Number of segments to sample (0=all)")
    parser.add_argument("--start", type=int, default=0, help="Start segment index")
    parser.add_argument("--end", type=int, default=None, help="End segment index")
    parser.add_argument("--full-audiobook", type=str, default=None,
                        help="Path to full compiled audiobook WAV for diarization")
    parser.add_argument("--output", type=str, default=None,
                        help="Output JSON file for results")
    args = parser.parse_args()

    if not ANNOTATED_FILE.exists():
        print(f"Error: {ANNOTATED_FILE} not found")
        sys.exit(1)

    with open(ANNOTATED_FILE, encoding="utf-8") as f:
        annotated = json.load(f)

    print(f"Loaded {len(annotated)} annotated segments")

    print("\nConnecting to Whisper WebUI...")
    client = create_client()
    print("Connected")

    if args.full_audiobook:
        results = verify_full_audiobook(client, args.full_audiobook, annotated)
    else:
        print(f"Sampling {args.sample or 'all'} segments from [{args.start}:{args.end or len(annotated)}]")
        results = verify_segments(client, annotated, args)

        print(f"\n{'='*60}")
        print(f"Verification Summary")
        print(f"{'='*60}")
        print(f"Verified: {results['verified']}")
        print(f"  Match:    {results['match']}")
        print(f"  Mismatch: {results['mismatch']}")
        print(f"  Errors:   {results['errors']}")
        if results['verified'] > 0:
            print(f"  Accuracy: {results['match']/results['verified']*100:.1f}%")

    output_path = Path(args.output) if args.output else OUTPUT_DIR / "diarization_verify.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\nResults saved to {output_path}")


if __name__ == "__main__":
    main()
