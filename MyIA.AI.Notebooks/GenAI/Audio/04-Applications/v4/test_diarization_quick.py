"""Quick test: diarization via Whisper WebUI REST API on 1 segment."""
from __future__ import annotations

import json
import os
import time
from pathlib import Path

import requests
from dotenv import load_dotenv

load_dotenv(Path(__file__).resolve().parents[3] / ".env", override=False)

WHISPER_WEBUI_URL = os.getenv("WHISPER_WEBUI_URL", "http://localhost:7860")
WHISPER_USER = os.getenv("WHISPER_WEBUI_USER", "whisper")
WHISPER_PASSWORD = os.getenv("WHISPER_WEBUI_PASSWORD", "")

MP3_PATH = Path(__file__).parent / "outputs" / "tts_v4" / "seg_0072_comte.mp3"


def _login_session() -> requests.Session:
    s = requests.Session()
    r = s.post(
        f"{WHISPER_WEBUI_URL}/login",
        data={"username": WHISPER_USER, "password": WHISPER_PASSWORD},
    )
    assert r.status_code == 200, f"Login failed: {r.text}"
    return s


def _upload(s: requests.Session, mp3_path: str) -> str:
    with open(mp3_path, "rb") as f:
        r = s.post(
            f"{WHISPER_WEBUI_URL}/gradio_api/upload",
            files={"files": (os.path.basename(mp3_path), f, "audio/mpeg")},
        )
    assert r.status_code == 200, f"Upload failed: {r.text}"
    return r.json()[0]


def transcribe_with_diarization(s: requests.Session, mp3_path: str) -> str:
    """Transcribe with diarization enabled. Returns SRT text."""
    uploaded = _upload(s, mp3_path)

    prepend_punc = "\"'" + "“¿([{-"
    append_punc = "\"'" + ".。,，!！?？:：”)]}、"

    data_payload = {
        "data": [
            [{"path": uploaded, "meta": {"_type": "gradio.FileData"}}],
            "",      # 1  input_folder_path
            False,   # 2  include_subdirectory
            True,    # 3  save_same_dir
            "SRT",   # 4  file_format
            False,   # 5  add_timestamp
            "large-v3-turbo",  # 6  model
            "french",          # 7  language
            False,   # 8  translate
            5,       # 9  beam_size
            -1,      # 10 log_prob_threshold
            0.6,     # 11 no_speech_threshold
            "float32",  # 12 compute_type
            5,       # 13 best_of
            1,       # 14 patience
            True,    # 15 condition_on_previous_text
            0.5,     # 16 prompt_reset_on_temperature
            "",      # 17 initial_prompt
            0,       # 18 temperature
            2.4,     # 19 compression_ratio_threshold
            1,       # 20 length_penalty
            1,       # 21 repetition_penalty
            0,       # 22 no_repeat_ngram_size
            "",      # 23 prefix
            True,    # 24 suppress_blank
            "[-1]",  # 25 suppress_tokens
            1,       # 26 max_initial_timestamp
            False,   # 27 word_timestamps
            prepend_punc,  # 28 prepend_punctuations
            append_punc,   # 29 append_punctuations
            None,    # 30 max_new_tokens
            30,      # 31 chunk_length
            None,    # 32 hallucination_silence_threshold
            "",      # 33 hotwords
            0.5,     # 34 language_detection_threshold
            1,       # 35 language_detection_segments
            24,      # 36 batch_size
            True,    # 37 offload whisper sub model
            False,   # 38 Enable Silero VAD Filter
            0.5,     # 39 VAD threshold
            250,     # 40 min_speech_duration_ms
            9999,    # 41 max_speech_duration_s
            1000,    # 42 min_silence_duration_ms
            2000,    # 43 speech_pad_ms
            True,    # 44 Enable Diarization
            "cuda",  # 45 diarization device
            os.getenv("HF_TOKEN", ""),  # 46 HF Token
            True,    # 47 offload diarization model
            False,   # 48 Enable BGM Filter
            "UVR-MDX-NET-Inst_HQ_4",  # 49 BGM model
            "cuda",  # 50 BGM device
            256,     # 51 BGM segment_size
            False,   # 52 BGM save_file
            True,    # 53 BGM offload
        ]
    }

    r = s.post(
        f"{WHISPER_WEBUI_URL}/gradio_api/call/transcribe_file",
        json=data_payload,
    )
    assert r.status_code == 200, f"Call failed ({r.status_code}): {r.text[:500]}"
    resp = r.json()
    if "event_id" not in resp:
        raise RuntimeError(f"No event_id in response: {resp}")
    event_id = resp["event_id"]

    # Stream SSE result
    t0 = time.time()
    r2 = s.get(
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
            elapsed = time.time() - t0
            print(f"  [{elapsed:.1f}s] event: {evt}")
        elif line.startswith("data:"):
            payload = line[5:].strip()
            try:
                parsed = json.loads(payload)
                result_data = parsed
            except json.JSONDecodeError:
                error_msg = payload
                print(f"  raw data: {payload[:200]}")

    if error_msg and not result_data:
        raise RuntimeError(f"Diarization failed: {error_msg[:500]}")

    if result_data and isinstance(result_data, list) and len(result_data) > 0:
        return str(result_data[0])
    return ""


def parse_srt_diarization(srt_content: str) -> list[dict]:
    """Parse SRT with speaker labels."""
    if not srt_content:
        return []

    segments = []
    blocks = srt_content.strip().split("\n\n")
    for block in blocks:
        lines = block.strip().split("\n")
        if len(lines) < 3:
            continue

        text = " ".join(lines[2:])

        # Extract speaker: SPEAKER_00|text or [SPEAKER_00] text
        speaker = "UNKNOWN"
        if "|" in text and text.startswith("SPEAKER_"):
            pipe_idx = text.index("|")
            speaker = text[:pipe_idx]
            text = text[pipe_idx + 1:].strip()

        # Parse timestamps
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


def main():
    print(f"Connecting to Whisper WebUI at {WHISPER_WEBUI_URL}...")
    s = _login_session()
    print("Logged in!")

    print(f"\nTesting diarization on: {MP3_PATH.name}")
    t0 = time.time()
    srt_text = transcribe_with_diarization(s, str(MP3_PATH))
    elapsed = time.time() - t0

    print(f"\n--- SRT Output ({elapsed:.1f}s) ---")
    print(srt_text[:2000])
    print("--- End ---")

    segments = parse_srt_diarization(srt_text)
    if segments:
        speakers = set(seg["speaker"] for seg in segments)
        print(f"\nDetected {len(segments)} segments, {len(speakers)} speaker(s): {speakers}")
        for seg in segments:
            print(f"  {seg['speaker']}: [{seg['start']:.1f}-{seg['end']:.1f}s] {seg['text'][:80]}")
    else:
        print("\nNo diarized segments found.")


if __name__ == "__main__":
    main()
