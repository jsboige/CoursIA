"""Whisper WebUI diarization client for the v4 pipeline.

Uses the Gradio REST API (not gradio_client library) for speaker diarization.
Requires Whisper WebUI running with pyannote and HF_TOKEN configured.
"""
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


def login_session() -> requests.Session:
    s = requests.Session()
    r = s.post(
        f"{WHISPER_WEBUI_URL}/login",
        data={"username": WHISPER_USER, "password": WHISPER_PASSWORD},
    )
    assert r.status_code == 200, f"Login failed: {r.text}"
    return s


def upload_file(s: requests.Session, file_path: str) -> str:
    with open(file_path, "rb") as f:
        r = s.post(
            f"{WHISPER_WEBUI_URL}/gradio_api/upload",
            files={"files": (Path(file_path).name, f, "audio/mpeg")},
        )
    assert r.status_code == 200, f"Upload failed: {r.text}"
    return r.json()[0]


def transcribe_with_diarization(
    s: requests.Session,
    file_path: str,
    language: str = "french",
    model: str = "large-v3-turbo",
    timeout: int = 600,
) -> str:
    """Transcribe with diarization via Whisper WebUI REST API.

    Returns raw SRT text with speaker labels (SPEAKER_00|text).
    """
    uploaded = upload_file(s, file_path)

    prepend_punc = "\"'" + "“¿([{-"
    append_punc = "\"'" + ".。,，!！?？:：”)]}、"

    payload = {
        "data": [
            [{"path": uploaded, "meta": {"_type": "gradio.FileData"}}],
            "",      # input_folder_path
            False,   # include_subdirectory
            True,    # save_same_dir
            "SRT",   # file_format
            False,   # add_timestamp
            model,   # model
            language,  # language
            False,   # translate
            5,       # beam_size
            -1,      # log_prob_threshold
            0.6,     # no_speech_threshold
            "float32",  # compute_type
            5,       # best_of
            1,       # patience
            True,    # condition_on_previous_text
            0.5,     # prompt_reset_on_temperature
            "",      # initial_prompt
            0,       # temperature
            2.4,     # compression_ratio_threshold
            1,       # length_penalty
            1,       # repetition_penalty
            0,       # no_repeat_ngram_size
            "",      # prefix
            True,    # suppress_blank
            "[-1]",  # suppress_tokens
            1,       # max_initial_timestamp
            False,   # word_timestamps
            prepend_punc,  # prepend_punctuations
            append_punc,   # append_punctuations
            None,    # max_new_tokens
            30,      # chunk_length
            None,    # hallucination_silence_threshold
            "",      # hotwords
            0.5,     # language_detection_threshold
            1,       # language_detection_segments
            24,      # batch_size
            True,    # offload whisper sub model
            False,   # Enable Silero VAD Filter
            0.5,     # VAD threshold
            250,     # min_speech_duration_ms
            9999,    # max_speech_duration_s
            1000,    # min_silence_duration_ms
            2000,    # speech_pad_ms
            True,    # Enable Diarization
            "cuda",  # diarization device
            os.getenv("HF_TOKEN", ""),  # HF Token
            True,    # offload diarization model
            False,   # Enable BGM Filter
            "UVR-MDX-NET-Inst_HQ_4",  # BGM model
            "cuda",  # BGM device
            256,     # BGM segment_size
            False,   # BGM save_file
            True,    # BGM offload
        ]
    }

    r = s.post(
        f"{WHISPER_WEBUI_URL}/gradio_api/call/transcribe_file",
        json=payload,
    )
    if r.status_code != 200:
        raise RuntimeError(f"Call failed ({r.status_code}): {r.text[:500]}")

    resp = r.json()
    event_id = resp.get("event_id")
    if not event_id:
        raise RuntimeError(f"No event_id: {resp}")

    # Stream SSE result
    t0 = time.time()
    r2 = s.get(
        f"{WHISPER_WEBUI_URL}/gradio_api/call/transcribe_file/{event_id}",
        stream=True, timeout=timeout,
    )
    result_data = None
    error_msg = None
    for line in r2.iter_lines(decode_unicode=True):
        if not line:
            continue
        if line.startswith("event:"):
            evt = line[6:].strip()
            if evt == "error":
                error_msg = "server error"
        elif line.startswith("data:"):
            raw = line[5:].strip()
            try:
                parsed = json.loads(raw)
                result_data = parsed
            except json.JSONDecodeError:
                error_msg = raw

    if error_msg and not result_data:
        raise RuntimeError(f"Diarization failed: {error_msg[:500]}")

    if result_data and isinstance(result_data, list) and len(result_data) > 0:
        return str(result_data[0])
    return ""


def parse_srt_diarization(srt_content: str) -> list[dict]:
    """Parse SRT with speaker labels into structured segments."""
    if not srt_content:
        return []

    segments = []
    blocks = srt_content.strip().split("\n\n")
    for block in blocks:
        lines = block.strip().split("\n")
        if len(lines) < 3:
            continue

        text = " ".join(lines[2:])

        speaker = "UNKNOWN"
        if "|" in text and text.startswith("SPEAKER_"):
            pipe_idx = text.index("|")
            speaker = text[:pipe_idx]
            text = text[pipe_idx + 1:].strip()

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


def diarize_segment(
    mp3_path: str,
    seg_index: int,
    session: requests.Session | None = None,
) -> dict:
    """Run diarization on a single MP3 segment.

    Returns a dict matching DiarizationResult schema.
    """
    try:
        from .schemas import DiarizationResult, DiarizedSegment
    except ImportError:
        from schemas import DiarizationResult, DiarizedSegment

    own_session = session is None
    if own_session:
        session = login_session()

    try:
        t0 = time.time()
        srt_text = transcribe_with_diarization(session, mp3_path)
        elapsed = time.time() - t0

        parsed = parse_srt_diarization(srt_text)
        speakers = list(set(s["speaker"] for s in parsed)) if parsed else []

        # Find dominant speaker
        from collections import Counter
        speaker_counts = Counter(s["speaker"] for s in parsed) if parsed else Counter()
        dominant = speaker_counts.most_common(1)[0][0] if speaker_counts else ""

        result = DiarizationResult(
            seg_index=seg_index,
            mp3_path=mp3_path,
            detected_speakers=speakers,
            segments=[DiarizedSegment(**s) for s in parsed],
            speaker_count=len(speakers),
            dominant_speaker=dominant,
            elapsed_s=round(elapsed, 1),
        )
    except Exception as e:
        result = DiarizationResult(
            seg_index=seg_index,
            mp3_path=mp3_path,
            detected_speakers=[],
            segments=[],
            speaker_count=0,
            elapsed_s=0.0,
            error=str(e),
        )
    finally:
        if own_session:
            pass  # session cleanup not needed

    return result.model_dump()
