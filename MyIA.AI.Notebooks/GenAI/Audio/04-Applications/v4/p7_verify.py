"""P7 — Quality Verification for the v4 audiobook pipeline.

Runs WER (Word Error Rate) and speaker diarization checks on the
compiled audiobook to verify voice consistency and transcription accuracy.
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import QualityReport

BASE_DIR = Path(__file__).parent

WHISPER_URL = "http://localhost:7860"


def _transcribe_whisper(audio_path: str) -> dict:
    """Transcribe via Whisper WebUI API for WER calculation."""
    import requests

    try:
        with open(audio_path, "rb") as f:
            resp = requests.post(
                f"{WHISPER_URL}/api/transcribe",
                files={"audio": f},
                data={"language": "fr", "word_timestamps": "true"},
                timeout=600,
            )
            resp.raise_for_status()
            return resp.json()
    except Exception as e:
        print(f"  [P7] Whisper transcription error: {e}")
        return {}


def _word_error_rate(reference: str, hypothesis: str) -> float:
    """Compute Word Error Rate between reference and hypothesis."""
    ref_words = reference.lower().split()
    hyp_words = hypothesis.lower().split()

    if not ref_words:
        return 0.0 if not hyp_words else 1.0

    n = len(ref_words)
    m = len(hyp_words)

    # Levenshtein distance
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = i
    for j in range(m + 1):
        dp[0][j] = j

    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if ref_words[i - 1] == hyp_words[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1])

    return dp[n][m] / n


def _run_diarization(audio_path: str) -> dict:
    """Run speaker diarization via Whisper WebUI."""
    import requests

    try:
        with open(audio_path, "rb") as f:
            resp = requests.post(
                f"{WHISPER_URL}/api/diarize",
                files={"audio": f},
                data={"num_speakers": "10", "language": "fr"},
                timeout=1800,
            )
            resp.raise_for_status()
            return resp.json()
    except Exception as e:
        print(f"  [P7] Diarization error: {e}")
        return {}


def run(force: bool = False) -> Path:
    """Run P7 — quality verification. Returns path to quality_report.json."""
    output_path = BASE_DIR / "outputs" / "quality_report.json"
    audiobook_path = BASE_DIR / "outputs" / "boule_de_suif_v4.mp3"

    if not audiobook_path.exists():
        raise FileNotFoundError(
            f"Audiobook not found: {audiobook_path}\n"
            "Run P6 (compilation) first."
        )

    if output_path.exists() and not force:
        print(f"[P7] Cached: {output_path}")
        return output_path

    print("[P7] Running quality verification...")

    # Load expected segments
    annotated_path = BASE_DIR / "outputs" / "annotated_v4.json"
    if not annotated_path.exists():
        print("  [P7] WARNING: annotated_v4.json not found, skipping WER")

    wer_results: dict[str, float] = {}
    diarization_results: dict[str, int | float] = {}

    # Step 1: WER on sample segments
    if annotated_path.exists():
        print("[P7] Step 1: WER calculation (sampling)...")
        from .schemas import AnnotatedBatch

        batch = AnnotatedBatch.model_validate_json(
            annotated_path.read_text(encoding="utf-8")
        )
        segments = batch.segments

        # Sample 20 segments evenly distributed
        step = max(1, len(segments) // 20)
        sample_indices = list(range(0, len(segments), step))[:20]

        # Load TTS results to get individual MP3 paths
        tts_path = BASE_DIR / "outputs" / "tts_results.json"
        if tts_path.exists():
            tts_data = json.loads(tts_path.read_text(encoding="utf-8"))
            tts_by_idx = {r["seg_index"]: r for r in tts_data}

            wers: list[float] = []
            for idx in sample_indices:
                if idx >= len(segments):
                    continue
                seg = segments[idx]
                tts_result = tts_by_idx.get(seg.seg_index, {})
                mp3_path = tts_result.get("mp3_path", "")

                if not mp3_path or not Path(mp3_path).exists():
                    continue

                result = _transcribe_whisper(mp3_path)
                hypothesis = result.get("text", "")
                if hypothesis:
                    wer = _word_error_rate(seg.text, hypothesis)
                    wers.append(wer)

            if wers:
                wers_sorted = sorted(wers)
                wer_results["mean"] = round(sum(wers) / len(wers), 3)
                wer_results["p95"] = round(
                    wers_sorted[int(len(wers_sorted) * 0.95)], 3
                )
                wer_results["segments_above_30pct"] = sum(
                    1 for w in wers if w > 0.30
                )
                print(f"  Mean WER: {wer_results['mean']}")
                print(f"  P95 WER: {wer_results['p95']}")

    # Step 2: Diarization on full audiobook
    print("[P7] Step 2: Speaker diarization...")
    print("  This may take 10-30 minutes...")

    diar_data = _run_diarization(str(audiobook_path))
    if diar_data:
        segments = diar_data.get("segments", [])
        speaker_counts: dict[str, int] = {}
        for s in segments:
            spk = s.get("speaker", "UNKNOWN")
            speaker_counts[spk] = speaker_counts.get(spk, 0) + 1

        unique_speakers = len(speaker_counts)
        diarization_results["detected_speakers"] = unique_speakers
        diarization_results["expected"] = 9
        diarization_results["top_speaker_pct"] = round(
            max(speaker_counts.values()) / max(sum(speaker_counts.values()), 1) * 100, 1
        )
        print(f"  Detected speakers: {unique_speakers} (target: <=10)")
    else:
        diarization_results["detected_speakers"] = -1
        diarization_results["expected"] = 9

    # Verdict
    detected = diarization_results.get("detected_speakers", 999)
    mean_wer = wer_results.get("mean", 1.0)
    verdict = "PASS" if (detected <= 10 and mean_wer <= 0.15) else "NEEDS_REVIEW"

    report = QualityReport(
        wer=wer_results,
        diarization=diarization_results,
        verdict=verdict,
    )

    output_path.write_text(
        report.model_dump_json(indent=2),
        encoding="utf-8",
    )
    print(f"[P7] Done: {output_path}")
    print(f"  Verdict: {verdict}")
    print(f"  Speakers: {detected}, WER: {mean_wer}")

    return output_path


if __name__ == "__main__":
    load_dotenv(Path(__file__).resolve().parent.parent.parent.parent / ".env")
    run(force="--force" in " ".join(__import__("sys").argv))
