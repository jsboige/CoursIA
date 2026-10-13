"""P7 — Quality Verification for the v4 audiobook pipeline.

Runs WER (Word Error Rate) and speaker diarization checks on the
compiled audiobook to verify voice consistency and transcription accuracy.

Uses Whisper WebUI Gradio REST API for both transcription and diarization.
"""
from __future__ import annotations

import json
from pathlib import Path

from dotenv import load_dotenv

from .schemas import QualityReport
from .diarization_client import (
    login_session,
    transcribe_with_diarization,
    parse_srt_diarization,
)

BASE_DIR = Path(__file__).parent


def _word_error_rate(reference: str, hypothesis: str) -> float:
    """Compute Word Error Rate between reference and hypothesis."""
    import re

    def normalize(text: str) -> list[str]:
        text = text.lower()
        text = re.sub(r"[^\w\s'àâéèêëïîôùûüçœæ-]", "", text)
        return text.split()

    ref_words = normalize(reference)
    hyp_words = normalize(hypothesis)

    if not ref_words:
        return 1.0

    n = len(ref_words)
    m = len(hyp_words)
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


def _normalize_words(text: str) -> list[str]:
    """Normalize text to comparison words: NFC, lowercase, non-alnum to
    spaces, collapsed whitespace. Same convention as the A0C bench (#17586)
    so p7 counts what the bench measured."""
    import re
    import unicodedata

    text = unicodedata.normalize("NFC", text).lower()
    text = "".join(c if c.isalnum() else " " for c in text)
    return re.sub(r"\s+", " ", text).strip().split()


def _missing_word_spans(
    reference: str, hypothesis: str, min_words: int = 3
) -> list[dict]:
    """Passages of >=min_words consecutive words missing from the hypothesis.

    Omission control of #19692: the mean WER hides a render that drops whole
    sentences (measured on CosyVoice3 A0C, #17586 c.6035598289 — two
    segments absent under 3/3 ASRs while WER stayed ~0.12). Method = word
    alignment (difflib): a `delete` run of >=min_words reference words, or
    a `replace` run whose reference side exceeds the hypothesis side by
    >=min_words words, means the passage is gone, not mispronounced.

    Replaces the phase-1 trigram primitive, which over-flagged: one
    substituted word breaks every trigram it touches, producing a ~5-word
    halo around a single bad word (Zonos chunked measured 11 spans by
    trigrams vs 0 by alignment, #19695 c.6115711862). The alignment emits
    exact boundaries instead.
    """
    import difflib

    ref_words = _normalize_words(reference)
    hyp_words = _normalize_words(hypothesis)

    spans: list[tuple[int, int]] = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(
        None, ref_words, hyp_words, autojunk=False
    ).get_opcodes():
        if tag == "delete" and i2 - i1 >= min_words:
            spans.append((i1, i2))
        elif tag == "replace" and (i2 - i1) - (j2 - j1) >= min_words:
            spans.append((i1, i2))
    return [
        {"start": a, "end": b, "words": " ".join(ref_words[a:b])} for a, b in spans
    ]


def _voted_missing_spans(
    spans_by_model: dict[str, list[dict]], min_models: int = 2
) -> list[dict]:
    """Keep the spans missing under >=min_models distinct ASRs.

    A single ASR mishears: the 2-of-3 vote separates real omissions from
    ASR noise (a passage the render dropped is missing under every model, a
    passage one ASR misheard is not — measured on the A0C bench, #17586).
    Two spans from different models support the same omission when they
    overlap by >=3 words (alignment boundaries shift by a word or two
    between models); the reported span is the covering one, with its
    supporting models recorded.

    Voted spans that overlap each other describe the same omission (one
    long drop can align differently under each ASR and land in neighbouring
    clusters): they are merged into the covering span with the union of
    their supporting models — the reference method of #19695 c.6115711862,
    which this vote now reproduces exactly on the four A0C controls.
    """
    clusters: list[dict] = []
    for model, spans in spans_by_model.items():
        for span in spans:
            placed = False
            for cluster in clusters:
                for other in cluster["spans"]:
                    overlap = min(span["end"], other["end"]) - max(
                        span["start"], other["start"]
                    )
                    if overlap >= 3:
                        cluster["spans"].append(span)
                        cluster["models"].add(model)
                        placed = True
                        break
                if placed:
                    break
            if not placed:
                clusters.append({"spans": [span], "models": {model}})

    voted = []
    for cluster in clusters:
        models = cluster["models"]
        if len(models) < min_models:
            continue
        covering = max(cluster["spans"], key=lambda s: s["end"] - s["start"])
        voted.append({**covering, "absent_sous": sorted(models)})
    voted.sort(key=lambda s: s["start"])
    merged: list[dict] = []
    for span in voted:
        if merged and span["start"] < merged[-1]["end"]:
            prev = merged[-1]
            covering = max((prev, span), key=lambda s: s["end"] - s["start"])
            merged[-1] = {
                **covering,
                "absent_sous": sorted(
                    set(prev["absent_sous"]) | set(span["absent_sous"])
                ),
            }
        else:
            merged.append(span)
    return merged


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

    # Step 1: WER on sample segments (using Whisper API on port 8190)
    if annotated_path.exists():
        print("[P7] Step 1: WER calculation (sampling)...")
        import os
        import requests as req
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
            omission_records: list[dict] = []
            for idx in sample_indices:
                if idx >= len(segments):
                    continue
                seg = segments[idx]
                tts_result = tts_by_idx.get(seg.seg_index, {})
                mp3_path = tts_result.get("mp3_path", "")

                if not mp3_path or not Path(mp3_path).exists():
                    continue

                try:
                    mp3_bytes = Path(mp3_path).read_bytes()
                    # Omission control (#19692 phase 1): transcribe each
                    # sampled segment under three models and vote — the
                    # 2-of-3 vote is what separated real omissions from ASR
                    # noise on the A0C bench (#17586). WER keeps its single
                    # large-v3-turbo convention (unchanged metric).
                    hypotheses: dict[str, str] = {}
                    for model in ("tiny", "large-v3", "large-v3-turbo"):
                        resp = req.post(
                            "http://localhost:8190/v1/audio/transcriptions",
                            files={
                                "file": (Path(mp3_path).name, mp3_bytes, "audio/mpeg")
                            },
                            data={"language": "fr", "model": model},
                            headers={
                                "Authorization": f"Bearer {os.getenv('WHISPER_API_KEY', '')}"
                            },
                            timeout=60,
                        )
                        if resp.status_code == 200:
                            text = resp.json().get("text", "")
                            if text:
                                hypotheses[model] = text
                        else:
                            print(
                                f"    seg {idx} {model}: HTTP {resp.status_code}"
                            )

                    hypothesis = hypotheses.get("large-v3-turbo", "")
                    if hypothesis:
                        wer = _word_error_rate(seg.text, hypothesis)
                        wers.append(wer)
                    if hypotheses:
                        spans_by_model = {
                            model: _missing_word_spans(seg.text, hyp)
                            for model, hyp in hypotheses.items()
                        }
                        voted = _voted_missing_spans(spans_by_model)
                        if voted:
                            omission_records.append({
                                "seg_index": seg.seg_index,
                                "speaker": seg.speaker,
                                "models_present": sorted(hypotheses),
                                "n_spans": len(voted),
                                "n_words": sum(
                                    s["end"] - s["start"] for s in voted
                                ),
                                "spans": voted,
                                "per_model_spans": {
                                    m: [s["words"] for s in spans]
                                    for m, spans in spans_by_model.items()
                                },
                            })
                except Exception as e:
                    print(f"    seg {idx} STT error: {e}")

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

            # Omission control (#19692 phase 1): counts go into the quality
            # report (numeric schema), the per-segment detail goes to its own
            # artifact so a span can be read before acting on it (known
            # false positives: ASR inflection drifts, cf _missing_word_spans).
            wer_results["omission_segments"] = float(len(omission_records))
            wer_results["omission_spans_3plus"] = float(
                sum(r["n_spans"] for r in omission_records)
            )
            wer_results["omission_words_3plus"] = float(
                sum(r["n_words"] for r in omission_records)
            )
            omission_path = BASE_DIR / "outputs" / "omission_report.json"
            omission_path.write_text(
                json.dumps(
                    {
                        "method": (
                            "word alignment + 2-of-3 ASR vote (#19692): "
                            "difflib word alignment of each ASR hypothesis "
                            "against the source; a delete run of >=3 words "
                            "(or a replace run with >=3 words of reference "
                            "excess) is a missing span; a span counts as an "
                            "omission when missing under >=2 of {tiny, "
                            "large-v3, large-v3-turbo} (overlap >=3 words), "
                            "overlapping voted spans merged into the "
                            "covering span (method of the A0C reference, "
                            "#19695 c.6115711862)"
                        ),
                        "sampled_segments": len(sample_indices),
                        "segments_with_omissions": len(omission_records),
                        "records": omission_records,
                    },
                    indent=2,
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            n_spans = int(wer_results["omission_spans_3plus"])
            if omission_records:
                print(
                    f"  OMISSIONS: {n_spans} span(s) >=3 mots sur "
                    f"{len(omission_records)} segment(s) -> {omission_path.name}"
                )
                for rec in omission_records[:5]:
                    first = rec["spans"][0]["words"]
                    print(
                        f"    seg {rec['seg_index']} ({rec['speaker']}): "
                        f"{rec['n_spans']} span(s), ex: {first[:70]}"
                    )
            else:
                print("  OMISSIONS: none >=3 mots")

    # Step 2: Diarization on full audiobook via Whisper WebUI Gradio API
    print("[P7] Step 2: Speaker diarization...")
    print("  This may take 10-30 minutes...")

    try:
        session = login_session()
        srt_text = transcribe_with_diarization(session, str(audiobook_path))
        parsed = parse_srt_diarization(srt_text)

        if parsed:
            speaker_counts: dict[str, int] = {}
            for s in parsed:
                spk = s["speaker"]
                speaker_counts[spk] = speaker_counts.get(spk, 0) + 1

            unique_speakers = len(speaker_counts)
            diarization_results["detected_speakers"] = unique_speakers
            diarization_results["expected"] = 9
            diarization_results["top_speaker_pct"] = round(
                max(speaker_counts.values()) / max(sum(speaker_counts.values()), 1) * 100, 1
            )
            diarization_results["total_segments"] = len(parsed)
            print(f"  Detected speakers: {unique_speakers} (target: <=10)")
            print(f"  Total diarized segments: {len(parsed)}")
        else:
            diarization_results["detected_speakers"] = 0
            diarization_results["expected"] = 9
            print("  No diarized segments found in audiobook.")
    except Exception as e:
        print(f"  [P7] Diarization error: {e}")
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
