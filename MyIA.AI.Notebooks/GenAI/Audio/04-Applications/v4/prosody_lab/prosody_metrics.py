"""Objective prosody-measurement instrument for the v4 audiobook pipeline (#1273).

Why this exists
---------------
Until now TTS renders were judged by ear or by WER (Word Error Rate). WER measures
*which words* are spoken, never *the melody* — so a perfectly intelligible yet
monotone reading scores well. This module measures the melody directly, turning
"ca sonne plat" into a number that can be compared against OpenAI TTS-1-HD.

Pivot metric
------------
``f0_semitone_range`` = pitch span of the utterance in semitones, computed from
robust 5th/95th percentiles of the voiced F0 contour (``12 * log2(p95 / p5)``).
Perceptual anchors (human narration):
    < ~4 st   : flat / monotone
    ~6-8 st   : moderately expressive
    ~8-12+ st : expressive audiobook narration

Other metrics: F0 mean/median/std/CV, intonation velocity (semitones/s of pitch
movement), RMS volume dynamics, voiced fraction, onset (syllable) rate, pause
structure, and a DTW contour distance for measuring controllability (does the
melody actually change when the prosody instruction changes?).

F0 is extracted with ``librosa.pyin`` (probabilistic YIN) which yields an explicit
voiced/unvoiced flag, unlike the legacy ``librosa.yin`` whose unvoiced frames
returned garbage F0 that polluted the statistics.

Usage (CLI)
-----------
    python prosody_metrics.py openai=a.mp3 fish=b.mp3 clone=c.wav \
        --json outputs/prosody_lab/metrics.json \
        --plot outputs/prosody_lab/contours.png

Usage (import)
--------------
    from prosody_metrics import compute_metrics, compare, dtw_contour_distance
    m = compute_metrics("render.wav")
    print(m["f0_semitone_range"])
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

# librosa / matplotlib are imported lazily inside functions so that importing
# this module for its dataclasses/constants does not pull heavy deps.

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

DEFAULT_SR = 22050
# Generous F0 search bounds covering male (~80 Hz) to expressive female (~450 Hz).
# Robust percentiles (below) absorb the occasional octave error, so wide bounds
# are safe.
DEFAULT_FMIN = 65.0
DEFAULT_FMAX = 500.0

# Perceptual verdict thresholds on the semitone-range pivot metric.
FLAT_ST = 4.0
EXPRESSIVE_ST = 8.0


# ---------------------------------------------------------------------------
# Audio loading (robust to mp3/wav, ffmpeg-optional)
# ---------------------------------------------------------------------------


def load_audio(path: str | Path, sr: int = DEFAULT_SR) -> tuple[np.ndarray, int]:
    """Load *path* as a mono float32 waveform resampled to *sr*.

    Tries ``librosa.load`` first (soundfile / audioread backend); on failure
    (e.g. mp3 without a libsndfile mp3 build) falls back to ``pydub`` which
    decodes via ffmpeg. Raises the original error if both backends fail.
    """
    import librosa

    try:
        y, _ = librosa.load(str(path), sr=sr, mono=True)
        if y.size > 0:
            return y.astype(np.float32), sr
    except Exception:
        pass

    # Fallback: pydub -> raw samples
    from pydub import AudioSegment

    seg = AudioSegment.from_file(str(path)).set_channels(1).set_frame_rate(sr)
    samples = np.array(seg.get_array_of_samples())
    max_val = float(1 << (8 * seg.sample_width - 1))
    y = (samples.astype(np.float32)) / max_val
    return y, sr


# ---------------------------------------------------------------------------
# F0 contour extraction
# ---------------------------------------------------------------------------


def extract_f0(
    y: np.ndarray,
    sr: int,
    fmin: float = DEFAULT_FMIN,
    fmax: float = DEFAULT_FMAX,
) -> dict[str, np.ndarray]:
    """Return the F0 contour via probabilistic YIN.

    Keys: ``f0`` (Hz, NaN where unvoiced), ``times`` (s), ``voiced`` (bool mask),
    ``f0_voiced`` (Hz, voiced frames only).
    """
    import librosa

    f0, voiced_flag, _ = librosa.pyin(
        y,
        fmin=fmin,
        fmax=fmax,
        sr=sr,
        frame_length=2048,
        hop_length=512,
    )
    times = librosa.times_like(f0, sr=sr, hop_length=512)
    voiced = voiced_flag & ~np.isnan(f0)
    return {
        "f0": f0,
        "times": times,
        "voiced": voiced,
        "f0_voiced": f0[voiced],
    }


def _semitones_from(f0_hz: np.ndarray, ref_hz: float) -> np.ndarray:
    """Convert an Hz array to semitones relative to *ref_hz* (NaN-safe)."""
    out = np.full_like(f0_hz, np.nan, dtype=np.float64)
    valid = ~np.isnan(f0_hz) & (f0_hz > 0)
    out[valid] = 12.0 * np.log2(f0_hz[valid] / ref_hz)
    return out


# ---------------------------------------------------------------------------
# Full metric computation
# ---------------------------------------------------------------------------


def compute_metrics(
    path: str | Path,
    sr: int = DEFAULT_SR,
    fmin: float = DEFAULT_FMIN,
    fmax: float = DEFAULT_FMAX,
) -> dict[str, Any]:
    """Compute the full prosody metric set for an audio file.

    Returns a JSON-serialisable dict. ``f0_semitone_range`` is the pivot metric.
    """
    import librosa

    y, sr = load_audio(path, sr=sr)
    duration = len(y) / sr

    contour = extract_f0(y, sr, fmin=fmin, fmax=fmax)
    f0v = contour["f0_voiced"]

    metrics: dict[str, Any] = {
        "file": str(Path(path).name),
        "path": str(path),
        "duration_s": round(duration, 2),
        "n_voiced_frames": int(f0v.size),
    }

    if f0v.size < 5:
        # Not enough voiced signal to characterise pitch.
        metrics.update(
            {
                "f0_mean_hz": 0.0,
                "f0_median_hz": 0.0,
                "f0_std_hz": 0.0,
                "f0_p5_hz": 0.0,
                "f0_p95_hz": 0.0,
                "f0_semitone_range": 0.0,
                "f0_cv": 0.0,
                "intonation_velocity_st_s": 0.0,
                "rms_mean": 0.0,
                "rms_std": 0.0,
                "rms_db_range": 0.0,
                "voiced_fraction": 0.0,
                "onset_rate_hz": 0.0,
                "pause_count": 0,
                "pause_fraction": 0.0,
                "verdict": "NO_VOICED_SIGNAL",
            }
        )
        return metrics

    # --- Pitch level & spread (robust percentiles guard against octave errors) ---
    f0_median = float(np.median(f0v))
    f0_mean = float(np.mean(f0v))
    f0_std = float(np.std(f0v))
    p5 = float(np.percentile(f0v, 5))
    p95 = float(np.percentile(f0v, 95))
    semitone_range = 12.0 * math.log2(p95 / p5) if p5 > 0 else 0.0
    cv = f0_std / f0_mean if f0_mean > 0 else 0.0

    # --- Intonation velocity: how fast the pitch moves (semitones / second) ---
    # Computed only across consecutive voiced frame pairs to avoid jumps over
    # unvoiced gaps.
    f0_full = contour["f0"]
    voiced = contour["voiced"]
    times = contour["times"]
    st_full = _semitones_from(f0_full, f0_median)
    both_voiced = voiced[:-1] & voiced[1:]
    dst = np.abs(np.diff(st_full))[both_voiced]
    dt = np.diff(times)[both_voiced]
    moving_time = float(np.sum(dt))
    intonation_velocity = float(np.sum(dst) / moving_time) if moving_time > 0 else 0.0

    # --- RMS volume dynamics ---
    rms = librosa.feature.rms(y=y, hop_length=512)[0]
    rms_nonzero = rms[rms > 1e-6]
    rms_mean = float(np.mean(rms))
    rms_std = float(np.std(rms))
    if rms_nonzero.size > 10:
        r_p5 = float(np.percentile(rms_nonzero, 5))
        r_p95 = float(np.percentile(rms_nonzero, 95))
        rms_db_range = 20.0 * math.log10(r_p95 / r_p5) if r_p5 > 0 else 0.0
    else:
        rms_db_range = 0.0

    # --- Voiced fraction ---
    voiced_fraction = float(np.mean(voiced))

    # --- Onset (syllable) rate proxy ---
    try:
        onsets = librosa.onset.onset_detect(y=y, sr=sr, hop_length=512, backtrack=True)
        onset_rate = float(len(onsets) / duration) if duration > 0 else 0.0
    except Exception:
        onset_rate = 0.0

    # --- Pause structure ---
    try:
        intervals = librosa.effects.split(y, top_db=30, hop_length=512)
        speech_time = float(np.sum(intervals[:, 1] - intervals[:, 0])) / sr
        pause_fraction = max(0.0, 1.0 - speech_time / duration) if duration > 0 else 0.0
        pause_count = max(0, len(intervals) - 1)
    except Exception:
        pause_fraction = 0.0
        pause_count = 0

    # --- Verdict on the pivot metric ---
    if semitone_range < FLAT_ST:
        verdict = "FLAT"
    elif semitone_range < EXPRESSIVE_ST:
        verdict = "MODERATE"
    else:
        verdict = "EXPRESSIVE"

    metrics.update(
        {
            "f0_mean_hz": round(f0_mean, 2),
            "f0_median_hz": round(f0_median, 2),
            "f0_std_hz": round(f0_std, 2),
            "f0_p5_hz": round(p5, 2),
            "f0_p95_hz": round(p95, 2),
            "f0_semitone_range": round(semitone_range, 2),
            "f0_cv": round(cv, 4),
            "intonation_velocity_st_s": round(intonation_velocity, 3),
            "rms_mean": round(rms_mean, 6),
            "rms_std": round(rms_std, 6),
            "rms_db_range": round(rms_db_range, 2),
            "voiced_fraction": round(voiced_fraction, 3),
            "onset_rate_hz": round(onset_rate, 2),
            "pause_count": pause_count,
            "pause_fraction": round(pause_fraction, 3),
            "verdict": verdict,
        }
    )
    return metrics


# ---------------------------------------------------------------------------
# DTW contour distance (controllability metric)
# ---------------------------------------------------------------------------


def _voiced_semitone_series(
    path: str | Path, sr: int, fmin: float, fmax: float
) -> np.ndarray:
    """Median-centred semitone contour with unvoiced gaps linearly interpolated."""
    y, sr = load_audio(path, sr=sr)
    contour = extract_f0(y, sr, fmin=fmin, fmax=fmax)
    f0 = contour["f0"].copy()
    voiced = contour["voiced"]
    if voiced.sum() < 5:
        return np.zeros(1, dtype=np.float64)
    median = float(np.median(f0[voiced]))
    st = _semitones_from(f0, median)
    # Interpolate over NaN (unvoiced) gaps so the contour is continuous for DTW.
    idx = np.arange(st.size)
    good = ~np.isnan(st)
    st_interp = np.interp(idx, idx[good], st[good])
    return st_interp


def dtw_contour_distance(
    path_a: str | Path,
    path_b: str | Path,
    sr: int = DEFAULT_SR,
    fmin: float = DEFAULT_FMIN,
    fmax: float = DEFAULT_FMAX,
) -> float:
    """Normalised DTW distance between two F0 contours (in semitones).

    Both contours are median-centred (so absolute pitch level is removed and we
    compare *shape only*). Returns the accumulated DTW cost divided by the path
    length: ~0 means identical melody, larger means the intonation differs.
    Used to test controllability — same text + different prosody instruction:
    if the distance stays near zero the engine ignored the instruction.
    """
    import librosa

    a = _voiced_semitone_series(path_a, sr, fmin, fmax)
    b = _voiced_semitone_series(path_b, sr, fmin, fmax)
    if a.size < 2 or b.size < 2:
        return 0.0
    D, wp = librosa.sequence.dtw(X=a.reshape(1, -1), Y=b.reshape(1, -1), metric="euclidean")
    return float(D[-1, -1] / len(wp))


# ---------------------------------------------------------------------------
# Comparison plotting
# ---------------------------------------------------------------------------


def plot_contours(
    labelled_paths: dict[str, str | Path],
    out_png: str | Path,
    sr: int = DEFAULT_SR,
    fmin: float = DEFAULT_FMIN,
    fmax: float = DEFAULT_FMAX,
    title: str = "Pitch contours (semitones rel. median)",
) -> str:
    """Overlay median-centred pitch-vs-time curves for several renders.

    A flat horizontal line = monotone; a wiggly line with large vertical span =
    expressive. Saves a PNG and returns its path.
    """
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(14, 6))
    for label, path in labelled_paths.items():
        try:
            y, sr2 = load_audio(path, sr=sr)
            contour = extract_f0(y, sr2, fmin=fmin, fmax=fmax)
            f0 = contour["f0"]
            voiced = contour["voiced"]
            times = contour["times"]
            if voiced.sum() < 5:
                continue
            median = float(np.median(f0[voiced]))
            st = _semitones_from(f0, median)
            st_plot = np.where(voiced, st, np.nan)
            span = 12.0 * math.log2(
                np.percentile(f0[voiced], 95) / np.percentile(f0[voiced], 5)
            )
            ax.plot(times, st_plot, label=f"{label} (range {span:.1f} st)", linewidth=1.3, alpha=0.85)
        except Exception as exc:  # noqa: BLE001 - keep plotting the others
            ax.plot([], [], label=f"{label} (ERROR: {exc})")

    ax.axhline(0, color="grey", linewidth=0.5, linestyle="--")
    ax.set_xlabel("Time (s)")
    ax.set_ylabel("Pitch (semitones rel. median)")
    ax.set_title(title)
    ax.legend(loc="upper right", fontsize=8)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    out_png = str(out_png)
    fig.savefig(out_png, dpi=110)
    plt.close(fig)
    return out_png


def compare(
    labelled_paths: dict[str, str | Path],
    json_out: str | Path | None = None,
    plot_out: str | Path | None = None,
    sr: int = DEFAULT_SR,
    fmin: float = DEFAULT_FMIN,
    fmax: float = DEFAULT_FMAX,
) -> dict[str, Any]:
    """Compute metrics for every render, optionally write JSON + contour PNG.

    Returns ``{"metrics": {label: metrics}, "plot": path|None}``.
    """
    out: dict[str, Any] = {"metrics": {}, "plot": None}
    for label, path in labelled_paths.items():
        out["metrics"][label] = compute_metrics(path, sr=sr, fmin=fmin, fmax=fmax)

    if plot_out:
        out["plot"] = plot_contours(labelled_paths, plot_out, sr=sr, fmin=fmin, fmax=fmax)

    if json_out:
        Path(json_out).parent.mkdir(parents=True, exist_ok=True)
        with open(json_out, "w", encoding="utf-8") as f:
            json.dump(out["metrics"], f, indent=2, ensure_ascii=False)

    return out


def print_table(metrics_by_label: dict[str, dict[str, Any]]) -> None:
    """Print a comparison table to stdout (pivot metric first)."""
    cols = [
        ("f0_semitone_range", "ST_range", "{:8.2f}"),
        ("f0_cv", "F0_CV", "{:8.4f}"),
        ("intonation_velocity_st_s", "Inton.v", "{:8.2f}"),
        ("f0_median_hz", "F0_med", "{:8.1f}"),
        ("rms_db_range", "RMS_dB", "{:8.2f}"),
        ("onset_rate_hz", "Onset/s", "{:8.2f}"),
        ("duration_s", "Dur_s", "{:8.1f}"),
        ("verdict", "Verdict", "{:>12s}"),
    ]
    header = f"{'Label':<22}" + "".join(f"{c[1]:>10}" for c in cols)
    print("=" * len(header))
    print(header)
    print("-" * len(header))
    for label, m in metrics_by_label.items():
        row = f"{label[:22]:<22}"
        for key, _, fmt in cols:
            val = m.get(key, "")
            try:
                row += f"{fmt.format(val):>10}"
            except (ValueError, TypeError):
                row += f"{str(val):>10}"
        print(row)
    print("=" * len(header))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Prosody metrics (F0 melody) for TTS renders.")
    p.add_argument(
        "inputs",
        nargs="+",
        help="Audio files. Use label=path to name a render, else the filename is the label.",
    )
    p.add_argument("--json", dest="json_out", default=None, help="Write metrics JSON here.")
    p.add_argument("--plot", dest="plot_out", default=None, help="Write contour overlay PNG here.")
    p.add_argument("--sr", type=int, default=DEFAULT_SR)
    p.add_argument("--fmin", type=float, default=DEFAULT_FMIN)
    p.add_argument("--fmax", type=float, default=DEFAULT_FMAX)
    p.add_argument(
        "--dtw",
        action="store_true",
        help="Also print a pairwise DTW contour-distance matrix (controllability).",
    )
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    args = _parse_args(argv)
    labelled: dict[str, str] = {}
    for item in args.inputs:
        if "=" in item:
            label, path = item.split("=", 1)
        else:
            label, path = Path(item).stem, item
        labelled[label] = path

    result = compare(
        labelled,
        json_out=args.json_out,
        plot_out=args.plot_out,
        sr=args.sr,
        fmin=args.fmin,
        fmax=args.fmax,
    )
    print_table(result["metrics"])
    if result["plot"]:
        print(f"\nContour plot: {result['plot']}")
    if args.json_out:
        print(f"Metrics JSON: {args.json_out}")

    if args.dtw and len(labelled) > 1:
        print("\nPairwise DTW contour distance (0 = identical melody):")
        labels = list(labelled)
        for i, la in enumerate(labels):
            for lb in labels[i + 1 :]:
                d = dtw_contour_distance(
                    labelled[la], labelled[lb], sr=args.sr, fmin=args.fmin, fmax=args.fmax
                )
                print(f"  {la:<20} <-> {lb:<20} : {d:.3f}")


if __name__ == "__main__":
    main()
