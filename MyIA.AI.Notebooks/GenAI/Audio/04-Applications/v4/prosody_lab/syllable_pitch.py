"""syllable_pitch.py — syllable-level pitch analyzer ("partition de musique").

Mandated instrument (#1877, user directive 2026-06-12 #5): give the pitch of
each SYLLABLE "comme une partition de musique" — the only way to verify TTS
expressivity autonomously at the syllable grain, beyond the GLOBAL F0 contour
that ``prosody_metrics.py`` already provides.

Method (fully autonomous — no forced aligner, no text, no model download):

1. F0 contour via ``librosa.pyin`` (reuses ``prosody_metrics.extract_f0``).
2. Syllable-nucleus detection adapted from De Jong & Wempe (2009), "Praat
   script to detect syllable nuclei": peaks of the intensity (loudness)
   envelope that (a) rise at least ``dip_db`` above their neighbouring valleys
   and (b) fall in VOICED regions (a nucleus is a voiced vowel).
3. Each nucleus -> one syllable. Its pitch = median voiced F0 over the window
   between the surrounding intensity valleys. Converted to Hz, MIDI note, note
   name (C/C#/.../B + octave) -> the "musical score".
4. Melodic metrics: span (max-min in semitones), mean absolute interval between
   consecutive syllables (melodic motion; near 0 == monotone chant), fraction
   of "flat" transitions (< 1 st), direction changes.
5. ``plot_score`` renders a piano-roll / staff view: each syllable a note bar at
   its pitch & duration, the continuous F0 faint behind, a melody line on top.

CLI::

    python syllable_pitch.py CLIP.mp3 [CLIP2.mp3 ...] [--out-dir DIR] [--json OUT]

Env: base Python 3.13 has librosa 0.11 / numpy / scipy / matplotlib / soundfile.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Optional

import numpy as np

# Reuse the validated F0 extractor from the global-contour instrument.
try:
    from prosody_metrics import extract_f0, load_audio
except ImportError:  # pragma: no cover - allow running from another cwd
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from prosody_metrics import extract_f0, load_audio


HOP_LENGTH = 512
FRAME_LENGTH = 2048
NOTE_NAMES = ["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

# Verdict thresholds. The GLOBAL span (max-min) is outlier-driven and too
# lenient at the syllable grain — a monotone chant with two big drops scores a
# wide span yet sounds flat. The robust monotony discriminators are the
# per-syllable MOTION (mean |interval|) and the FLAT-TRANSITION fraction
# (consecutive syllables within < 1 st). Verdict is built on those; span is
# reported for reference only.
MOTION_FLAT_MAX = 1.0       # st/syllable: below this == monotone chant
MOTION_MODERATE_MAX = 1.6   # st/syllable
FLATPCT_FLAT_MIN = 55.0     # % flat transitions above this == chant
FLATPCT_MODERATE_MIN = 40.0 # %


def hz_to_midi(f0_hz: float) -> float:
    """Continuous MIDI note number for a frequency in Hz."""
    return 69.0 + 12.0 * math.log2(f0_hz / 440.0)


def midi_to_note_name(midi: float) -> str:
    """Nearest equal-tempered note name, e.g. 110 Hz -> 'A2'."""
    m = int(round(midi))
    return f"{NOTE_NAMES[m % 12]}{m // 12 - 1}"


def _intensity_db(y: np.ndarray) -> np.ndarray:
    """RMS loudness envelope in dB, frame-aligned with the pyin F0 frames."""
    import librosa

    rms = librosa.feature.rms(
        y=y, frame_length=FRAME_LENGTH, hop_length=HOP_LENGTH
    )[0]
    rms = np.maximum(rms, 1e-8)
    return 20.0 * np.log10(rms)


def detect_syllable_nuclei(
    intensity_db: np.ndarray,
    voiced: np.ndarray,
    times: np.ndarray,
    dip_db: float = 2.0,
    silence_db_below_max: float = 25.0,
    min_spacing_s: float = 0.09,
) -> List[int]:
    """Indices of intensity-envelope frames that are syllable nuclei.

    A nucleus is a local intensity peak that (a) is voiced, (b) sits at least
    ``silence_db_below_max`` dB above the silence floor, and (c) rises at least
    ``dip_db`` above the valley separating it from its neighbours, with peaks
    no closer than ``min_spacing_s`` (French syllable rate caps ~8/s).
    """
    from scipy.signal import find_peaks

    n = len(intensity_db)
    if n == 0:
        return []

    # Align voiced mask length to the intensity frames (pyin / rms can differ
    # by one frame depending on padding).
    m = min(n, len(voiced), len(times))
    intensity_db = intensity_db[:m]
    voiced = voiced[:m]

    floor = float(np.max(intensity_db)) - silence_db_below_max
    dt = float(np.median(np.diff(times[:m]))) if m > 1 else HOP_LENGTH / 22050.0
    distance = max(1, int(round(min_spacing_s / dt)))

    peaks, _ = find_peaks(
        intensity_db,
        height=floor,
        prominence=dip_db,
        distance=distance,
    )
    # Keep only voiced nuclei (vowels carry pitch).
    return [int(p) for p in peaks if voiced[p]]


def analyze_syllables(
    path: str,
    fmin: float = 65.0,
    fmax: float = 500.0,
    dip_db: float = 2.0,
) -> Dict:
    """Transcribe a clip into per-syllable notes + melodic metrics.

    Returns a dict with ``syllables`` (list of note dicts), ``melodic_*``
    metrics, and a ``verdict``. Designed to be JSON-serialisable.
    """
    y, sr = load_audio(path)
    f0d = extract_f0(y, sr, fmin=fmin, fmax=fmax)
    f0 = f0d["f0"]
    times = f0d["times"]
    voiced = f0d["voiced"]

    intensity = _intensity_db(y)
    nuclei = detect_syllable_nuclei(intensity, voiced, times, dip_db=dip_db)

    # Valley boundaries: midpoints between consecutive nuclei delimit the window
    # over which each nucleus' pitch is measured.
    syllables: List[Dict] = []
    m = min(len(f0), len(times), len(voiced))
    for i, p in enumerate(nuclei):
        left = 0 if i == 0 else (nuclei[i - 1] + p) // 2
        right = (m - 1) if i == len(nuclei) - 1 else (p + nuclei[i + 1]) // 2
        seg_f0 = f0[left : right + 1]
        seg_v = voiced[left : right + 1]
        vals = seg_f0[seg_v & np.isfinite(seg_f0)]
        if vals.size == 0:
            continue
        f0_hz = float(np.median(vals))
        if not (fmin <= f0_hz <= fmax):
            continue
        midi = hz_to_midi(f0_hz)
        syllables.append(
            {
                "index": len(syllables),
                "t_start": round(float(times[left]), 3),
                "t_center": round(float(times[p]), 3),
                "t_end": round(float(times[right]), 3),
                "dur": round(float(times[right] - times[left]), 3),
                "f0_hz": round(f0_hz, 1),
                "midi": round(midi, 2),
                "note": midi_to_note_name(midi),
                "intensity_db": round(float(intensity[min(p, len(intensity) - 1)]), 1),
            }
        )

    result: Dict = {
        "path": str(path),
        "label": Path(path).stem,
        "duration_s": round(float(len(y) / sr), 2),
        "n_syllables": len(syllables),
        "syllables": syllables,
    }

    if len(syllables) >= 2:
        midis = np.array([s["midi"] for s in syllables])
        rel = midis - np.median(midis)  # semitones relative to the "key"
        intervals = np.abs(np.diff(midis))  # melodic motion per syllable
        directions = np.sign(np.diff(midis))
        dir_changes = int(np.sum(np.abs(np.diff(directions[directions != 0])) > 0)) \
            if np.any(directions != 0) else 0
        span = float(np.max(midis) - np.min(midis))
        result.update(
            {
                "syllable_rate_hz": round(len(syllables) / max(result["duration_s"], 0.1), 2),
                "melodic_span_st": round(span, 2),
                "mean_abs_interval_st": round(float(np.mean(intervals)), 2),
                "median_pitch_hz": round(float(np.median([s["f0_hz"] for s in syllables])), 1),
                "pct_flat_transitions": round(float(np.mean(intervals < 1.0) * 100), 1),
                "direction_changes": dir_changes,
                "rel_semitones": [round(float(x), 2) for x in rel],
            }
        )
        motion = result["mean_abs_interval_st"]
        flat_pct = result["pct_flat_transitions"]
        if motion < MOTION_FLAT_MAX or flat_pct >= FLATPCT_FLAT_MIN:
            result["verdict"] = "FLAT"
        elif motion < MOTION_MODERATE_MAX or flat_pct >= FLATPCT_MODERATE_MIN:
            result["verdict"] = "MODERATE"
        else:
            result["verdict"] = "EXPRESSIVE"
    else:
        result["verdict"] = "INSUFFICIENT"
    return result


def plot_score(analyses, out_png: str, title: Optional[str] = None) -> str:
    """Render syllable notes as a piano-roll / staff ("partition de musique").

    Accepts a single analysis dict or a list of them (stacked subplots for
    side-by-side comparison of several clips).
    """
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    if isinstance(analyses, dict):
        analyses = [analyses]
    n = len(analyses)
    fig, axes = plt.subplots(n, 1, figsize=(13, 3.0 * n + 0.5), squeeze=False)

    for ax, a in zip(axes[:, 0], analyses):
        sylls = a.get("syllables", [])
        if not sylls:
            ax.set_title(f"{a.get('label', '?')} — no syllables detected")
            continue
        midis = [s["midi"] for s in sylls]
        for s in sylls:
            # one note bar: horizontal segment at the syllable pitch over its span
            ax.plot(
                [s["t_start"], s["t_end"]],
                [s["midi"], s["midi"]],
                lw=6,
                solid_capstyle="round",
                color="#2c6fbb",
                alpha=0.85,
            )
        centers = [s["t_center"] for s in sylls]
        ax.plot(centers, midis, "-", color="#d1495b", lw=1.0, alpha=0.7)  # melody line
        ax.plot(centers, midis, ".", color="#d1495b", ms=4)

        lo, hi = int(math.floor(min(midis))) - 1, int(math.ceil(max(midis))) + 1
        ticks = list(range(lo, hi + 1))
        ax.set_yticks(ticks)
        ax.set_yticklabels([midi_to_note_name(t) for t in ticks], fontsize=7)
        ax.grid(axis="y", ls=":", alpha=0.4)
        ax.set_ylabel("note")
        verdict = a.get("verdict", "?")
        span = a.get("melodic_span_st", 0)
        interval = a.get("mean_abs_interval_st", 0)
        ax.set_title(
            f"{a.get('label','?')}  |  {a.get('n_syllables',0)} syll  "
            f"span={span} st  motion={interval} st/syll  -> {verdict}",
            fontsize=9,
        )
    axes[-1, 0].set_xlabel("time (s)")
    if title:
        fig.suptitle(title, fontsize=11)
    fig.tight_layout()
    Path(out_png).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_png, dpi=110)
    plt.close(fig)
    return out_png


def print_score_table(a: Dict) -> None:
    """Pretty-print the per-syllable note sequence + melodic summary."""
    print(f"\n=== {a['label']}  ({a['duration_s']}s, {a['n_syllables']} syllables) ===")
    if a.get("verdict") == "INSUFFICIENT":
        print("  insufficient voiced syllables to transcribe")
        return
    notes = " ".join(s["note"] for s in a["syllables"])
    print(f"  melody: {notes}")
    print(
        f"  span={a['melodic_span_st']} st | motion={a['mean_abs_interval_st']} st/syll"
        f" | flat-transitions={a['pct_flat_transitions']}% | rate={a['syllable_rate_hz']}/s"
        f" | median={a['median_pitch_hz']} Hz -> {a['verdict']}"
    )


def main() -> None:
    ap = argparse.ArgumentParser(description="Syllable-level pitch analyzer")
    ap.add_argument("clips", nargs="+", help="audio files (mp3/wav)")
    ap.add_argument("--out-dir", default=None, help="dir for the score PNG")
    ap.add_argument("--json", default=None, help="write all analyses to this JSON")
    ap.add_argument("--dip-db", type=float, default=2.0)
    args = ap.parse_args()

    analyses = []
    for clip in args.clips:
        a = analyze_syllables(clip, dip_db=args.dip_db)
        print_score_table(a)
        analyses.append(a)

    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(json.dumps(analyses, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"\n[json] {args.json}")

    out_dir = args.out_dir or str(Path(args.clips[0]).parent)
    png = str(Path(out_dir) / "syllable_score.png")
    plot_score(analyses, png, title="Syllable pitch — partition")
    print(f"[png ] {png}")


if __name__ == "__main__":
    main()
