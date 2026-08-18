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

# --- Structural (melody-level) criteria -------------------------------------
# motion/pct_flat are LOCAL measures: a drone alternating two adjacent notes
# has perfectly normal step size and slips through. These three catch the
# shape of the melody itself. Calibrated on three references measured
# 2026-08-18 (see docstring of melody_stats).
EFFNOTES_DRONE_MAX = 7.0     # 2**entropy over note names; kokoro 11.8, v4 6.0
TOP3_DRONE_MIN = 65.0        # % of syllables on the 3 commonest notes
MOTIF3_DRONE_MIN = 60.0      # % of 3-gram positions inside a repeated motif
MIN_SYLL_FOR_STRUCTURE = 60  # below this, concentration stats are unreliable


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


def melody_stats(notes):
    """Structural description of a note sequence: how many notes it really uses,
    how concentrated it is, and how much of it is literal repetition.

    Reference values measured 2026-08-18 on Boule de Suif material:

    ==========================  =========  ======  =========  ===========
    clip                        eff_notes  top-3   motif-3    verdict
    ==========================  =========  ======  =========  ===========
    v1 kokoro (no cloning)          11.8   44.5%      14.5%   EXPRESSIVE
    v2 fishaudio tags-only           5.3   79.7%      90.9%   FLAT
    v4 extrait_ouverture_2min30      6.0   72.8%      82.2%   DRONE
    ==========================  =========  ======  =========  ===========

    Returns a dict; keys are None (with ``structure_na_reason`` set) when the
    sample is too short for the concentration statistics to mean anything --
    never silently zero, which would read as "clean".
    """
    import collections, math
    n = len(notes)
    out = {"n_notes_distinct": len(set(notes)), "n_syllables_scored": n}
    if n < MIN_SYLL_FOR_STRUCTURE:
        out.update({
            "effective_notes": None, "top3_note_pct": None,
            "motif3_repeat_pct": None, "top_motifs": [],
            "structure_na_reason": "only %d syllables, need >= %d" % (n, MIN_SYLL_FOR_STRUCTURE),
        })
        return out
    c = collections.Counter(notes)
    H = -sum((v / n) * math.log2(v / n) for v in c.values())
    top = c.most_common(3)
    grams = collections.Counter(tuple(notes[i:i + 3]) for i in range(n - 2))
    tot = n - 2
    rep = sum(v for g, v in grams.items() if v >= 2)
    out.update({
        "effective_notes": round(2 ** H, 1),
        "note_entropy_bits": round(H, 2),
        "top3_note_pct": round(100.0 * sum(v for _, v in top) / n, 1),
        "top3_notes": [k for k, _ in top],
        "motif3_repeat_pct": round(100.0 * rep / tot, 1),
        "top_motifs": ["-".join(g) + " x%d" % v for g, v in grams.most_common(3)],
        "structure_na_reason": None,
    })
    return out


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
        # max-minus-min is driven by single outlier syllables: on the v4 extract
        # ONE syllable out of 401 (E3, 0.2%) lifted span from ~8 to 12.24 st.
        # Report the robust interdecile span alongside it.
        result["melodic_span_p5p95_st"] = round(
            float(np.percentile(midis, 95) - np.percentile(midis, 5)), 2
        )
        result.update(melody_stats([s["note"] for s in syllables]))

        motion = result["mean_abs_interval_st"]
        flat_pct = result["pct_flat_transitions"]
        if motion < MOTION_FLAT_MAX or flat_pct >= FLATPCT_FLAT_MIN:
            result["verdict"] = "FLAT"
        elif motion < MOTION_MODERATE_MAX or flat_pct >= FLATPCT_MODERATE_MIN:
            result["verdict"] = "MODERATE"
        else:
            result["verdict"] = "EXPRESSIVE"

        # Structural override: a repeating melody is monotonous even when its
        # local step size looks healthy. The v4 extract missed FLAT by 0.21
        # st and 1.2 points on the two local axes while spending 73% of its
        # 401 syllables on three adjacent semitones.
        drone_reasons = []
        if result.get("effective_notes") is not None:
            if result["effective_notes"] < EFFNOTES_DRONE_MAX:
                drone_reasons.append(
                    "effective_notes %.1f < %.1f" % (result["effective_notes"], EFFNOTES_DRONE_MAX))
            if result["top3_note_pct"] >= TOP3_DRONE_MIN:
                drone_reasons.append(
                    "top3_note_pct %.1f%% >= %.1f%%" % (result["top3_note_pct"], TOP3_DRONE_MIN))
            if result["motif3_repeat_pct"] >= MOTIF3_DRONE_MIN:
                drone_reasons.append(
                    "motif3_repeat_pct %.1f%% >= %.1f%%" % (result["motif3_repeat_pct"], MOTIF3_DRONE_MIN))
        result["drone_reasons"] = drone_reasons
        if drone_reasons:
            result["verdict"] = "DRONE"
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
        f"  span={a['melodic_span_st']} st (p5-p95 {a.get('melodic_span_p5p95_st')} st)"
        f" | motion={a['mean_abs_interval_st']} st/syll"
        f" | flat-transitions={a['pct_flat_transitions']}% | rate={a['syllable_rate_hz']}/s"
        f" | median={a['median_pitch_hz']} Hz"
    )
    if a.get("structure_na_reason"):
        print(f"  structure: n/a ({a['structure_na_reason']})")
    elif a.get("effective_notes") is not None:
        print(
            f"  structure: {a['effective_notes']} notes effectives sur {a['n_notes_distinct']} distinctes"
            f" | top-3 {a['top3_notes']} = {a['top3_note_pct']}%"
            f" | motifs 3-notes repetes {a['motif3_repeat_pct']}%"
        )
        print(f"  motifs   : {' | '.join(a.get('top_motifs', []))}")
    print(f"  VERDICT  : {a['verdict']}")
    for r in a.get("drone_reasons", []):
        print(f"             drone: {r}")


def _synth(midi_sequence, syll_per_s=3.0, sr=22050):
    """Build a syllable-like signal whose f0 follows the given MIDI sequence."""
    import numpy as np
    dur = 1.0 / syll_per_s
    n = int(sr * dur)
    t = np.arange(n) / sr
    env = np.hanning(n) ** 0.5  # amplitude dip between syllables -> nuclei
    out = []
    for m in midi_sequence:
        f = 440.0 * (2.0 ** ((m - 69) / 12.0))
        sig = np.zeros(n)
        for k in (1, 2, 3, 4):  # harmonics so pyin locks on
            sig += (1.0 / k) * np.sin(2 * np.pi * f * k * t)
        out.append(sig * env)
    y = np.concatenate(out)
    return (y / (np.max(np.abs(y)) + 1e-9) * 0.9).astype("float32"), sr


def self_test() -> int:
    """Positive control. A detector that cannot fail loudly is worthless:
    this asserts the analyzer actually FIRES on a synthetic drone and stays
    quiet on a synthetic varied melody. Exit non-zero on either failure.
    """
    import tempfile, os, random
    import numpy as np
    import soundfile as sf

    random.seed(0)
    n = 120
    drone = [45 + random.choice([0, 0, 0, 1, -1]) for _ in range(n)]   # A2 +/- 1 st
    varied = [45 + random.choice(range(-8, 13)) for _ in range(n)]      # 21-st ambitus

    ok = True
    tmp = tempfile.mkdtemp(prefix="syllpitch_selftest_")
    for name, seq, must_be_drone in (("drone", drone, True), ("varied", varied, False)):
        y, sr = _synth(seq)
        wav = os.path.join(tmp, name + ".wav")
        sf.write(wav, y, sr)
        a = analyze_syllables(wav)
        is_drone = a.get("verdict") == "DRONE"
        status = "PASS" if is_drone == must_be_drone else "FAIL"
        if status == "FAIL":
            ok = False
        print(
            "[self-test] %-6s expected drone=%-5s got verdict=%-10s"
            " eff_notes=%s top3=%s motif3=%s n_syll=%d -> %s"
            % (name, must_be_drone, a.get("verdict"), a.get("effective_notes"),
               a.get("top3_note_pct"), a.get("motif3_repeat_pct"),
               a.get("n_syllables", 0), status)
        )
    print("[self-test] %s" % ("OK" if ok else "FAILED -- the detector is not measuring what it claims"))
    return 0 if ok else 1


def main() -> None:
    ap = argparse.ArgumentParser(description="Syllable-level pitch analyzer")
    ap.add_argument("clips", nargs="*", help="audio files (mp3/wav)")
    ap.add_argument("--out-dir", default=None, help="dir for the score PNG")
    ap.add_argument("--json", default=None, help="write all analyses to this JSON")
    ap.add_argument("--dip-db", type=float, default=2.0)
    ap.add_argument("--self-test", action="store_true",
                    help="run the synthetic drone/varied positive control and exit")
    args = ap.parse_args()

    if args.self_test:
        raise SystemExit(self_test())

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
