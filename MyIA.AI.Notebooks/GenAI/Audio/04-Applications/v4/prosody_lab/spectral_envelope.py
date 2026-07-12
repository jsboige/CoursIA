"""spectral_envelope.py — energy-envelope + spectral-signature analyzer.

The second and third "eye" of the prosody lab (#1877/#1273, user directive
2026-06-13). ``syllable_pitch.py`` measures the MELODY; WER measures the words.
Neither detects the two defects the user hears but the earlier tools missed:

* **Essoufflement** — the voice runs out of breath over a too-long segment: the
  loudness ENVELOPE decays and the timbre darkens toward the end (A__W2 fish
  hot, where prosody "s'endort" after the first syllable). Caught here by
  ``decay_db`` (median energy of the last third minus the first third), the
  longest un-broken voiced run (a narrator who never pauses to breathe), and the
  spectral-centroid slope (effort/brightness fading).

* **Inconsistance de voix** — a chunked render stitches together segments that
  are not the SAME speaker (A__W3 qwen VoiceDesign re-*designs* the voice on each
  chunk -> "3 nationalités" in one narrator line). Caught here by a per-window
  MFCC timbre fingerprint, a window x window self-similarity matrix, and a
  cluster count: one voice -> one cluster; several distinct accents -> several
  clusters with low cross-window similarity.

For a dialogue, the same voice-consistency tool tells whether the narrator and
the characters are actually differentiated (>=2 clusters, aligned to the turns)
or whether the narrator voice BLEEDS over everyone (a single cluster — the
defect in extract B).

Fully autonomous: librosa MFCC/RMS/centroid + scikit-learn KMeans/silhouette.
No pretrained speaker model needed — classic MFCC self-similarity is enough to
expose gross accent/timbre changes; a neural d-vector would only sharpen it.

CLI::

    python spectral_envelope.py CLIP.mp3 [CLIP2 ...] [--out-dir DIR] [--json OUT]

Env: base Python 3.13 has librosa 0.11 / numpy / scipy / sklearn / matplotlib.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

try:
    from prosody_metrics import load_audio
except ImportError:  # pragma: no cover - allow running from another cwd
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from prosody_metrics import load_audio


SR = 22050
HOP = 512
NFFT = 2048
N_MFCC = 20

# Active-speech gate: frames within this many dB of the peak are "speech".
SILENCE_DB_BELOW_PEAK = 35.0
MIN_PAUSE_S = 0.18          # a breath/pause is at least this much silence
WINDOW_S = 2.0             # timbre-fingerprint window (long enough to average
                           # out phonetic content -> speaker identity dominates)

# Breath / essoufflement verdict (provisional; calibrated against the bench).
DECAY_FADING_DB = -2.5      # last third quieter than first third by this -> fading
DECAY_WINDED_DB = -4.0
LONG_RUN_S = 7.0            # a voiced stretch this long without a pause = no breath

# Voice-consistency verdict, from cluster separation of [mean,std]-MFCC windows.
# A single voice splits weakly (low silhouette / CH); genuinely distinct voices
# (a chunked re-design, a narrator bleeding over a character) split cleanly.
SIL_MIN = 0.20             # silhouette above this -> the >=2 split is real
CH_MIN = 7.5               # Calinski-Harabasz separation backing a >=2 verdict
SIL_DRIFT = 0.16           # weak-but-present split -> flag as drifting timbre


# ---------------------------------------------------------------------------
# Frame features
# ---------------------------------------------------------------------------


def _frame_features(y: np.ndarray, sr: int):
    """RMS(dB), spectral centroid, MFCC and time axis, all length-aligned."""
    import librosa

    rms = librosa.feature.rms(y=y, frame_length=NFFT, hop_length=HOP)[0]
    rms_db = 20.0 * np.log10(np.maximum(rms, 1e-8))
    cent = librosa.feature.spectral_centroid(y=y, sr=sr, n_fft=NFFT, hop_length=HOP)[0]
    mfcc = librosa.feature.mfcc(y=y, sr=sr, n_mfcc=N_MFCC, n_fft=NFFT, hop_length=HOP)
    T = min(len(rms_db), len(cent), mfcc.shape[1])
    rms_db, cent, mfcc = rms_db[:T], cent[:T], mfcc[:, :T]
    times = librosa.times_like(rms_db, sr=sr, hop_length=HOP)[:T]
    return times, rms_db, cent, mfcc


def _active_and_pauses(times: np.ndarray, rms_db: np.ndarray):
    """Active-speech mask + breath pauses + voiced runs from the dB envelope."""
    peak = float(np.max(rms_db))
    thr = peak - SILENCE_DB_BELOW_PEAK
    active = rms_db > thr
    dt = float(np.median(np.diff(times))) if len(times) > 1 else HOP / SR

    pauses: List[Tuple[float, float]] = []
    voiced_runs: List[Tuple[float, float, float]] = []
    i, n = 0, len(active)
    while i < n:
        j = i
        while j < n and active[j] == active[i]:
            j += 1
        t0, t1 = float(times[i]), float(times[min(j, n - 1)])
        dur = (j - i) * dt
        if not active[i] and dur >= MIN_PAUSE_S:
            pauses.append((t0, t1))
        elif active[i]:
            voiced_runs.append((t0, t1, dur))
        i = j
    return active, thr, pauses, voiced_runs


def _breath(times, rms_db, cent, active, pauses, voiced_runs) -> Dict:
    """Energy-envelope decay + breath structure (the essoufflement detector)."""
    ta = times[active]
    da = rms_db[active]
    ca = cent[active]
    if ta.size >= 6:
        t0, t1 = float(ta[0]), float(ta[-1])
        span = max(t1 - t0, 1e-3)
        b1 = ta < t0 + span / 3.0
        b3 = ta > t1 - span / 3.0
        med1 = float(np.median(da[b1])) if b1.any() else float(np.median(da))
        med3 = float(np.median(da[b3])) if b3.any() else float(np.median(da))
        decay_db = med3 - med1
        slope_db_s = float(np.polyfit(ta, da, 1)[0])
        cent_slope = float(np.polyfit(ta, ca, 1)[0])
    else:
        decay_db = slope_db_s = cent_slope = 0.0

    max_run = max((r[2] for r in voiced_runs), default=0.0)
    dur = float(times[-1]) if len(times) else 0.0
    pause_rate = len(pauses) / max(dur, 0.1)

    if decay_db <= DECAY_WINDED_DB and max_run >= LONG_RUN_S:
        verdict = "WINDED"
    elif decay_db <= DECAY_FADING_DB:
        verdict = "FADING"
    else:
        verdict = "STEADY"

    return {
        "decay_db": round(decay_db, 2),
        "energy_slope_db_s": round(slope_db_s, 2),
        "centroid_slope_hz_s": round(cent_slope, 1),
        "max_voiced_run_s": round(max_run, 2),
        "n_pauses": len(pauses),
        "pause_rate_hz": round(pause_rate, 2),
        "breath_verdict": verdict,
    }


def _voice(times, mfcc, active, window_s: float = WINDOW_S):
    """Per-window timbre fingerprint -> voice-consistency metrics + self-sim.

    Returns (metrics_dict, centers, self_sim_matrix). Each window is fingerprinted
    by the [mean, std] of its MFCC(1..19) — a 2 s window is long enough that
    phonetic content averages out and what remains is the speaker's timbre. The
    windows are standardized, then KMeans (k=1..3) is scored by silhouette and
    Calinski-Harabasz: a single voice splits weakly; genuinely distinct voices
    (a chunk re-design, a narrator bleeding over a character) split cleanly. The
    self-similarity matrix for the heatmap is the cosine between standardized
    fingerprints, so a concatenation shows dark off-diagonal blocks at the joins.
    """
    from numpy.linalg import norm
    from sklearn.cluster import KMeans
    from sklearn.metrics import calinski_harabasz_score, silhouette_score
    from sklearn.preprocessing import StandardScaler

    M = mfcc[1:, :]  # drop MFCC0 (overall energy) -> keep timbre shape
    dt = float(np.median(np.diff(times))) if len(times) > 1 else HOP / SR
    wlen = max(1, int(round(window_s / dt)))

    feats: List[np.ndarray] = []
    centers: List[float] = []
    i, n = 0, mfcc.shape[1]
    while i < n:
        j = min(i + wlen, n)
        a = active[i:j]
        if a.sum() >= max(5, wlen // 3):
            block = M[:, i:j][:, a]
            feats.append(np.concatenate([block.mean(axis=1), block.std(axis=1)]))
            centers.append(float(times[(i + j) // 2]))
        i = j
    V = np.array(feats)

    out: Dict = {"n_windows": int(len(V))}
    if len(V) < 4:
        out.update(
            voice_verdict="INSUFFICIENT", n_voice_clusters=1,
            timbre_sim_mean=1.0, silhouette=0.0, ch_separation=0.0,
        )
        return out, centers, None

    Z = StandardScaler().fit_transform(V)
    Zn = Z / np.maximum(norm(Z, axis=1, keepdims=True), 1e-8)
    S = Zn @ Zn.T  # cosine self-similarity of standardized fingerprints
    iu = np.triu_indices(len(V), k=1)
    sim_mean = float(np.mean(S[iu]))

    best_k, best_sil, best_ch = 1, -1.0, 0.0
    for k in range(2, min(4, len(V) - 1) + 1):
        try:
            lab = KMeans(n_clusters=k, n_init=10, random_state=0).fit_predict(Z)
            sil = silhouette_score(Z, lab)
            ch = calinski_harabasz_score(Z, lab)
        except Exception:
            continue
        if sil > best_sil:
            best_sil, best_k, best_ch = sil, k, ch

    # Verdict from cluster separation only (the identity signal that survives
    # phonetic averaging). raw mean-MFCC cosine was discarded: dominated by
    # phoneme, not speaker, so it cried wolf on every clip.
    if best_sil >= SIL_MIN and best_ch >= CH_MIN:
        n_clusters, verdict = best_k, "INCONSISTENT"
    elif best_sil >= SIL_DRIFT:
        n_clusters, verdict = best_k, "DRIFTING"
    else:
        n_clusters, verdict = 1, "CONSISTENT"

    out.update(
        voice_verdict=verdict,
        n_voice_clusters=int(n_clusters),
        timbre_sim_mean=round(sim_mean, 3),
        silhouette=round(float(max(best_sil, 0.0)), 3),
        ch_separation=round(float(best_ch), 1),
    )
    return out, centers, S


def analyze_spectral(path: str) -> Dict:
    """Full energy-envelope + spectral-signature analysis of one clip."""
    y, sr = load_audio(path)
    times, rms_db, cent, mfcc = _frame_features(y, sr)
    active, thr, pauses, voiced_runs = _active_and_pauses(times, rms_db)
    breath = _breath(times, rms_db, cent, active, pauses, voiced_runs)
    voice, centers, S = _voice(times, mfcc, active)

    result: Dict = {
        "path": str(path),
        "label": Path(path).stem,
        "duration_s": round(float(len(y) / sr), 2),
        **breath,
        **voice,
    }
    # Heavy arrays kept out of the JSON; carried for the plotter via a private key.
    result["_plot"] = {
        "times": times,
        "rms_db": rms_db,
        "cent": cent,
        "thr": thr,
        "pauses": pauses,
        "centers": centers,
        "S": S,
    }
    return result


def plot_signature(a: Dict, out_png: str, title: Optional[str] = None) -> str:
    """3-panel diagnostic: energy envelope, timbre brightness, voice self-sim."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    p = a.get("_plot", {})
    times = p.get("times")
    rms_db = p.get("rms_db")
    cent = p.get("cent")
    S = p.get("S")

    fig, axes = plt.subplots(1, 3, figsize=(15, 3.6))

    # Panel 1 — energy envelope + pauses + decay trend.
    ax = axes[0]
    if times is not None:
        ax.plot(times, rms_db, color="#2c6fbb", lw=0.9)
        ax.axhline(p["thr"], color="grey", ls=":", lw=0.8)
        for (t0, t1) in p.get("pauses", []):
            ax.axvspan(t0, t1, color="orange", alpha=0.18)
        act = rms_db > p["thr"]
        if act.sum() > 3:
            ta, da = times[act], rms_db[act]
            fit = np.polyfit(ta, da, 1)
            ax.plot(ta, np.polyval(fit, ta), color="#d1495b", lw=1.4)
    ax.set_title(
        f"energy  decay={a['decay_db']}dB  run={a['max_voiced_run_s']}s  "
        f"pauses={a['n_pauses']} -> {a['breath_verdict']}",
        fontsize=8,
    )
    ax.set_xlabel("time (s)")
    ax.set_ylabel("dB")

    # Panel 2 — spectral centroid (timbre brightness) trajectory.
    ax = axes[1]
    if times is not None:
        ax.plot(times, cent, color="#5b8c5a", lw=0.8, alpha=0.9)
        act = rms_db > p["thr"]
        if act.sum() > 3:
            ta, ca = times[act], cent[act]
            fit = np.polyfit(ta, ca, 1)
            ax.plot(ta, np.polyval(fit, ta), color="#d1495b", lw=1.4)
    ax.set_title(f"timbre brightness  slope={a['centroid_slope_hz_s']} Hz/s", fontsize=8)
    ax.set_xlabel("time (s)")
    ax.set_ylabel("centroid (Hz)")

    # Panel 3 — voice self-similarity matrix (block = distinct voice).
    # Scale to the off-diagonal data range so the block structure is visible
    # (the standardized-cosine off-diagonal sits well below 1.0; a fixed floor
    # would clip every cell to black).
    ax = axes[2]
    if S is not None and S.shape[0] > 1:
        off = S[~np.eye(S.shape[0], dtype=bool)]
        vlo = float(np.percentile(off, 5))
        im = ax.imshow(S, cmap="magma", vmin=vlo, vmax=1.0, origin="lower")
        fig.colorbar(im, ax=ax, fraction=0.046, pad=0.04)
    ax.set_title(
        f"voice self-sim  clusters={a['n_voice_clusters']}  "
        f"sil={a['silhouette']}  CH={a['ch_separation']} -> {a['voice_verdict']}",
        fontsize=8,
    )
    ax.set_xlabel("window")
    ax.set_ylabel("window")

    fig.suptitle(title or a.get("label", "?"), fontsize=10)
    fig.tight_layout(rect=(0, 0, 1, 0.95))
    Path(out_png).parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_png, dpi=110)
    plt.close(fig)
    return out_png


def print_row(a: Dict) -> None:
    print(
        f"  {a['label']:26s} | breath: decay={a['decay_db']:+5.1f}dB "
        f"run={a['max_voiced_run_s']:4.1f}s pauses={a['n_pauses']:2d} -> {a['breath_verdict']:7s}"
        f" | voice: clusters={a['n_voice_clusters']} sim={a['timbre_sim_mean']:.2f} "
        f"sil={a['silhouette']:.2f} CH={a['ch_separation']:.0f} -> {a['voice_verdict']}"
    )


def main() -> None:
    ap = argparse.ArgumentParser(description="Energy-envelope + spectral-signature analyzer")
    ap.add_argument("clips", nargs="+", help="audio files (mp3/wav)")
    ap.add_argument("--out-dir", default=None, help="dir for the per-clip signature PNGs")
    ap.add_argument("--json", default=None, help="write all analyses (metrics only) to JSON")
    args = ap.parse_args()

    rows: List[Dict] = []
    print("\n=== spectral / envelope analysis ===")
    for clip in args.clips:
        a = analyze_spectral(clip)
        print_row(a)
        out_dir = args.out_dir or str(Path(clip).parent)
        plot_signature(a, str(Path(out_dir) / f"sig_{a['label']}.png"))
        rows.append({k: v for k, v in a.items() if k != "_plot"})

    if args.json:
        Path(args.json).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json).write_text(
            json.dumps(rows, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        print(f"\n[json] {args.json}")


if __name__ == "__main__":
    main()
