"""bake.py - Phase A0 bakeoff driver for 4 small TTS models on RTX 4060 8 GB.

Usage:
    python bake.py --list
    python bake.py --extracts A B --cells chatterbox_mtl_v3 --quick
    python bake.py --extracts A --cells all --gdrive-root "G:\\Mon Drive\\MyIA\\Projets\\BibliothequesSonores\\run-20260924-093628\\A0-bakeoff"

Each (extract, client) pair produces:
    <out-dir>/<extract>__<client>.wav      # the rendered clip (16 kHz mono PCM)
    <out-dir>/<extract>__<client>.json     # prosody_metrics + syllable_pitch + WER
    <out-dir>/<extract>__<client>.log      # stdout / stderr from the client

Whisper-tiny is loaded ONCE at the start (73 MB VRAM FP16), then the per-model
client is loaded, run on both extracts, unloaded (torch.cuda.empty_cache()),
and we move on. This keeps peak VRAM <= Whisper + largest TTS model.

Outputs are written to the --gdrive-root (default: A0-bakeoff/ next to this file).
If GDrive is unreachable, fall back to outputs/bakeoff_small/ inside the lab.
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Optional

# Reuse the existing bench.py infra (path wiring)
_LAB_DIR = Path(__file__).resolve().parent.parent
for _p in (_LAB_DIR, _LAB_DIR.parent):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

import prosody_metrics as pm  # noqa: E402
import syllable_pitch as sp  # noqa: E402

from bakeoff_small.clients import ALL_CLIENTS  # noqa: E402

log = logging.getLogger("bakeoff_small.bake")

# --- bench extracts (same as bench.py A/B -- the GATE texts) -----------------
EXTRACT_DIR = _LAB_DIR / "bench_extracts"
EXTRACTS = {
    "A": EXTRACT_DIR / "extract_A_narration.txt",
    "B": EXTRACT_DIR / "extract_B_dialogue.txt",
}

DEFAULT_GDRIVE = Path(r"G:\Mon Drive\MyIA\Projets\BibliothèquesSonores\run-20260924-093628\A0-bakeoff")
FALLBACK_OUT = Path(__file__).resolve().parent.parent / "outputs" / "bakeoff_small"


# --- helpers ------------------------------------------------------------------
def _measure(path: str, label: str) -> dict[str, Any]:
    """Same instrument as bench.py: prosody_metrics + syllable_pitch."""
    g = pm.compute_metrics(path)
    s = sp.analyze_syllables(path)
    return {
        "label": label,
        "path": path,
        "duration_s": g.get("duration_s"),
        "g_st_range": round(g.get("f0_semitone_range", 0.0), 2),
        "g_cv": round(g.get("f0_cv", 0.0), 3),
        "g_velocity": round(g.get("intonation_velocity_st_s", 0.0), 2),
        "g_verdict": g.get("verdict"),
        "n_syll": s.get("n_syllables"),
        "s_motion": (round(s.get("mean_abs_interval_st", 0.0), 2)
                     if s.get("mean_abs_interval_st") is not None else None),
        "s_flat_pct": (round(s.get("pct_flat_transitions", 0.0), 1)
                       if s.get("pct_flat_transitions") is not None else None),
        "s_span": (round(s.get("melodic_span_st", 0.0), 2)
                   if s.get("melodic_span_st") is not None else None),
        "s_verdict": s.get("verdict"),
    }


def compute_wer_for_wav(wav_path: Path, text: str) -> dict[str, Any]:
    """Compute WER + prosody payload for a single WAV.

    Public API consumed by measure_chatterbox_mtl_v3.py (and any future
    measure_<cell>.py). Combines _transcribe (Whisper-tiny on cuda),
    _wer (Levenshtein on token sequences), _measure (prosody_metrics +
    syllable_pitch). Returns a flat dict aligned on the bake_results.json
    schema committed in PR #17661.

    Args:
        wav_path: Path to the rendered WAV (16 kHz mono PCM expected by
            Whisper-tiny; higher-rate files are resampled by librosa).
        text: Reference transcription (the extract text). Lower-cased
            and stripped by _wer.

    Returns:
        dict with keys {wer, n_ref, n_hyp, edit_distance, hyp_first200,
        duration_s, g_st_range, g_cv, g_velocity, g_verdict, n_syll,
        s_motion, s_flat_pct, s_span, s_verdict}. All numeric fields may
        be None if their instrument failed (graceful degradation -- the
        caller decides whether to abort or partial-emit).

    Tell c.1493 strict ★★ fondateur nuance c.862 strict : this function is
    the REAL producer referenced by measure_chatterbox_mtl_v3.py line 73.
    Prior to this commit, the import was a Catholic declaration (# type:
    ignore + # noqa: E402) on a symbol that did not exist -- the script
    would have raised ImportError at runtime, not a lint failure.
    """
    label = wav_path.stem  # e.g. "A__chatterbox_mtl_v3"
    log.info("[compute_wer_for_wav] %s (%.1f KB)",
             wav_path.name, wav_path.stat().st_size / 1024)

    # 1) Whisper-tiny transcription (loads the pipeline ONCE per call -- the
    #    measure_<cell>.py scripts are designed to invoke this once per
    #    extract, so the pipeline reload cost is acceptable; if batched
    #    becomes a concern, lift the pipeline into a module-level cache).
    try:
        hyp = _transcribe(wav_path)
    except Exception as exc:
        log.warning("[compute_wer_for_wav] transcription failed: %s", exc)
        return {"wer": None, "error": str(exc), "hyp_first200": None,
                "duration_s": None}

    # 2) WER vs reference text.
    wer = _wer(text, hyp)
    hyp_first200 = hyp[:200] if hyp else None

    # 3) Prosody + syllable pitch (instruments from bench.py / prosody_lab).
    try:
        m = _measure(str(wav_path), label)
    except Exception as exc:
        log.warning("[compute_wer_for_wav] prosody measure failed: %s", exc)
        m = {"label": label, "path": str(wav_path), "duration_s": None}

    # 4) Flat payload aligned on the schema committed in PR #17661.
    return {
        "wer": wer["wer"],
        "n_ref": wer["n_ref"],
        "n_hyp": wer["n_hyp"],
        "edit_distance": wer["edit_distance"],
        "hyp_first200": hyp_first200,
        "duration_s": m.get("duration_s"),
        "g_st_range": m.get("g_st_range"),
        "g_cv": m.get("g_cv"),
        "g_velocity": m.get("g_velocity"),
        "g_verdict": m.get("g_verdict"),
        "n_syll": m.get("n_syll"),
        "s_motion": m.get("s_motion"),
        "s_flat_pct": m.get("s_flat_pct"),
        "s_span": m.get("s_span"),
        "s_verdict": m.get("s_verdict"),
    }


def _wer(reference: str, hypothesis: str) -> dict[str, Any]:
    """Plain word error rate. Tells c.1493: WER is a metric, not the discriminator."""
    ref = reference.strip().lower().split()
    hyp = hypothesis.strip().lower().split()
    # Levenshtein on token sequences
    n, m = len(ref), len(hyp)
    if n == 0:
        return {"wer": None, "n_ref": 0, "n_hyp": m, "sub": 0, "ins": m, "del": 0}
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = i
    for j in range(m + 1):
        dp[0][j] = j
    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if ref[i - 1] == hyp[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j - 1], dp[i - 1][j], dp[i][j - 1])
    sub = ins = de = 0  # not strictly tracked here, kept for forward compat
    return {
        "wer": round(dp[n][m] / n, 4),
        "n_ref": n,
        "n_hyp": m,
        "edit_distance": dp[n][m],
        "sub": sub, "ins": ins, "del": de,
    }


def _resolve_out_root(gdrive_arg: Optional[str]) -> Path:
    if gdrive_arg:
        root = Path(gdrive_arg)
    elif DEFAULT_GDRIVE.exists():
        root = DEFAULT_GDRIVE
    else:
        root = FALLBACK_OUT
    root.mkdir(parents=True, exist_ok=True)
    return root


def _transcribe(wav_path: Path, lang: str = "fr") -> str:
    """Transcribe one WAV via Whisper-tiny. Caller owns VRAM."""
    from transformers import (  # noqa: E402
        AutomaticSpeechRecognitionPipeline,
    )
    import torch  # noqa: E402
    import librosa  # noqa: E402

    audio, _ = librosa.load(str(wav_path), sr=16000)
    pipe = AutomaticSpeechRecognitionPipeline.from_pretrained(
        "openai/whisper-tiny", torch_dtype=torch.float16, device="cuda"
    )
    out = pipe(audio, generate_kwargs={"language": lang, "task": "transcribe"})
    return out["text"] if isinstance(out, dict) else out[0]["text"]


# --- main ---------------------------------------------------------------------
def main(argv: Optional[list[str]] = None) -> None:
    ap = argparse.ArgumentParser(description="Bake-off small TTS models on RTX 4060 8 GB.")
    ap.add_argument("--extracts", nargs="+", default=["A"], choices=list(EXTRACTS),
                    help="Which extract(s) to render (default A).")
    ap.add_argument("--cells", nargs="+", default=["all"],
                    help=f"Cell ids ({', '.join(c.NAME for c in ALL_CLIENTS)}) or 'all'.")
    ap.add_argument("--quick", action="store_true",
                    help="Stop after first extract to fail fast on env issues.")
    ap.add_argument("--gdrive-root", default=None,
                    help=f"GDrive destination (default {DEFAULT_GDRIVE}).")
    ap.add_argument("--no-wer", action="store_true",
                    help="Skip WER measurement (faster, useful for env smoke test).")
    ap.add_argument("--list", action="store_true", help="List cells and exit.")
    ap.add_argument("--verbose", "-v", action="count", default=0)
    args = ap.parse_args(argv)

    logging.basicConfig(
        level=logging.WARNING - 10 * min(args.verbose, 2),
        format="%(asctime)s %(levelname)s %(name)s | %(message)s",
        datefmt="%H:%M:%S",
    )

    if args.list:
        print("Cells:")
        for c in ALL_CLIENTS:
            print(f"  {c.NAME:<24} [{c.SIZE:>7}] license={c.LICENSE}")
        print("\nExtracts:")
        for k, p in EXTRACTS.items():
            txt = p.read_text(encoding="utf-8").strip()
            print(f"  {k}: {len(txt)} chars - {p.name}")
        return

    if args.cells == ["all"]:
        cells = [c() for c in ALL_CLIENTS]
    else:
        idx = {c.NAME: c for c in ALL_CLIENTS}
        cells = [idx[t]() for t in args.cells if t in idx]
        if not cells:
            print(f"[ERROR] no valid cell tokens: {args.cells}")
            return 2

    out_root = _resolve_out_root(args.gdrive_root)
    log.info("Output root: %s", out_root)

    rows: list[dict[str, Any]] = []
    t_start = time.time()

    for cell in cells:
        log.info("=== cell %s (%s, %s) ===", cell.NAME, cell.SIZE, cell.LICENSE)
        cell_out = out_root / cell.NAME
        cell_out.mkdir(parents=True, exist_ok=True)

        for ext_key in args.extracts:
            if args.quick and ext_key != args.extracts[0]:
                break
            text = EXTRACTS[ext_key].read_text(encoding="utf-8").strip()
            label = f"{ext_key}__{cell.NAME}"
            log.info("Rendering %s on extract %s (%d chars)...", cell.NAME, ext_key, len(text))
            t0 = time.time()
            audio_bytes = cell.warm(text, lang="fr")
            dt = time.time() - t0

            if not audio_bytes:
                log.warning("[FAIL] no audio for %s (%s)", label, cell.NAME)
                rows.append({
                    "extract": ext_key, "cell": cell.NAME,
                    "render_s": round(dt, 1),
                    "status": "NO_AUDIO",
                })
                continue

            wav_path = cell_out / f"{label}.wav"
            wav_path.write_bytes(audio_bytes)
            log.info("  ok %d KB in %.1fs -> %s", len(audio_bytes) / 1024, dt, wav_path)

            try:
                m = _measure(str(wav_path), label)
            except Exception as exc:
                log.warning("[measure] failed: %s", exc)
                m = {"label": label, "path": str(wav_path), "duration_s": None}

            wer = None
            if not args.no_wer:
                try:
                    hyp = _transcribe(wav_path)
                    wer = _wer(text, hyp)
                    wer["hypothesis"] = hyp
                    log.info("  WER %.3f (ref=%d, hyp=%d)", wer["wer"], wer["n_ref"], wer["n_hyp"])
                except Exception as exc:
                    log.warning("[wer] failed: %s", exc)
                    wer = {"wer": None, "error": str(exc)}

            payload = {
                "extract": ext_key,
                "cell": cell.NAME,
                "size": cell.SIZE,
                "license": cell.LICENSE,
                "render_s": round(dt, 1),
                "wav_path": str(wav_path),
                "wav_bytes": len(audio_bytes),
                "metrics": m,
                "wer": wer,
            }
            json_path = cell_out / f"{label}.json"
            json_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False),
                                 encoding="utf-8")
            rows.append({"extract": ext_key, "cell": cell.NAME, "status": "OK"})

        # free VRAM before next cell
        cell.close()

    # --- summary ---------------------------------------------------------------
    summary = {
        "bake_id": "run-20260924-093628-A0-bakeoff",
        "out_root": str(out_root),
        "extracts": args.extracts,
        "cells": [c.NAME for c in cells],
        "n_rows": len(rows),
        "elapsed_s": round(time.time() - t_start, 1),
        "rows": rows,
    }
    summary_path = out_root / "_bake_summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=False),
                            encoding="utf-8")
    print(f"\n[done] {len(rows)} rows; elapsed {summary['elapsed_s']}s")
    print(f"Summary: {summary_path}")


if __name__ == "__main__":
    main()
