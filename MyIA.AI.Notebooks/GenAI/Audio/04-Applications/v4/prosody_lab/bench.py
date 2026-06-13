"""Prosody bench — engine/workflow matrix on the 2 imposed extracts (#1877/#1273).

User mandate 2026-06-12: pick the best LOCAL engine/workflow to fix the monotone
Boule de Suif audiobook, validated on TWO fixed extracts BEFORE any production:
  A = opening narration  (bench_extracts/extract_A_narration.txt)
  B = character dialogue  (bench_extracts/extract_B_dialogue.txt)

STRICT GATE (user, verbatim): do NOT generate the 385 segments until the engine
is validated on these 2 extracts. This script renders ONLY the 2 extracts — it
never touches segments_v4.json. It is a *measurement* tool, not a producer.

Every cell is measured two ways, no ear-judging:
  - GLOBAL contour   : prosody_metrics.compute_metrics  (ST range, F0 CV, velocity)
  - SYLLABLE partition: syllable_pitch.analyze_syllables (melodic motion / syllable,
    % flat transitions) — the "pitch des syllabes comme une partition de musique"
    instrument the user asked for, the robust monotony discriminator.

Workflow matrix (the "differents modeles/workflows a evaluer"):
  W1 fish_flat      FishAudio clone <- flat ref v4_narrator_male_neutral, temp 0.7
                    = the CURRENT v4 pipeline = the monotony we are fixing (baseline)
  W2 fish_flat_hot  same flat ref, temp 1.0 = the temperature lever (capped MODERATE)
  W3 qwen_vd_prompt Qwen3-TTS VoiceDesign with a natural-language PROSODY PROMPT
                    (directive #2 — the lever never exploited; SLOW on WSL)
  W4 higgs_native   Higgs Audio v3 native (sglang-omni, 8199)
  W5 openai_instr   OpenAI gpt-4o-mini-tts + instructions (cloud expressivity ceiling)
  W6 kokoro_native  Kokoro native (8191) = fast local floor

The "keep the FishAudio identity + recover control" path (directive #3) is Round 2:
  W7 fish_expr_male FishAudio clone <- a SAME-IDENTITY *expressive male* reference.
                    Requires sourcing that reference first (the prior female Qwen ref
                    was invalid). Opt-in via --expr-ref-id once Round 1 picks a winner.

Usage:
    python bench.py --list
    python bench.py --extracts B --cells fast      # quick end-to-end proof
    python bench.py --extracts A B --cells all      # full matrix (Qwen is slow)
    python bench.py --cells W4 W5 W6                 # specific cells
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, Callable

# --- path wiring: clients live in prosody_lab/, fishaudio_client lives in v4/ ---
_LAB_DIR = Path(__file__).resolve().parent
_V4_DIR = _LAB_DIR.parent
for _p in (_LAB_DIR, _V4_DIR):
    if str(_p) not in sys.path:
        sys.path.insert(0, str(_p))

import prosody_metrics as pm  # noqa: E402
import syllable_pitch as sp  # noqa: E402
from qwen_tts_client import qwen_tts_voicedesign_chunked  # noqa: E402
from openai_tts_client import openai_tts  # noqa: E402

try:
    from fishaudio_client import fishaudio_tts  # noqa: E402
    _HAS_FISH = True
except Exception as exc:  # pragma: no cover
    print(f"[warn] fishaudio_client unavailable: {exc}")
    _HAS_FISH = False

# Proven Higgs/Kokoro callers (reused, not re-implemented).
from ab_engine_test import call_higgs, call_kokoro  # noqa: E402

# --- fixed inputs (the GATE: only these two files are ever rendered) ----------
EXTRACT_DIR = _LAB_DIR / "bench_extracts"
EXTRACTS: dict[str, Path] = {
    "A": EXTRACT_DIR / "extract_A_narration.txt",
    "B": EXTRACT_DIR / "extract_B_dialogue.txt",
}

OUT_DIR = _V4_DIR / "outputs" / "prosody_lab" / "bench"
OUT_DIR.mkdir(parents=True, exist_ok=True)

# --- references ---------------------------------------------------------------
# The flat reference the v4 pipeline actually clones from = root cause of monotony.
FLAT_REF_ID = "v4_narrator_male_neutral"

# --- prosody prompts ----------------------------------------------------------
# MALE warm audiobook narrator (identity-consistent with the male v4 narrator).
# The prior bench used a *female* VoiceDesign voice, which invalidated the A/B by
# changing timbre, not just prosody. This keeps a male identity throughout.
QWEN_NARRATOR_MALE = (
    "Un narrateur francais de livre audio, voix masculine grave, chaleureuse et "
    "profondement expressive. Il module fortement son intonation : posee et sombre "
    "dans la description, puis tendue et vibrante dans les dialogues. Rythme vivant, "
    "pauses dramatiques, contrastes de hauteur marques, jamais monotone."
)
OPENAI_NARRATOR_MALE = (
    "Read as a French audiobook narrator with a deep warm male voice. Vary the "
    "intonation strongly: somber and measured in narration, tense and vivid in the "
    "dialogue. Lively rhythm, dramatic pauses, marked pitch contrasts, never monotone."
)


# ---------------------------------------------------------------------------
# Workflow cells
# ---------------------------------------------------------------------------
def _fish(text: str, ref: str, temp: float) -> bytes | None:
    if not _HAS_FISH:
        print("  [skip] fishaudio_client unavailable")
        return None
    return fishaudio_tts(text, reference_id=ref, temperature=temp, seed=42,
                         format="mp3", timeout=600)


# Each cell: id -> (engine, ext, speed, desc, render(text)->bytes|None)
Cell = dict[str, Any]
WORKFLOWS: list[Cell] = [
    {"id": "W1_fish_flat", "ext": "mp3", "speed": "med",
     "desc": "FishAudio clone <- flat ref (CURRENT pipeline baseline, temp 0.7)",
     "render": lambda t: _fish(t, FLAT_REF_ID, 0.7)},
    {"id": "W2_fish_flat_hot", "ext": "mp3", "speed": "med",
     "desc": "FishAudio clone <- flat ref, temp 1.0 (temperature lever)",
     "render": lambda t: _fish(t, FLAT_REF_ID, 1.0)},
    {"id": "W3_qwen_vd_prompt", "ext": "wav", "speed": "slow",
     "desc": "Qwen3-TTS VoiceDesign + prosody PROMPT (directive #2; slow WSL)",
     "render": lambda t: qwen_tts_voicedesign_chunked(
         t, instructions=QWEN_NARRATOR_MALE, max_chars=160)},
    {"id": "W4_higgs_native", "ext": "mp3", "speed": "fast",
     "desc": "Higgs Audio v3 native (sglang-omni, 8199)",
     "render": call_higgs},
    {"id": "W5_openai_instr", "ext": "mp3", "speed": "fast",
     "desc": "OpenAI gpt-4o-mini-tts + instructions (cloud ceiling)",
     "render": lambda t: openai_tts(t, voice="onyx", model="gpt-4o-mini-tts",
                                    instructions=OPENAI_NARRATOR_MALE,
                                    response_format="mp3")},
    {"id": "W6_kokoro_native", "ext": "mp3", "speed": "fast",
     "desc": "Kokoro native (8191) = fast local floor",
     "render": call_kokoro},
]

# Round-2 cell (keep-FishAudio-identity path) is wired dynamically from --expr-ref-id.

SPEED_GROUPS = {
    "fast": {"W4_higgs_native", "W5_openai_instr", "W6_kokoro_native"},
    "med": {"W1_fish_flat", "W2_fish_flat_hot"},
    "slow": {"W3_qwen_vd_prompt"},
}


def _resolve_cells(tokens: list[str], expr_ref_id: str | None) -> list[Cell]:
    cells_by_id = {c["id"]: c for c in WORKFLOWS}
    if expr_ref_id:
        cell = {
            "id": "W7_fish_expr_male", "ext": "mp3", "speed": "med",
            "desc": f"FishAudio clone <- expressive male ref '{expr_ref_id}' (keep-voice path)",
            "render": lambda t, _r=expr_ref_id: _fish(t, _r, 0.8),
        }
        cells_by_id[cell["id"]] = cell
    if not tokens or tokens == ["all"]:
        return list(cells_by_id.values())
    selected: list[Cell] = []
    seen: set[str] = set()
    for tok in tokens:
        if tok in SPEED_GROUPS:
            for cid in cells_by_id:
                if cid in SPEED_GROUPS[tok] and cid not in seen:
                    selected.append(cells_by_id[cid]); seen.add(cid)
        elif tok in cells_by_id and tok not in seen:
            selected.append(cells_by_id[tok]); seen.add(tok)
        else:
            print(f"[warn] unknown cell token: {tok}")
    return selected


# ---------------------------------------------------------------------------
# Measurement
# ---------------------------------------------------------------------------
def _measure(path: str, label: str) -> dict[str, Any]:
    """Global contour + syllable partition for one clip, merged into a flat row."""
    g = pm.compute_metrics(path)
    s = sp.analyze_syllables(path)
    return {
        "label": label,
        "path": path,
        "duration_s": g.get("duration_s"),
        # global contour
        "g_st_range": round(g.get("f0_semitone_range", 0.0), 2),
        "g_cv": round(g.get("f0_cv", 0.0), 3),
        "g_velocity": round(g.get("intonation_velocity_st_s", 0.0), 2),
        "g_verdict": g.get("verdict"),
        # syllable partition
        "n_syll": s.get("n_syllables"),
        "syll_rate": (round(s.get("syllable_rate_hz", 0.0), 2)
                      if s.get("syllable_rate_hz") is not None else None),
        "s_motion": (round(s.get("mean_abs_interval_st", 0.0), 2)
                     if s.get("mean_abs_interval_st") is not None else None),
        "s_flat_pct": (round(s.get("pct_flat_transitions", 0.0), 1)
                       if s.get("pct_flat_transitions") is not None else None),
        "s_span": (round(s.get("melodic_span_st", 0.0), 2)
                   if s.get("melodic_span_st") is not None else None),
        "s_verdict": s.get("verdict"),
        "_syll_analysis": s,  # kept for the partition plot; stripped from JSON
    }


def _render_table(rows: list[dict[str, Any]]) -> str:
    hdr = ("| extract | workflow | dur | n_syll | ST | CV | vel | "
           "motion | flat% | global | syllable |")
    sep = "|---|---|--:|--:|--:|--:|--:|--:|--:|---|---|"
    lines = [hdr, sep]
    for r in rows:
        lines.append(
            f"| {r['extract']} | {r['cell']} | {r['duration_s']} | {r['n_syll']} | "
            f"{r['g_st_range']} | {r['g_cv']} | {r['g_velocity']} | "
            f"{r['s_motion']} | {r['s_flat_pct']} | {r['g_verdict']} | {r['s_verdict']} |"
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------
def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description="Prosody engine/workflow bench on 2 fixed extracts (#1877/#1273).")
    ap.add_argument("--extracts", nargs="+", default=["A", "B"], choices=["A", "B"],
                    help="Which extract(s) to render (default both).")
    ap.add_argument("--cells", nargs="+", default=["all"],
                    help="Cell ids (W1_fish_flat ...), speed groups (fast/med/slow), or 'all'.")
    ap.add_argument("--expr-ref-id", default=None,
                    help="Round 2: FishAudio reference_id of a same-identity expressive male voice "
                         "(adds the W7 keep-voice cell).")
    ap.add_argument("--http-dir", default=None,
                    help="Optional dir to also copy clips into (e.g. an HTTP-served folder).")
    ap.add_argument("--list", action="store_true", help="List cells and exit.")
    args = ap.parse_args(argv)

    cells = _resolve_cells(args.cells, args.expr_ref_id)
    if args.list:
        print("Cells:")
        for c in cells:
            print(f"  {c['id']:<20} [{c['speed']:>4}] {c['desc']}")
        print("\nExtracts:")
        for k, p in EXTRACTS.items():
            txt = p.read_text(encoding="utf-8").strip()
            print(f"  {k}: {len(txt)} chars — {p.name}")
        return

    rows: list[dict[str, Any]] = []
    syll_by_extract: dict[str, list[dict[str, Any]]] = {k: [] for k in args.extracts}
    t_start = time.time()

    for ext_key in args.extracts:
        text = EXTRACTS[ext_key].read_text(encoding="utf-8").strip()
        print(f"\n========== Extract {ext_key} ({len(text)} chars) ==========")
        for c in cells:
            label = f"{ext_key}__{c['id']}"
            print(f"\n[{label}] {c['desc']}")
            t0 = time.time()
            try:
                audio = c["render"](text)
            except Exception as exc:
                print(f"  [ERROR] render raised: {exc}")
                audio = None
            dt = time.time() - t0
            if not audio:
                print(f"  [FAIL] no audio ({dt:.1f}s)")
                rows.append({"extract": ext_key, "cell": c["id"], "duration_s": None,
                             "n_syll": None, "g_st_range": None, "g_cv": None,
                             "g_velocity": None, "s_motion": None, "s_flat_pct": None,
                             "g_verdict": "NO_AUDIO", "s_verdict": "NO_AUDIO",
                             "render_s": round(dt, 1)})
                continue
            clip = OUT_DIR / f"{label}.{c['ext']}"
            clip.write_bytes(audio)
            print(f"  [ok] {len(audio)/1024:.0f} KB in {dt:.1f}s -> {clip.name}")
            m = _measure(str(clip), label)
            syll_by_extract[ext_key].append(m.pop("_syll_analysis"))
            row = {"extract": ext_key, "cell": c["id"], "render_s": round(dt, 1), **m}
            row.pop("_syll_analysis", None)
            rows.append(row)
            print(f"     global: ST={m['g_st_range']} CV={m['g_cv']} vel={m['g_velocity']} -> {m['g_verdict']}")
            print(f"     syllab: motion={m['s_motion']} flat%={m['s_flat_pct']} ({m['n_syll']} syll) -> {m['s_verdict']}")

            if args.http_dir:
                hdir = Path(args.http_dir)
                hdir.mkdir(parents=True, exist_ok=True)
                (hdir / clip.name).write_bytes(audio)

    # --- outputs --------------------------------------------------------------
    table = _render_table(rows)
    print("\n\n" + "=" * 70)
    print(f"BENCH RESULTS ({len(rows)} renders, {time.time() - t_start:.0f}s)")
    print("=" * 70)
    print(table)

    json_out = OUT_DIR / "bench_results.json"
    json_out.write_text(json.dumps({"rows": rows}, indent=2, ensure_ascii=False), encoding="utf-8")
    md_out = OUT_DIR / "bench_results.md"
    md_out.write_text("# Prosody bench results\n\n" + table + "\n", encoding="utf-8")
    print(f"\nJSON : {json_out}")
    print(f"MD   : {md_out}")

    # Syllable partition PNG per extract (overlay all cells).
    for ext_key, analyses in syll_by_extract.items():
        analyses = [a for a in analyses if a and a.get("n_syllables", 0) >= 2]
        if not analyses:
            continue
        png = OUT_DIR / f"partition_extract_{ext_key}.png"
        try:
            sp.plot_score(analyses, str(png), title=f"Extract {ext_key} — syllable partition")
            print(f"PNG  : {png}")
        except Exception as exc:
            print(f"[warn] partition plot failed for {ext_key}: {exc}")


if __name__ == "__main__":
    main()
