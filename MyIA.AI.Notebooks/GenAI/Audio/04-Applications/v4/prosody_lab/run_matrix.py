"""Staged prosody experiment runner for #1273.

Answers the three questions the user asked about local TTS:
  (a) Can we *control prosody* of a voice?       -> Stage 3 (DTW on opposed instructions)
  (b) Can we *control consistency* (cloning)?    -> Stage 2 (cloning impact on F0 range)
  (c) A mechanism for the *melody* vs OpenAI?    -> Stage 0 benchmark + prosody_metrics

Each cell synthesizes audio, writes it under ``v4/outputs/prosody_lab/``, then
``prosody_metrics`` measures the F0 melody. Nothing is judged by ear: every
verdict is the measured semitone range against the OpenAI benchmark.

Stages (select with --stages, default all):
  0  OpenAI tts-1-hd benchmark            -> target numbers
  1  native non-cloned expressive         -> Qwen VoiceDesign / CustomVoice, FishAudio, Kokoro
  2  cloning impact                        -> Qwen Base clone vs native VoiceDesign
  3  controllability                       -> same text, 3 opposed prosody instructions + DTW

Usage:
    conda run -n mcp-jupyter-py310 python run_matrix.py --stages 0 1 3
    conda run -n mcp-jupyter-py310 python run_matrix.py            # all stages
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

# --- path wiring: clients live here, fishaudio_client lives in v4/ -----------
_LAB_DIR = Path(__file__).resolve().parent
_V4_DIR = _LAB_DIR.parent
for p in (_LAB_DIR, _V4_DIR):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

import prosody_metrics as pm  # noqa: E402
from qwen_tts_client import qwen_tts_voicedesign_chunked  # noqa: E402
from openai_tts_client import openai_tts  # noqa: E402

try:
    from fishaudio_client import fishaudio_tts  # noqa: E402
    _HAS_FISH = True
except Exception as exc:  # pragma: no cover
    print(f"[warn] fishaudio_client unavailable: {exc}")
    _HAS_FISH = False

OUT_DIR = _V4_DIR / "outputs" / "prosody_lab"
OUT_DIR.mkdir(parents=True, exist_ok=True)

TEST_TEXT = (_LAB_DIR / "test_segment.txt").read_text(encoding="utf-8").strip()

# Stage 3 controllability uses ONE short, emotionally-chargeable sentence rather
# than the full passage: the DTW contrast between opposed deliveries is sharper
# on a single line, and a short render stays well within the slow WSL Qwen
# engine's working length (no chunking needed, fast + reliable).
CONTROL_TEXT = "Mais quand je les ai vus, ces Prussiens, ce fut plus fort que moi !"

# ---------------------------------------------------------------------------
# Prosody prompts (the "prosody signal" under test)
# ---------------------------------------------------------------------------

# Stage 1: a single rich expressive narration prompt for VoiceDesign.
VOICEDESIGN_EXPRESSIVE = (
    "Une narratrice francaise de livre audio, voix chaleureuse et profondement "
    "expressive. Elle module fortement son intonation : douce et posee dans la "
    "description, puis vibrante de colere et d'indignation dans le discours direct. "
    "Rythme vivant, pauses dramatiques, contrastes de hauteur marques."
)

# Stage 3: three deliberately opposed deliveries of the SAME text. If the F0
# contours barely differ (low DTW), the engine ignores the instruction.
CONTROL_INSTRUCTIONS = {
    "calm": (
        "Une voix feminine tres calme, posee et neutre, presque monotone, qui lit "
        "lentement sans emotion, sur un ton egal et apaise."
    ),
    "tense": (
        "Une voix feminine tendue et anxieuse, au bord de la rupture, debit nerveux "
        "et saccade, intonation crispee et instable, souffle court."
    ),
    "exalted": (
        "Une voix feminine exaltee et passionnee, qui s'emporte, monte dans les aigus, "
        "accentue chaque mot avec vehemence et indignation theatrale."
    ),
}

# Cloud controllability analogue (gpt-4o-mini-tts honours instructions).
OPENAI_CONTROL_INSTRUCTIONS = {
    "calm": "Read very calmly and flatly, neutral and slow, almost monotone.",
    "tense": "Read tense and anxious, on edge, nervous clipped rhythm.",
    "exalted": "Read exalted and passionate, voice rising, every word emphasised with theatrical indignation.",
}


def _save(audio: bytes | None, name: str, ext: str) -> str | None:
    if not audio:
        print(f"  [FAIL] {name}: no audio returned")
        return None
    path = OUT_DIR / f"{name}.{ext}"
    path.write_bytes(audio)
    print(f"  [ok]   {name}: {len(audio)} bytes -> {path.name}")
    return str(path)


# ---------------------------------------------------------------------------
# Stages
# ---------------------------------------------------------------------------


def stage0_openai() -> dict[str, str]:
    """OpenAI tts-1-hd benchmark — defines the target semitone range."""
    print("\n[Stage 0] OpenAI tts-1-hd benchmark")
    cells: dict[str, str] = {}
    for voice in ("nova", "shimmer"):
        audio = openai_tts(TEST_TEXT, voice=voice, model="tts-1-hd", response_format="mp3")
        p = _save(audio, f"s0_openai_tts1hd_{voice}", "mp3")
        if p:
            cells[f"openai-{voice}"] = p
    return cells


def stage1_native() -> dict[str, str]:
    """Native non-cloned expressive renders (the user's hypothesis)."""
    print("\n[Stage 1] native non-cloned expressive")
    cells: dict[str, str] = {}

    # Qwen VoiceDesign with the rich expressive prompt.
    # NOTE: the loaded checkpoint is VoiceDesign-only. CustomVoice (named native
    # speakers, e.g. "Vivian") is NOT served by this checkpoint and raises
    # "Unsupported speaker: <name>" which kills the vLLM EngineCore. Exercising
    # CustomVoice would require swapping the container to the CustomVoice model
    # (MODEL=CustomVoice) — out of scope for this diagnostic round.
    # Chunked: long-text VoiceDesign exceeds the gateway's 300s timeout on WSL,
    # so render per-sentence and concatenate (production-realistic, robust).
    audio = qwen_tts_voicedesign_chunked(TEST_TEXT, instructions=VOICEDESIGN_EXPRESSIVE)
    p = _save(audio, "s1_qwen_voicedesign_expressive", "wav")
    if p:
        cells["qwen-VD-expressive"] = p

    # FishAudio S2-Pro native (no reference_id) — its default voice.
    if _HAS_FISH:
        audio = fishaudio_tts(TEST_TEXT, reference_id="", temperature=0.8, format="mp3")
        p = _save(audio, "s1_fishaudio_native", "mp3")
        if p:
            cells["fish-native"] = p

    # Kokoro floor through the gateway's OpenAI-compatible /v1/audio/speech
    # (speed only, no pitch/tags — establishes the monotone baseline).
    try:
        import requests
        r = requests.post(
            "http://localhost:8196/v1/audio/speech",
            json={"model": "kokoro", "input": TEST_TEXT, "voice": "af_heart", "response_format": "mp3"},
            timeout=120,
        )
        if r.ok and "audio" in r.headers.get("content-type", ""):
            p = _save(r.content, "s1_kokoro_floor", "mp3")
            if p:
                cells["kokoro-floor"] = p
        else:
            print(f"  [FAIL] kokoro: status={r.status_code} ctype={r.headers.get('content-type')}")
    except Exception as exc:
        print(f"  [FAIL] kokoro: {exc}")

    return cells


# Stage 2 reference clips (production cloning engine = FishAudio S2-Pro).
# The flat narrator reference is the one the v4 pipeline actually clones from
# (a generic ~250-char preset render) — the suspected root cause of monotony.
FLAT_REF_ID = "v4_narrator_male_neutral"
FLAT_REF_TEXT = (
    "Les voyageurs se regardaient avec une certaine honte. La lueur vacillante de "
    "la bougie eclairait des visages decomposes, et l'on entendait au-dehors le pas "
    "lourd des soldats prussiens qui montaient la garde dans la nuit froide de decembre."
)
# Expressive reference = the Stage 1 Qwen VoiceDesign render (rich F0 range),
# uploaded into FishAudio to test whether a varied source recovers expressivity.
EXPR_REF_ID = "prosody_expr_voicedesign"


def stage2_cloning(*_ignored) -> dict[str, str]:
    """Cloning impact on FishAudio S2-Pro (the production clone engine).

    Compares three deliveries of the same test text:
      - native  : no reference_id (engine's own voice = its expressivity ceiling)
      - clone-flat : cloned from the flat ~250-char production reference
      - clone-expr : cloned from the expressive Stage 1 VoiceDesign render

    Quantifies how much F0 range the clone loses vs the native voice, and
    whether a richer reference source recovers it.
    """
    print("\n[Stage 2] cloning impact (FishAudio S2-Pro)")
    cells: dict[str, str] = {}
    if not _HAS_FISH:
        print("  [skip] fishaudio_client unavailable")
        return cells

    from fishaudio_client import upload_reference, list_references

    # native (no ref)
    audio = fishaudio_tts(TEST_TEXT, reference_id="", temperature=0.8, format="mp3")
    p = _save(audio, "s2_fish_native", "mp3")
    if p:
        cells["fish-native"] = p

    # clone from the flat production reference (already on the server)
    audio = fishaudio_tts(TEST_TEXT, reference_id=FLAT_REF_ID, temperature=0.8, format="mp3")
    p = _save(audio, "s2_fish_clone_flat", "mp3")
    if p:
        cells["fish-clone-flat"] = p

    # clone from the expressive VoiceDesign render (upload it first if present)
    expr_src = OUT_DIR / "s1_qwen_voicedesign_expressive.wav"
    if expr_src.exists():
        ok = upload_reference(EXPR_REF_ID, str(expr_src), VOICEDESIGN_EXPRESSIVE[:200])
        refs = list_references().get("reference_ids", [])
        if ok or EXPR_REF_ID in refs:
            audio = fishaudio_tts(TEST_TEXT, reference_id=EXPR_REF_ID, temperature=0.8, format="mp3")
            p = _save(audio, "s2_fish_clone_expr", "mp3")
            if p:
                cells["fish-clone-expr"] = p
        else:
            print(f"  [skip] could not register expressive reference '{EXPR_REF_ID}'")
    else:
        print(f"  [skip] expressive source {expr_src.name} absent (run Stage 1 first)")

    return cells


def stage3_controllability() -> dict[str, str]:
    """Same text, opposed prosody instructions -> DTW measures controllability."""
    print("\n[Stage 3] controllability (opposed instructions)")
    cells: dict[str, str] = {}

    # Qwen VoiceDesign: the local controllability test. CONTROL_TEXT is short
    # enough to render as a single call (no chunking, well under the timeout).
    for key, instr in CONTROL_INSTRUCTIONS.items():
        audio = qwen_tts_voicedesign_chunked(CONTROL_TEXT, instructions=instr)
        p = _save(audio, f"s3_qwen_{key}", "wav")
        if p:
            cells[f"qwen-{key}"] = p

    # OpenAI gpt-4o-mini-tts: the cloud controllability reference (same text).
    for key, instr in OPENAI_CONTROL_INSTRUCTIONS.items():
        audio = openai_tts(
            CONTROL_TEXT, voice="nova", model="gpt-4o-mini-tts",
            instructions=instr, response_format="mp3",
        )
        p = _save(audio, f"s3_openai_{key}", "mp3")
        if p:
            cells[f"openai-{key}"] = p

    return cells


# ---------------------------------------------------------------------------
# Orchestration
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> None:
    ap = argparse.ArgumentParser(description="Staged prosody experiment runner (#1273).")
    ap.add_argument("--stages", nargs="+", type=int, default=[0, 1, 2, 3],
                    help="Which stages to run (default: all).")
    ap.add_argument("--ref-audio", default=None, help="Stage 2: reference audio path/URL/base64.")
    ap.add_argument("--ref-text", default=None, help="Stage 2: transcript of the reference audio.")
    args = ap.parse_args(argv)

    print(f"Test text ({len(TEST_TEXT)} chars):\n{TEST_TEXT}\n")
    t0 = time.time()

    all_cells: dict[str, str] = {}
    if 0 in args.stages:
        all_cells.update(stage0_openai())
    if 1 in args.stages:
        all_cells.update(stage1_native())
    if 2 in args.stages:
        all_cells.update(stage2_cloning(args.ref_audio, args.ref_text))
    if 3 in args.stages:
        all_cells.update(stage3_controllability())

    if not all_cells:
        print("\nNo audio produced; aborting metrics.")
        return

    print(f"\nSynthesis done in {time.time() - t0:.0f}s; {len(all_cells)} renders. Measuring melody...")

    # Metrics + contour plot + JSON for everything synthesized.
    result = pm.compare(
        all_cells,
        json_out=str(OUT_DIR / "metrics.json"),
        plot_out=str(OUT_DIR / "contours.png"),
    )
    print()
    pm.print_table(result["metrics"])
    print(f"\nContour plot: {result['plot']}")
    print(f"Metrics JSON: {OUT_DIR / 'metrics.json'}")

    # DTW controllability matrix for Stage 3 (qwen-* and openai-* groups).
    if 3 in args.stages:
        for grp in ("qwen", "openai"):
            keys = [k for k in all_cells if k.startswith(f"{grp}-") and
                    any(s in k for s in ("calm", "tense", "exalted"))]
            if len(keys) >= 2:
                print(f"\n[Stage 3] DTW contour distance ({grp}, 0 = identical melody):")
                for i, ka in enumerate(keys):
                    for kb in keys[i + 1:]:
                        d = pm.dtw_contour_distance(all_cells[ka], all_cells[kb])
                        print(f"  {ka:<18} <-> {kb:<18} : {d:.3f}")


if __name__ == "__main__":
    main()
