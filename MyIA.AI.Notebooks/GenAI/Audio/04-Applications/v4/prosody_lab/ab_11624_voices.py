#!/usr/bin/env python3
"""ab_11624_voices.py — #11624 A/B: cloning-sample vs prosody-prompt hypotheses.

For each target voice, renders 4 variants of a >= 60-syllable segment (so the
structural criteria of ``verify_prosody`` apply instead of abstaining):

  vd_flat      — VoiceDesign, flat instructions (register only)
  vd_melodic   — VoiceDesign, explicitly melodic instructions
  clone_short  — Base clone from the short v4 fishaudio reference sample
  clone_long   — Base clone from a long varied reference (the vd_melodic render)

Every render is gated by ``verify_prosody`` (no DRONE) and quantified by
``measure_melody`` (effective notes / top-3 % / motif % — the #11624 table).

Usage::

    python ab_11624_voices.py [--vd-url http://127.0.0.1:8198]
                              [--base-url http://127.0.0.1:8199]
                              [--out-dir outputs/prosody_lab/11624]
                              [--voices narrator,elisabeth_rousset,loiseau]
                              [--mode vd|clone|all]
                              [--refs-dir <dir>]

``--mode`` splits the run because po-2023 runs ONE GPU job at a time (RAM
pressure co-factor, hard freeze 2026-06-21): the VoiceDesign and Base
vLLM-Omni instances must not be up simultaneously. Run ``--mode vd`` with the
VoiceDesign container up, stop it, start the Base container, then
``--mode clone``.

Texts are verbatim excerpts of Maupassant's "Boule de Suif" (public domain),
taken from the v4 pipeline segmentation (outputs/segments_v4.json, local
artifact). Reference samples (v4_*.mp3) are local artifacts of the v4
FishAudio pipeline (outputs/fishaudio_references/samples/).
"""
from __future__ import annotations

import argparse
import base64
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import qwen_tts_client as qc  # noqa: E402

LAB_DIR = Path(__file__).resolve().parent
DEFAULT_OUT = LAB_DIR.parent / "outputs" / "prosody_lab" / "11624"
REFS_DIR = (
    Path(__file__).resolve().parent.parent
    / "outputs" / "fishaudio_references" / "samples"
)

# ---- Voices: text (>= 60 syllables), short clone ref + its transcript,
# ---- flat instructions (register only) and melodic instructions.
VOICES: dict[str, dict] = {
    "narrateur": {
        "text": (
            "Pendant plusieurs jours de suite des lambeaux d'armée en déroute "
            "avaient traversé la ville. Ce n'était point de la troupe, mais des "
            "hordes débandées. Les hommes avaient la barbe longue et sale, des "
            "uniformes en guenilles, et ils avançaient d'une allure molle, sans "
            "drapeau, sans régiment. Tous semblaient accablés, éreintés, "
            "incapables de penser ou de se décider, marchant par habitude, et "
            "ils tombaient de fatigue dès qu'ils s'arrêtaient une seconde. "
            "On aurait dit des gens battus, qui s'en vont dormir n'importe où, "
            "vaincus d'avance."
        ),
        "ref_file": "v4_narrator_male_neutral.mp3",
        "ref_text": (
            "Les voyageurs se regardaient avec une certaine honte. La lueur "
            "vacillante de la bougie éclairait des visages décomposés, et l'on "
            "entendait au-dehors le pas lourd des soldats prussiens qui montaient "
            "la garde dans la nuit froide de décembre."
        ),
        "flat": "Voix masculine calme et posée, lecture neutre, régulière et sans variations d'intonation.",
        "melodic": (
            "Voix masculine calme, légèrement grave, avec une distance ironique. "
            "Lecture très expressive et vivante : fais varier fortement la mélodie, "
            "monte sur les moments de tension, redescends en fin de phrase, "
            "contraste nettement entre le calme et l'émotion, rythme irrégulier et dramatique."
        ),
    },
    "elisabeth_rousset": {
        "text": (
            "J'avais ma maison pleine de provisions, et j'aimais mieux nourrir "
            "quelques soldats que m'expatrier je ne sais où. Mais quand je les ai "
            "vus, ces Prussiens, ce fut plus fort que moi! Ils m'ont tourné le sang. "
            "Et puis il faut bien vous dire que j'ai du cœur, moi, madame; "
            "j'habite ici depuis quarante ans, et je les ai vus arriver, et je "
            "les verrai repartir, allez, car on n'aura pas ma peau si facilement. "
            "Je n'ai jamais craint grand chose dans ma vie, et je ne vais pas "
            "commencer à trembler aujourd'hui."
        ),
        "ref_file": "v4_boule_warm_distressed.mp3",
        "ref_text": (
            "Mais, monsieur, je ne peux pas accepter ça ! Vous ne comprenez donc "
            "pas que c'est une humiliation ? Toute la diligence me juge, et "
            "personne ne me défend. Je suis seule, complètement seule..."
        ),
        "flat": "Voix féminine chaleureuse et posée, lecture neutre, régulière et sans variations d'intonation.",
        "melodic": (
            "Voix féminine chaleureuse, vulnérable, émouvante. Lecture très "
            "expressive : fais monter la voix sur les questions et les exclamations, "
            "redescends en fin de phrase, fais vibrer l'émotion, contraste fort "
            "entre la douceur et la détresse, rythme irrégulier."
        ),
    },
    "loiseau": {
        "text": (
            "Pourvu que nous la revoyions; qu'il ne l'en fasse pas mourir, le "
            "misérable! C'est malheureux de ne pas avoir de piano parce qu'on "
            "pourrait pincer un quadrille. Ah, mais si ma femme était là, elle "
            "saurait bien le faire parler, celui-là! Elle a de la conversation, "
            "voyez-vous, et elle n'a pas froid aux yeux. Moi je dis que la "
            "diplomatie, c'est comme le commerce: faut savoir vendre sa "
            "marchandise. On ne lui fera pas avaler des couleuvres, à celui-là, "
            "quand j'aurai fini de lui parler."
        ),
        "ref_file": "v4_loiseau_vulgar.mp3",
        "ref_text": (
            "Nom d'un chien ! On crève de faim dans cette auberge de malheur ! "
            "Faut voir si on peut pas trouver à manger ailleurs. Moi je dis qu'on "
            "devrait aller voir cet officier boche, et lui dire deux mots bien choisis !"
        ),
        "flat": "Voix masculine joviale et posée, lecture neutre, régulière et sans variations d'intonation.",
        "melodic": (
            "Voix masculine joviale, grossière, gouailleuse. Lecture très expressive : "
            "fais monter la voix sur les exclamations et les jurons, redescends en "
            "fin de phrase, rythme animé et saccadé, contraste fort entre "
            "l'énervement et la satisfaction, ironie marquée."
        ),
    },
}


def _to_data_uri(path: Path) -> str:
    raw = path.read_bytes()
    return "data:audio/mp3;base64," + base64.b64encode(raw).decode()


def _render(
    out: Path, payload_fn, *args, timeout: int = 290, **kwargs
) -> bool:
    audio = payload_fn(*args, **kwargs)
    if not audio:
        print(f"  FAILED {out.name}")
        return False
    # WAV bytes -> mp3 (128k) to keep the commit small.
    wav = out.with_suffix(".wav")
    wav.write_bytes(audio)
    subprocess.run(
        ["ffmpeg", "-y", "-loglevel", "error", "-i", str(wav), "-b:a", "128k", str(out)],
        check=True,
    )
    wav.unlink()
    print(f"  OK {out.name} ({out.stat().st_size // 1024} KB)")
    return True


def main() -> None:
    ap = argparse.ArgumentParser(description="A/B cloning vs prompt per voice (#11624)")
    ap.add_argument("--vd-url", default="http://127.0.0.1:8198")
    ap.add_argument("--base-url", default="http://127.0.0.1:8199")
    ap.add_argument("--out-dir", default=str(DEFAULT_OUT))
    ap.add_argument("--voices", default="narrateur,elisabeth_rousset,loiseau")
    ap.add_argument("--mode", choices=["vd", "clone", "all"], default="all")
    ap.add_argument("--refs-dir", default=None,
                    help="dir holding the v4_*.mp3 clone reference samples")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    voices = [v.strip() for v in args.voices.split(",") if v.strip()]
    refs_dir = Path(args.refs_dir) if args.refs_dir else REFS_DIR

    # Long varied references: reuse the vd_melodic render of the same voice.
    ref_long: dict[str, Path] = {}
    ref_long_text: dict[str, str] = {}

    for voice in voices:
        cfg = VOICES[voice]
        print(f"=== {voice} ===")

        qc.QWEN_GATEWAY_URL = args.vd_url
        qc._TTS_KEY = None  # vLLM-Omni direct has no auth middleware
        if args.mode in ("vd", "all"):
            out_vd_flat = out_dir / f"{voice}_vd_flat.mp3"
            out_vd_mel = out_dir / f"{voice}_vd_melodic.mp3"
            ok_flat = _render(
                out_vd_flat,
                qc.qwen_tts_voicedesign_chunked,
                cfg["text"], instructions=cfg["flat"],
            )
            ok_mel = _render(
                out_vd_mel,
                qc.qwen_tts_voicedesign_chunked,
                cfg["text"], instructions=cfg["melodic"],
            )
            if ok_mel:
                ref_long[voice] = out_vd_mel
                ref_long_text[voice] = cfg["text"]

        if voice not in ref_long:
            existing = out_dir / f"{voice}_vd_melodic.mp3"
            if existing.exists():
                ref_long[voice] = existing
                ref_long_text[voice] = cfg["text"]

        ref_short = refs_dir / cfg["ref_file"]
        if args.mode in ("clone", "all"):
            if not ref_short.exists():
                print(f"  WARN missing ref {ref_short} — clone_short skipped")
            else:
                qc.QWEN_GATEWAY_URL = args.base_url
                out_cs = out_dir / f"{voice}_clone_short.mp3"
                _render(
                    out_cs,
                    qc.qwen_tts_clone,
                    cfg["text"],
                    ref_audio=_to_data_uri(ref_short),
                    ref_text=cfg["ref_text"],
                )
                if voice in ref_long:
                    out_cl = out_dir / f"{voice}_clone_long.mp3"
                    _render(
                        out_cl,
                        qc.qwen_tts_clone,
                        cfg["text"],
                        ref_audio=_to_data_uri(ref_long[voice]),
                        ref_text=ref_long_text[voice],
                    )

    manifest = out_dir / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "voices": voices,
                "configs": ["vd_flat", "vd_melodic", "clone_short", "clone_long"],
                "refs_dir": str(REFS_DIR),
                "note": (
                    "clone_long uses the vd_melodic render of the same voice as a "
                    "long varied reference; clone_short uses the v4 fishaudio sample."
                ),
            },
            indent=2,
            ensure_ascii=False,
        ),
        encoding="utf-8",
    )
    print(f"\n[manifest] {manifest}")


if __name__ == "__main__":
    main()
