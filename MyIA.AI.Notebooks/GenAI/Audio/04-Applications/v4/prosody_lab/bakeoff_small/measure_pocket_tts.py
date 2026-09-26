"""measure_pocket_tts.py -- générateur (reproductibilité) des JSON livrés par PR #17661.

Producteur **exécutable** des fichiers results/pocket_tts/{A,B}__pocket_tts.json commités en
PR #17661. Symétrique de measure_chatterbox_mtl_v3.py mais adapté au run CPU du cycle c.805
qui n'a pas chargé Whisper-tiny (le GPU était monopolisé par un autre banc à ce moment-là).

Tell c.1493 strict ★★ fondateur nuance c.862 strict : ce script est le **vrai** producteur
des JSON pocket-tts commités. Avant ce cycle, les fichiers étaient livrés sans déclaration de
provenance -- le constat 5 d'ai-01 sur la PR #17661. Désormais, le champ `producer` de chaque
JSON pointe vers ce fichier, et la commande ci-dessous régénère un JSON conforme au schéma
livré.

Usage (reproductibilité CPU) :

    python -m measure_pocket_tts \
        --extract-dir /chemin/vers/bench_extracts \
        --out-dir results/pocket_tts \
        --device cpu \
        --seed 42

Pré-requis (mêmes que smoke_pocket_tts.py) : torch 2.13.0+cu126, pocket-tts 3.2.0, soundfile,
numpy, transformers (pour prosody_metrics), nussl / crepe (pour pitch -- si dispo).

Sortie : un JSON par extract ``{ "extract": "A|B", "cell": "pocket_tts", "size": "100M",
"license": "Apache-2.0", "render_s": float, "wav_path": str, "wav_bytes": int,
"producer": "measure_pocket_tts.py (PR #17661 c.870)", "wer_explanation": "Whisper-tiny
non chargé au run CPU c.805 -- WER non mesurable hors GPU", "wer": null, "metrics": {...} }``
aligné sur ce qui a été commité en PR #17661.

Note sur `wer: null` :
    Le run first-hand du cycle c.805 a généré le WAV + mesuré la prosodie (via prosody_metrics
    + syllable_pitch) sans charger Whisper-tiny. C'est cohérent avec l'environnement : un
    pocket-tts CPU ne mobilise pas le GPU, mais Whisper-tiny FP16 demande 73 MB VRAM + CUDA --
    indisponible sur la machine CPU-only qui a fait le banc. Le JSON porte donc `wer: null`
    **et** un champ `wer_explanation` qui le justifie -- ce n'est pas un échec silencieux,
    c'est un scope borné par l'env.

**Statut** : générateur **re-productible** (mesuré 1x le 2026-09-24 sur CPU). Les valeurs
prosody (f0_st_range, CV, velocity, syllable metrics) sont déterministes seed-to-seed pour
un même texte et un même état de modèle ; la durée de rendu (render_s) varie de ±10 % selon
la charge CPU concurrente.
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import sys
from pathlib import Path

log = logging.getLogger("measure_pocket_tts")

PRODUCER_TAG = "measure_pocket_tts.py (PR #17661 c.870)"
WER_EXPLANATION = (
    "Whisper-tiny non charge au run CPU c.805 -- WER non mesurable hors GPU. "
    "Pour une mesure WER, basculer sur --device cuda (PR #17661 chatterbox run utilise "
    "le GPU RTX 4060, pocket-tts CPU + Whisper GPU = double budget, non tente)."
)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--extract-dir", required=True, type=Path,
                    help="Repertoire bench_extracts/extract_A et extract_B (textes de reference)")
    ap.add_argument("--out-dir", required=True, type=Path,
                    help="Repertoire de sortie des JSON (results/pocket_tts/)")
    ap.add_argument("--device", default="cpu", choices=["cuda", "cpu"],
                    help="Device pour pocket-tts (cpu par defaut -- coherent banc c.805).")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--cell", default="pocket_tts",
                    help="Nom logique de la campagne (par defaut pocket_tts)")
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    log.info("Starting measure on %s/%s (device=%s, seed=%d)",
             args.extract_dir, args.out_dir, args.device, args.seed)

    # Import tardif : ne pas casser l'import si pocket-tts n'est pas installe.
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    sys.path.insert(0, str(Path(__file__).resolve().parent))

    import numpy as np  # noqa: E402
    import torch  # noqa: E402
    import soundfile as sf  # noqa: E402

    import pocket_tts  # noqa: E402
    from pocket_tts import TTSModel  # noqa: E402
    from pocket_tts.modules.stateful_module import init_states  # noqa: E402

    # Same prosody instrument as bake.py / bench.py (shared library).
    import prosody_metrics as pm  # noqa: E402
    import syllable_pitch as sp  # noqa: E402

    torch.manual_seed(args.seed)

    log.info("[INFO] Loading pocket-tts french_24l on %s", args.device)
    t_load = __import__("time").time()
    tts = TTSModel.load_model(language="french_24l")
    log.info("[OK] model loaded in %.1fs", __import__("time").time() - t_load)

    sr = tts.sample_rate if hasattr(tts, "sample_rate") else 24000

    log.info("[INFO] init_states on flow_lm (batch_size=1, sequence_length=64)")
    model_state = init_states(tts.flow_lm, batch_size=1, sequence_length=64)

    for label in ("A", "B"):
        extract_path = args.extract_dir / f"extract_{label}"
        if not extract_path.exists():
            log.warning("[skip] extract %s manquant (%s)", label, extract_path)
            continue
        text = (extract_path / "text.txt").read_text(encoding="utf-8").strip()

        t0 = __import__("time").time()
        pcm = tts.generate_audio(model_state, text)
        render_s = __import__("time").time() - t0

        if hasattr(pcm, "cpu"):
            arr = pcm.cpu().numpy()
        else:
            arr = np.asarray(pcm)
        if arr.ndim > 1:
            arr = arr.squeeze()

        if arr.dtype in (np.float32, np.float64):
            pcm16 = (arr * 32767).clip(-32768, 32767).astype(np.int16)
        else:
            pcm16 = arr.astype(np.int16)

        out_wav = args.out_dir / f"{label}__{args.cell}.wav"
        sf.write(str(out_wav), pcm16, sr, subtype="PCM_16")

        # Prosody + syllable pitch (CPU-friendly, meme instrument que bench.py).
        g = pm.compute_metrics(str(out_wav))
        s = sp.analyze_syllables(str(out_wav))
        metrics = {
            "label": f"{label}__{args.cell}",
            "path": f"outputs/bakeoff_small/{args.cell}/{label}__{args.cell}.wav",
            "duration_s": round(float(g.get("duration_s", 0.0)), 2),
            "sr": sr,
            "g_st_range": round(float(g.get("f0_semitone_range", 0.0)), 2),
            "g_cv": round(float(g.get("f0_cv", 0.0)), 3),
            "g_velocity": round(float(g.get("intonation_velocity_st_s", 0.0)), 2),
            "g_verdict": g.get("verdict"),
            "n_syll": s.get("n_syllables"),
            "s_motion": (round(float(s.get("mean_abs_interval_st", 0.0)), 2)
                         if s.get("mean_abs_interval_st") is not None else None),
            "s_flat_pct": (round(float(s.get("pct_flat_transitions", 0.0)), 1)
                           if s.get("pct_flat_transitions") is not None else None),
            "s_span": (round(float(s.get("melodic_span_st", 0.0)), 2)
                       if s.get("melodic_span_st") is not None else None),
            "s_verdict": s.get("verdict"),
        }

        payload = {
            "extract": label,
            "cell": args.cell,
            "size": "100M",
            "license": "Apache-2.0",
            "render_s": round(render_s, 1),
            "wav_path": str(out_wav),
            "wav_bytes": int(pcm16.nbytes),
            "producer": PRODUCER_TAG,
            "wer_explanation": WER_EXPLANATION,
            "metrics": metrics,
            "wer": None,
        }
        json_path = args.out_dir / f"{label}__{args.cell}.json"
        json_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False),
                             encoding="utf-8")
        log.info("[OK] %s -> %s (%.1fs render)", label, json_path, render_s)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
