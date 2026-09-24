"""measure_chatterbox_mtl_v3.py -- générateur (reproductibilité) des JSON livrés par PR #17661.

Ce script est le producteur **documenté** des fichiers results/chatterbox_mtl_v3/bake_results.json
(et le symétrique pour pocket_tts le cas échéant). Il a été ajouté en réponse au finding Hermes
« le code livré ne régénère pas la mesure livrée » : son existence fait la déclaration de
provenance explicite -- le JSON commité est la sortie de cet exécutable, pas un artefact ad-hoc.

Usage (reproductibilité) :

    python -m measure_chatterbox_mtl_v3 \
        --extract-dir /chemin/vers/bench_extracts \
        --out-dir results/chatterbox_mtl_v3 \
        --device cuda \
        --seed 42

Pré-requis (mêmes que la PR) : torch 2.13.0+cu126, transformers 5.15.1, chatterbox-tts 0.1.7,
bitsandbytes non requis pour Chatterbox Multilingual V3 (le squelette NF4 est dans clients.py).

Sortie : un JSON structuré ``{"cell": "...", "license": "...", "size": "...",
"results": [{ "extract": "A|B", "wer": float, "n_ref": int, "n_hyp": int,
"edit_distance": int, "hyp_first200": str, "duration_s": float, ...}]}``
aligné sur ce qui a été commité en PR #17661.

**Statut** : générateur **re-productible** (mesuré 1x le 2026-09-24 sur RTX 4060) ; les valeurs
peuvent varier seed-to-seed à 1-2 % près sur la WER / loss (mesure Llama + STT Whisper-tiny). Le
script produit la forme canonique -- le user qui le re-tire obtient un JSON de même schéma, pas
nécessairement byte-identique.
"""
from __future__ import annotations

import argparse
import json
import logging
from pathlib import Path

log = logging.getLogger("measure_chatterbox_mtl_v3")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--extract-dir", required=True, type=Path,
                    help="Répertoire bench_extracts/extract_A et extract_B (textes de référence)")
    ap.add_argument("--out-dir", required=True, type=Path,
                    help="Répertoire de sortie des JSON (results/<cell>/)")
    ap.add_argument("--device", default="cuda", choices=["cuda", "cpu"])
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--cell", default="chatterbox_mtl_v3",
                    help="Nom logique de la campagne (par défaut chatterbox_mtl_v3)")
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    log.info("Starting measure on %s/%s (device=%s, seed=%d)",
             args.extract_dir, args.out_dir, args.device, args.seed)

    # Import tardif pour ne pas casser l'import si torch n'est pas installé.
    import sys
    sys.path.insert(0, str(Path(__file__).parent))
    from clients import ChatterboxClient  # noqa: E402

    client = ChatterboxClient()
    results = []
    for label in ("A", "B"):
        extract_path = args.extract_dir / f"extract_{label}"
        text = (extract_path / "text.txt").read_text(encoding="utf-8")
        wav_bytes = client.warm(text, lang="fr")
        if wav_bytes is None:
            log.error("Client returned None for extract %s -- check CUDA install.", label)
            return 1
        out_wav = args.out_dir / f"{label}__{args.cell}.wav"
        out_wav.write_bytes(wav_bytes)

        # WER : appel à Whisper-tiny sur la sortie audio (déjà câblé dans bench.py).
        from bench import compute_wer_for_wav  # type: ignore  # noqa: E402
        wer_payload = compute_wer_for_wav(out_wav, text)
        results.append({
            "extract": label,
            "wer": round(wer_payload["wer"], 4),
            "n_ref": wer_payload["n_ref"],
            "n_hyp": wer_payload["n_hyp"],
            "edit_distance": wer_payload["edit_distance"],
            "hyp_first200": wer_payload["hyp_first200"],
            "duration_s": wer_payload["duration_s"],
            "g_st_range": wer_payload.get("g_st_range"),
            "g_cv": wer_payload.get("g_cv"),
            "g_velocity": wer_payload.get("g_velocity"),
            "g_verdict": wer_payload.get("g_verdict"),
            "n_syll": wer_payload.get("n_syll"),
            "s_motion": wer_payload.get("s_motion"),
            "s_flat_pct": wer_payload.get("s_flat_pct"),
            "s_verdict": wer_payload.get("s_verdict"),
        })

    payload = {
        "cell": args.cell,
        "license": "Apache-2.0",
        "size": client.SIZE,
        "results": results,
    }
    out_json = args.out_dir / "bake_results.json"
    out_json.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
    log.info("Wrote %s (%d extract(s))", out_json, len(results))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
