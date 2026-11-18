r"""rerun_a0c_chatterbox_chunked.py — re-rendu A0C Chatterbox MTL v3 découpé par phrase + ref_wav.

Cadrage audio c.1467 (reçu 11:09 le 07/10) :
- Chatterbox **découpé par phrase** avec un wav de référence.
- Mesure : WER sur 3 ASR, prosodie, **omissions** (hallucinations / segments sautés).

Le précédent rendu (c.1462) avait un score catastrophique sur la fidélité (93,65 %
WER) et l'omission de segments (2 mesures perdues sous 3 ASR sur 3 — phrases
"des artilleurs sombres alignés avec des fantassins divers" et "sur leurs
épaules de fanfarons"). Le découpage par phrase + un wav de référence doit
réduire l'omission : Chatterbox a moins de "sauts" sur des phrases courtes.

Stratégie :
1. Découpe extract_C en phrases (regex simple sur [.!?]\s+).
2. Phrase 1 sert de **ref_wav** pour les phrases suivantes (consistance de voix).
3. Pour chaque phrase, generate avec `audio_prompt_path=ref_wav_path`.
4. Concatène les wav numpy en un seul.
5. Mesure WER sur l'assemblé.

Pré-requis :
    /d/dev/CoursIA-2/venv/Scripts/python.exe (chatterbox + faster_whisper déjà OK)

Usage :
    /d/dev/CoursIA-2/venv/Scripts/python.exe \\
        MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/rerun_a0c_chatterbox_chunked.py \\
        --text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \\
        --out-dir "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007" \\
        [--lang fr] [--device cuda]
"""
from __future__ import annotations

import argparse
import io
import json
import re
import sys
import time
from pathlib import Path


def split_sentences(text: str) -> list[str]:
    """Découpe grossière par [.!?] suivi d'espace, sans dépendance NLP."""
    # Sépare aussi sur ; pour les phrases longues du narratif Maupassant
    parts = re.split(r"(?<=[.!?])\s+", text.strip())
    return [p.strip() for p in parts if p.strip()]


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text-file", required=True, type=Path)
    p.add_argument("--out-dir", required=True, type=Path)
    p.add_argument("--lang", default="fr")
    p.add_argument("--device", default="cuda")
    p.add_argument("--ref-from-first-sentence", action="store_true", default=True,
                   help="Utilise la première phrase comme ref_wav pour la consistance de voix.")
    args = p.parse_args()

    if not args.text_file.exists():
        print(f"Texte introuvable : {args.text_file}", file=sys.stderr)
        return 2
    text = args.text_file.read_text(encoding="utf-8").strip()

    sentences = split_sentences(text)
    if not sentences:
        print("Aucune phrase détectée.", file=sys.stderr)
        return 2

    args.out_dir.mkdir(parents=True, exist_ok=True)
    out_wav = args.out_dir / "A0C-chatterbox-mtl-v3-chunked.wav"
    metrics_path = args.out_dir / "A0C-chatterbox-mtl-v3-chunked-metrics.json"

    print(f"=== Re-rendu A0C Chatterbox MTL v3 DÉCOUPÉ PAR PHRASE ===")
    print(f"  Texte : {args.text_file} ({len(text)} chars, {len(sentences)} phrases)")
    print(f"  Out : {out_wav}")
    print(f"  Langue : {args.lang}, ref_wav = première phrase synthétisée")
    print()

    # Imports tardifs
    import numpy as np
    import soundfile as sf
    import torch
    from chatterbox.mtl_tts import ChatterboxMultilingualTTS  # noqa: E402

    t_load = time.time()
    model = ChatterboxMultilingualTTS.from_pretrained(args.device)
    t_load_s = time.time() - t_load
    sr = model.sr  # convention chatterbox : sr=24000
    print(f"  Modèle chargé en {t_load_s:.1f}s (sr={sr} Hz)\n")

    # 1) Première phrase — sert de ref_wav
    if args.ref_from_first_sentence:
        ref_text = sentences[0]
        print(f"  [REF] Phrase 1 (ref_wav) : {ref_text[:80]}...")
        t0 = time.time()
        wav_ref = model.generate(ref_text, language_id=args.lang)
        if hasattr(wav_ref, "squeeze"):
            wav_ref_np = wav_ref.squeeze(0).detach().cpu().numpy()
        else:
            wav_ref_np = wav_ref
        ref_wav_path = args.out_dir / ".chunked_ref.wav"
        sf.write(str(ref_wav_path), wav_ref_np, sr)
        t_ref = time.time() - t0
        print(f"    OK en {t_ref:.1f}s, durée {len(wav_ref_np)/sr:.2f}s")
        concat = [wav_ref_np]
        n_chunks = 1
        chunk_durations = [len(wav_ref_np) / sr]
    else:
        ref_wav_path = None
        concat = []
        n_chunks = 0
        chunk_durations = []

    # 2) Phrases suivantes — avec audio_prompt_path
    for i, sent in enumerate(sentences[1:], start=2):
        print(f"  [{i:2d}/{len(sentences)}] {sent[:80]}...")
        t0 = time.time()
        if ref_wav_path is not None:
            wav = model.generate(sent, language_id=args.lang,
                                 audio_prompt_path=str(ref_wav_path))
        else:
            wav = model.generate(sent, language_id=args.lang)
        if hasattr(wav, "squeeze"):
            wav_np = wav.squeeze(0).detach().cpu().numpy()
        else:
            wav_np = wav
        concat.append(wav_np)
        chunk_durations.append(len(wav_np) / sr)
        n_chunks += 1
        print(f"    OK en {time.time()-t0:.1f}s, durée {len(wav_np)/sr:.2f}s")

    # 3) Concatène + silence 200ms entre phrases
    silence = np.zeros(int(sr * 0.2), dtype=np.float32)
    pieces = []
    for i, w in enumerate(concat):
        pieces.append(w)
        if i < len(concat) - 1:
            pieces.append(silence)
    full = np.concatenate(pieces) if pieces else np.zeros(0, dtype=np.float32)
    sf.write(str(out_wav), full, sr)

    total_audio_s = len(full) / sr
    print(f"\n  Concaténé : {n_chunks} phrases, {total_audio_s:.2f}s audio, {out_wav}")

    metrics = {
        "cell": "chatterbox_mtl_v3_chunked",
        "license": "Apache-2.0",
        "size": "0.5B",
        "model_id": "ResembleAI/chatterbox-multilingual",
        "mode": "CHUNKED_SENTENCE + REF_FROM_FIRST",
        "text_file": str(args.text_file),
        "text_chars": len(text),
        "text_sentences": len(sentences),
        "sentences": sentences,
        "n_chunks": n_chunks,
        "chunk_durations_s": chunk_durations,
        "sample_rate": sr,
        "duration_s": float(total_audio_s),
        "ref_wav_path": str(ref_wav_path) if ref_wav_path else None,
        "load_s": t_load_s,
        "wer": None,        # rempli par measure_3asr.py
        "omissions": None,  # rempli par measure_3asr.py (segments de 3+ mots omis)
        "prosody": None,    # rempli par verify_prosody.py
    }
    metrics_path.write_text(json.dumps(metrics, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"  Métriques (synthèse) : {metrics_path}")
    print(f"  WER 3-ASR + omissions : à mesurer par measure_3asr.py (c.1473)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
