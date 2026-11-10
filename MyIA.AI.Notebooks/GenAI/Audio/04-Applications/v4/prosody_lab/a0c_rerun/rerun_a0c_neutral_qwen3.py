"""rerun_a0c_neutral_qwen3.py — re-rendu A0C Qwen3-TTS CustomVoice en mode NEUTRE.

Cadrage audio c.1467 (reçu 11:09 le 07/10) :
- Qwen3-TTS en réglage **neutre** (sans « débit lent »).
- Mesure : WER sur 3 ASR (tiny / small / large-v3), prosodie.
- Sortie : A0-review-20261007/A0C-qwen3tts-customvoice-neutral.{wav,metrics.json}.

Mode neutre = `instruct=None` (défaut du client). c.1462 a tourné Chatterbox MTL v3
+ Qwen3-TTS-1.7B CustomVoice avec instruct "voix posée, débit lent, ton narratif"
(5× inflation "débit lent" mesurée sur WER). Le neutre doit retomber à un
rendement plus proche de la lecture naturelle.

Pré-requis :
    /d/dev/CoursIA-2/venv-qwen3tts/Scripts/python.exe -m pip install qwen-tts torch torchaudio

Usage (depuis racine dépôt ou worktree) :
    /d/dev/CoursIA-2/venv-qwen3tts/Scripts/python.exe \\
        MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/rerun_a0c_neutral_qwen3.py \\
        --text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \\
        --out-dir "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007" \\
        [--speaker serena] [--language French] [--device cuda] [--dtype bf16]
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text-file", required=True, type=Path,
                   help="Fichier texte de référence (extract_C_long_narration.txt).")
    p.add_argument("--out-dir", required=True, type=Path,
                   help="Dossier de sortie (A0-review-20261007).")
    p.add_argument("--speaker", default="serena")
    p.add_argument("--language", default="French")
    p.add_argument("--device", default="cuda")
    p.add_argument("--dtype", default="bf16", choices=["bf16", "fp16", "fp32"])
    args = p.parse_args()

    if not args.text_file.exists():
        print(f"Texte introuvable : {args.text_file}", file=sys.stderr)
        return 2
    text = args.text_file.read_text(encoding="utf-8").strip()
    if not text:
        print(f"Texte vide : {args.text_file}", file=sys.stderr)
        return 2

    args.out_dir.mkdir(parents=True, exist_ok=True)
    out_wav = args.out_dir / "A0C-qwen3tts-customvoice-neutral.wav"
    metrics_path = args.out_dir / "A0C-qwen3tts-customvoice-neutral-metrics.json"

    # Imports tardifs (env potentiellement absent)
    import torch
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "bakeoff_large"))
    from clients import qwen3_tts_customvoice as qwen  # noqa: E402

    print(f"=== Re-rendu A0C Qwen3-TTS NEUTRE ===")
    print(f"  Texte : {args.text_file} ({len(text)} chars, {len(text.split())} mots)")
    print(f"  Out : {out_wav}")
    print(f"  Speaker={args.speaker} Language={args.language} (instruct=None = NEUTRE)")
    print()

    t_load = time.time()
    model = qwen.load_model(device=args.device, dtype=args.dtype)
    t_load_s = time.time() - t_load
    print(f"  Modèle chargé en {t_load_s:.1f}s\n")

    t_synth = time.time()
    synth_result = qwen.synth(
        text=text,
        out_wav=str(out_wav),
        model=model,
        language=args.language,
        speaker=args.speaker,
        instruct=None,  # *** NEUTRE — sans « débit lent » ***
    )
    t_synth_s = time.time() - t_synth
    print(f"\n  Synthèse OK en {t_synth_s:.1f}s : {synth_result.get('duration_s', 0):.2f}s audio, "
          f"RTF={synth_result.get('rtf', 0):.3f}, VRAM peak={synth_result.get('vram_peak_gb', 0):.2f} GB")

    metrics = {
        "cell": "qwen3_tts_customvoice_neutral",
        "license": "Apache-2.0",
        "size": "1.7B",
        "model_id": "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",
        "mode": "NEUTRAL (instruct=None)",
        "text_file": str(args.text_file),
        "text_chars": len(text),
        "text_words": len(text.split()),
        "speaker": args.speaker,
        "language": args.language,
        "load_s": t_load_s,
        "synth": synth_result,
        "wallclock_total_s": t_load_s + t_synth_s,
        "wer": None,        # rempli par measure_3asr.py
        "prosody": None,    # rempli par verify_prosody.py (à part)
    }
    metrics_path.write_text(json.dumps(metrics, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"\n  Métriques (synthèse) : {metrics_path}")
    print(f"  WER 3-ASR : à mesurer par measure_3asr.py (c.1473)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
