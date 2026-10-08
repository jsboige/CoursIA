"""measure_3asr.py — mesure WER sur 3 ASR (tiny, small, large-v3) + détection d'omissions.

Cadrage audio c.1467 (DM ai-01 11:09 le 07/10) :
- Mesure WER sur 3 ASR, prosodie, **omissions** (segments de 3+ mots omis sous ≥2 ASR sur 3).

Entrée : un fichier .wav (Qwen3 neutre OU Chatterbox chunked) + le texte de référence.
Sortie : mise à jour du metrics.json existant (ajout wer + omissions).

Usage :
    /d/dev/CoursIA-2/venv/Scripts/python.exe \\
        MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/a0c_rerun/measure_3asr.py \\
        --wav "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/A0C-qwen3tts-customvoice-neutral.wav" \\
        --ref-text-file "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/extract_C_long_narration.txt" \\
        --metrics-json "G:/Mon Drive/MyIA/Projets/BibliothequesSonores/A0-review-20261007/A0C-qwen3tts-customvoice-neutral-metrics.json" \\
        [--asr-models tiny small large-v3] [--device cuda]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path


def _wer(ref_words: list[str], hyp_words: list[str]) -> float:
    """WER par distance de Levenshtein (inline, jiwer-free)."""
    n, m = len(ref_words), len(hyp_words)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        dp[i][0] = i
    for j in range(m + 1):
        dp[0][j] = j
    for i in range(1, n + 1):
        for j in range(1, m + 1):
            if ref_words[i - 1] == hyp_words[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1])
    return dp[n][m] / max(n, 1)


def _transcribe_with_faster_whisper(wav_path: str, model_size: str, device: str) -> str:
    """Transcrit via faster-whisper, retourne la chaîne hyp complète."""
    from faster_whisper import WhisperModel
    wm = WhisperModel(
        model_size,
        device=device if device == "cuda" else "cpu",
        compute_type="float16" if device == "cuda" else "int8",
    )
    segments, info = wm.transcribe(wav_path, language="fr", beam_size=5)
    return " ".join(seg.text for seg in segments).strip()


def _detect_omissions(ref_text: str, hyps: dict[str, str], min_words: int = 3) -> dict:
    """Détecte les segments de ≥ min_words mots omis sous ≥ 2 ASR sur 3.

    Stratégie : pour chaque segment de N≥min_words mots du ref, vérifier s'il
    apparaît (en substring) dans chaque hyp. Un segment est "omis" si absent
    de ≥ 2 hyps. Retourne la liste des segments omis + le verdict global.
    """
    sentences = re.split(r"(?<=[.!?])\s+", ref_text.strip())
    segments = [s.strip() for s in sentences if len(s.strip().split()) >= min_words]
    omitted = []
    for seg in segments:
        per_asr = {name: (seg in hyp) for name, hyp in hyps.items()}
        n_absent = sum(1 for v in per_asr.values() if not v)
        if n_absent >= 2:
            omitted.append({"segment": seg, "n_words": len(seg.split()),
                            "absent_in": [k for k, v in per_asr.items() if not v]})
    return {
        "n_segments_checked": len(segments),
        "n_omitted": len(omitted),
        "segments": omitted,
    }


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--wav", required=True, type=Path)
    p.add_argument("--ref-text-file", required=True, type=Path)
    p.add_argument("--metrics-json", required=True, type=Path,
                   help="metrics.json à enrichir (le script écrit en place).")
    p.add_argument("--asr-models", nargs="+", default=["tiny", "small", "large-v3"])
    p.add_argument("--device", default="cuda")
    args = p.parse_args()

    if not args.wav.exists():
        print(f"WAV introuvable : {args.wav}", file=sys.stderr)
        return 2
    if not args.ref_text_file.exists():
        print(f"Ref texte introuvable : {args.ref_text_file}", file=sys.stderr)
        return 2
    if not args.metrics_json.exists():
        print(f"metrics.json introuvable : {args.metrics_json}", file=sys.stderr)
        return 2

    ref_text = args.ref_text_file.read_text(encoding="utf-8").strip()
    ref_words = ref_text.split()

    print(f"=== Mesure 3-ASR sur {args.wav.name} ===")
    print(f"  Ref : {len(ref_text)} chars, {len(ref_words)} mots")
    print(f"  ASR : {args.asr_models}")
    print()

    metrics = json.loads(args.metrics_json.read_text(encoding="utf-8"))
    hyps = {}
    wer_by_model = {}
    for model_size in args.asr_models:
        t0 = time.time()
        try:
            hyp = _transcribe_with_faster_whisper(str(args.wav), model_size, args.device)
        except Exception as e:
            print(f"  [{model_size}] ÉCHEC : {e}", file=sys.stderr)
            wer_by_model[model_size] = {"error": str(e)}
            continue
        dt = time.time() - t0
        wer = _wer(ref_words, hyp.split())
        hyps[model_size] = hyp
        wer_by_model[model_size] = {
            "wer": float(wer),
            "wer_pct": round(wer * 100, 2),
            "hyp_words": len(hyp.split()),
            "wallclock_s": round(dt, 1),
        }
        print(f"  [{model_size}] WER = {wer*100:.2f}% ({len(hyp.split())} mots, {dt:.1f}s)")

    # Omissions (si on a au moins 2 hyps)
    omissions = None
    if len(hyps) >= 2:
        omissions = _detect_omissions(ref_text, hyps, min_words=3)
        print(f"\n  Omissions (≥ 3 mots, ≥ 2 ASR) : {omissions['n_omitted']} / "
              f"{omissions['n_segments_checked']} segments")
        for o in omissions["segments"]:
            print(f"    - « {o['segment'][:80]}… » absent de {o['absent_in']}")

    # Mise à jour metrics.json
    metrics["wer"] = {
        "by_model": wer_by_model,
        "ref_text_file": str(args.ref_text_file),
        "hyps_full": hyps,
    }
    metrics["omissions"] = omissions
    args.metrics_json.write_text(json.dumps(metrics, indent=2, ensure_ascii=False),
                                 encoding="utf-8")
    print(f"\n  metrics.json enrichi : {args.metrics_json}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
