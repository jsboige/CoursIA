"""Banc Phase A0 — run un client bakeoff_large sur le passage de référence.

Usage (depuis la racine du dépôt ou worktree) :
    export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
    _runtime/venv-qwen3tts/Scripts/python.exe bakeoff_large/banc_phase_a0.py \\
        --client qwen3_tts_customvoice \\
        --speaker Chelsie \\
        --language French \\
        --instruct "voix posée, débit lent, ton narratif" \\
        --out-root runs/run-20260924-143012/A0-bakeoff/qwen3_tts_customvoice

Le banc applique le client à un passage de référence (~30 s Boule de Suif, fr), mesure :
- VRAM pic
- Wallclock + RTF
- Sortie .wav (24 kHz mono)
- Métriques prosodie : ST-spread, CV, velocity (via scripts/tts_verification/verify_prosody.py)
- WER Whisper-tiny (via faster-whisper)

Verdict plancher Phase A0 :
- Audio sauvé hors dépôt (GDrive) — AUCUN .wav commité
- Métriques sauvées en JSON dans out-root/metrics.json
- Une ligne de banc postée en commentaire #17586 (grain) + dashboard
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

# Permit import des clients bakeoff_large depuis n'importe quel cwd
BAKEOFF_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(BAKEOFF_ROOT))


# Passage de référence (Boule de Suif, Maupassant — ~30 s à débit narratif 150 wpm)
# Tell c.c.c.d.767-L1 strict fondateur : test reproductible et first-hand.
TEST_TEXT_BOULE = (
    "La voiture allait tout doucement. Un froid humide pénétrait les membres ; on ne "
    "voyait rien devant soi ; la nuit était profonde. Les voyageurs, engourdis par "
    "le froid, avaient perdu le désir de parler. Le cocher marchait à côté de la "
    "voiture, la tête inclinée sous la pluie. Les roues grinçaient dans la boue."
)


def run_client(client_name: str, text: str, out_wav: str, **client_kwargs) -> dict:
    """Invoque un client bakeoff_large.<clients.<name>>.synth(text, out_wav, **kwargs)."""
    import importlib
    client_mod = importlib.import_module(f"clients.{client_name}")
    model = client_mod.load_model(device="cuda", dtype="bf16")
    result = client_mod.synth(text=text, out_wav=out_wav, model=model, **client_kwargs)
    return result


def measure_prosody(wav_path: str) -> dict:
    """Délègue à scripts/tts_verification/verify_prosody.py --single."""
    repo_root = BAKEOFF_ROOT.resolve()
    for _ in range(5):
        if (repo_root / "scripts" / "tts_verification" / "verify_prosody.py").exists():
            break
        repo_root = repo_root.parent
    script = repo_root / "scripts" / "tts_verification" / "verify_prosody.py"
    if not script.exists():
        return {"error": f"verify_prosody.py not found at {script}"}
    try:
        out = subprocess.run(
            [sys.executable, str(script), "--single", wav_path, "--json"],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300,
        )
        if out.returncode == 0 and out.stdout.strip():
            return json.loads(out.stdout)
        return {"error": f"verify_prosody exit={out.returncode}", "stderr": out.stderr[:300]}
    except Exception as e:
        return {"error": str(e)}


def measure_wer(wav_path: str, reference_text: str, model_size: str = "tiny") -> dict:
    """WER via faster-whisper (Whisper-tiny par défaut)."""
    try:
        from faster_whisper import WhisperModel
        wm = WhisperModel(model_size, device="cuda" if _cuda_available() else "cpu",
                          compute_type="float16" if _cuda_available() else "int8")
        segments, info = wm.transcribe(wav_path, language="fr", beam_size=5)
        hyp = " ".join(seg.text for seg in segments).strip()
        # WER simple (pas jiwer pour rester dep-free)
        ref_words = reference_text.split()
        hyp_words = hyp.split()
        # Edit distance Levenshtein — implémentation inline pour rester léger
        n = len(ref_words)
        m = len(hyp_words)
        dp = [[0]*(m+1) for _ in range(n+1)]
        for i in range(n+1): dp[i][0] = i
        for j in range(m+1): dp[0][j] = j
        for i in range(1, n+1):
            for j in range(1, m+1):
                if ref_words[i-1] == hyp_words[j-1]:
                    dp[i][j] = dp[i-1][j-1]
                else:
                    dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
        wer = dp[n][m] / max(n, 1)
        return {"wer": float(wer), "hyp": hyp, "model": f"faster-whisper-{model_size}"}
    except Exception as e:
        return {"error": str(e)}


def _cuda_available() -> bool:
    try:
        import torch
        return torch.cuda.is_available()
    except Exception:
        return False


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--client", required=True, help="Nom du module client (sans .py)")
    p.add_argument("--out-root", required=True, help="Dossier de sortie (GDrive-mount recommandé)")
    p.add_argument("--text", default=TEST_TEXT_BOULE)
    p.add_argument("--speaker", default=None)
    p.add_argument("--language", default="French")
    p.add_argument("--instruct", default=None)
    p.add_argument("--skip-wer", action="store_true")
    p.add_argument("--skip-prosody", action="store_true")
    args = p.parse_args()

    out_root = Path(args.out_root)
    out_root.mkdir(parents=True, exist_ok=True)
    out_wav = out_root / f"{args.client}.wav"
    metrics_path = out_root / "metrics.json"

    print(f"=== Banc Phase A0 — client {args.client} ===")
    print(f"Text ({len(args.text)} chars): {args.text[:80]}...")
    print(f"Out: {out_wav}")
    print()

    client_kwargs = {}
    if args.speaker:
        client_kwargs["speaker"] = args.speaker
    if args.language:
        client_kwargs["language"] = args.language
    if args.instruct:
        client_kwargs["instruct"] = args.instruct

    t0 = time.time()
    synth_result = run_client(args.client, args.text, str(out_wav), **client_kwargs)
    t_total = time.time() - t0
    print()
    print(f"Synthèse OK : {synth_result.get('duration_s', 0):.2f}s audio, RTF={synth_result.get('rtf', 0):.3f}, VRAM peak={synth_result.get('vram_peak_gb', 0):.2f} GB")

    metrics = {
        "client": args.client,
        "text": args.text,
        "client_kwargs": client_kwargs,
        "synth": synth_result,
        "wallclock_total_s": t_total,
        "wer": None,
        "prosody": None,
    }

    if not args.skip_wer:
        print("\nMesure WER via faster-whisper-tiny...")
        metrics["wer"] = measure_wer(str(out_wav), args.text)
        if "wer" in metrics["wer"]:
            print(f"  WER = {metrics['wer']['wer']*100:.2f}%")

    if not args.skip_prosody:
        print("\nMesure prosodie via verify_prosody.py...")
        metrics["prosody"] = measure_prosody(str(out_wav))
        print(f"  prosody: {json.dumps(metrics['prosody'], ensure_ascii=False)[:200]}")

    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, ensure_ascii=False)
    print(f"\nMétriques sauvées : {metrics_path}")
    print(f"Banc complet en {t_total:.1f}s.")


if __name__ == "__main__":
    main()
