"""Banc Phase A0 — run un client bakeoff_large sur le passage de référence.

Usage (depuis la racine du dépôt ou worktree) :
    export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
    _runtime/venv-qwen3tts/Scripts/python.exe bakeoff_large/banc_phase_a0.py \\
        --client qwen3_tts_customvoice \\
        --speaker serena \\
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
# strict fondateur : test reproductible et first-hand.
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


def _librosa_available(python_exe: str) -> bool:
    """L'organe importe librosa en differe (prosody_metrics.load_audio) : un
    interpreteur qui ne l'a pas ne le montre qu'a l'execution, jamais a l'import."""
    try:
        out = subprocess.run(
            [python_exe, "-c", "import librosa"],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=180,
        )
        return out.returncode == 0
    except Exception:
        return False


def resolve_prosody_python(repo_root: Path) -> tuple[str, str]:
    """Interpreteur de la jambe prosodie, et provenance du choix.

    L'organe tourne en SOUS-PROCESSUS, mais `sys.executable` est l'interpreteur du
    BANC -- donc le venv du CLIENT mesure. La jambe prosodie ne marchait que pour
    les clients dont le venv porte librosa (venv-cosyvoice3) et echouait en rc=1
    pour les autres (venv-zonos) ; l'echec etait alors rapporte comme un
    `verify_prosody exit=1` attribue au client. La colonne prosodie du bakeoff
    etait donc biaisee vers les clients qui ont librosa par accident, et non par
    qualite -- un biais de mesure, pas un defaut de client.

    Priorite : PROSODY_PYTHON (explicite), puis l'interpreteur courant s'il a
    librosa, puis un venv frere de _runtime/ qui l'a. A defaut l'interpreteur
    courant, et l'erreur dira lequel -- pour ne plus accuser le client.
    """
    forced = os.environ.get("PROSODY_PYTHON")
    if forced:
        return forced, "PROSODY_PYTHON"
    if _librosa_available(sys.executable):
        return sys.executable, "sys.executable (librosa present)"
    pattern = "venv-*/Scripts/python.exe" if os.name == "nt" else "venv-*/bin/python"
    for cand in sorted((repo_root / "_runtime").glob(pattern)):
        if _librosa_available(str(cand)):
            return str(cand), f"_runtime/{cand.parent.parent.name} (auto-detecte)"
    return sys.executable, "sys.executable (aucun interpreteur avec librosa trouve)"


def measure_prosody(wav_path: str) -> dict:
    """Délègue à scripts/tts_verification/verify_prosody.py --single."""
    rel_script = Path("scripts") / "tts_verification" / "verify_prosody.py"
    repo_root = BAKEOFF_ROOT.resolve()
    # Remontee jusqu'au marqueur reel (.git du worktree, ou le script lui-meme),
    # jamais une borne fixe : BAKEOFF_ROOT est a 7 niveaux sous la racine, et une
    # borne a 5 s'arretait sur GenAI/ -- rendant "not found" un organe qui existe (#18442).
    # Un .gitignore intermediaire ne doit pas arreter la remontee (cf. clients/cosyvoice3.py).
    while repo_root != repo_root.parent:
        if (repo_root / rel_script).exists() or (repo_root / ".git").exists():
            break
        repo_root = repo_root.parent
    script = repo_root / rel_script
    if not script.exists():
        return {"error": f"verify_prosody.py not found at {script}"}
    python_exe, source = resolve_prosody_python(repo_root)
    try:
        out = subprocess.run(
            # `--single` imprime deja le rapport JSON sur stdout ; `--json` attend un
            # CHEMIN et n'est honore que par la branche `--audio-dir` de l'organe
            # (verify_prosody.py:391,408). Le passer nu faisait sortir argparse en rc=2.
            [python_exe, str(script), "--single", wav_path],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=300,
        )
        if out.returncode == 0 and out.stdout.strip():
            report = json.loads(out.stdout)
            if isinstance(report, dict):
                # Trace de l'interpreteur : la colonne prosodie reste auditable
                # meme quand l'auto-detection a choisi un venv frere.
                report["_interpreter"] = {"path": python_exe, "source": source}
            return report
        # Panne d'environnement, pas defaut du client mesure : on la nomme telle quelle.
        if "No module named 'librosa'" in (out.stderr or ""):
            return {
                "error": (f"prosodie indisponible : l'interpreteur {python_exe} n'a pas "
                          "librosa. Definir PROSODY_PYTHON vers un venv qui l'a."),
                "interpreter": python_exe, "interpreter_source": source,
                "stderr": out.stderr[:300],
            }
        return {"error": f"verify_prosody exit={out.returncode}",
                "interpreter": python_exe, "interpreter_source": source,
                "stderr": out.stderr[:300]}
    except Exception as e:
        return {"error": str(e), "interpreter": python_exe, "interpreter_source": source}


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
