"""Client Fun-CosyVoice3-0.5B-2512 pour Phase A0 #17586 bakeoff_large.

Mode : FunAudioLLM/Fun-CosyVoice3-0.5B-2512 (Apache-2.0, FR natif parmi 9 langues,
zero-shot cross-lingual + instruct2). Slot 1 de la recommandation shortlist.

Installation (env propre, regle F) : cf env_setup/SETUP.md section CosyVoice3.
Chargement officiel (carte HF) : repo FunAudioLLM/CosyVoice (submodule Matcha-TTS)
+ snapshot_download du modele, puis cosyvoice.cli.cosyvoice.AutoModel.

Interface uniforme (cf. __init__.py) :
    load_model(model_id, device, dtype) -> AutoModel
    synth(text, out_wav, model, language, speaker, instruct, **kwargs) -> dict

Choix de prompt vocal (canonique carte, reproductible) :
    - zero_shot (defaut) : prompt wav asset du repo (voix zh, transcript carte) +
      texte FR -> clone cross-lingual zero-shot, la capacite A0 sous test.
    - instruct2 (si --instruct fourni) : instruction NL FR (ex: ton narratif, posé).

Prong A : organ-first = package officiel cosyvoice du repo FunAudioLLM/CosyVoice
(pas de reimplementation transformers locale).
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path


DEFAULT_MODEL_ID = "FunAudioLLM/Fun-CosyVoice3-0.5B-2512"
DEFAULT_LANGUAGE = "French"

# Transcript du prompt asset (carte HF, usage zero_shot canonique)
PROMPT_TEXT_ZH = "希望你以后能够做的比我还好呦。"
# CosyVoice3 exige le marqueur <|endofprompt|> dans prompt_text (llm.py:479,
# assert 151646) ; frontend_zero_shot ne l'ajoute PAS -- c'est a l'appelant.
ENDOFPROMPT = "<|endofprompt|>"
INSTRUCT_PREFIX = "You are a helpful assistant."


def _bootstrap_paths():
    """Ajoute le repo CosyVoice et Matcha-TTS au sys.path, retourne (repo, model_dir, asset_wav)."""
    p = Path(__file__).resolve()
    # Un .gitignore intermediaire (ex: GenAI/) ne doit pas arreter la remontee :
    # seuls .git (racine du worktree) ou _runtime/CosyVoice marquent la racine.
    for _ in range(10):
        if (p / ".git").exists() or (p / "_runtime" / "CosyVoice").exists():
            break
        p = p.parent
    repo_root = p
    runtime = repo_root / "_runtime"
    cv_repo = runtime / "CosyVoice"
    model_dir = runtime / "pretrained_models" / "Fun-CosyVoice3-0.5B"
    asset_wav = cv_repo / "asset" / "zero_shot_prompt.wav"
    for sp in (str(cv_repo), str(cv_repo / "third_party" / "Matcha-TTS")):
        if sp not in sys.path:
            sys.path.insert(0, sp)
    return cv_repo, model_dir, asset_wav


def load_model(model_id: str = DEFAULT_MODEL_ID, device: str = "cuda", dtype: str = "bf16"):
    """Charge AutoModel CosyVoice3 avec mesure VRAM pic."""
    import torch

    _bootstrap_paths()
    from cosyvoice.cli.cosyvoice import AutoModel

    torch_dtype = {"bf16": torch.bfloat16, "fp16": torch.float16, "fp32": torch.float32}[dtype]
    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    print(f"  [CosyVoice3] Loading {model_id} on {device} ({dtype})...")
    t0 = time.time()
    # AutoModel gere lui-meme le device du LLM (fp16/bf16 GPU supporte)
    model = AutoModel(model_dir=str(_resolve_model_dir()))
    dt = time.time() - t0
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    print(f"  [CosyVoice3] Loaded in {dt:.1f}s, VRAM peak {vram_peak_gb:.2f} GB, sr={model.sample_rate}")
    return model


def _resolve_model_dir() -> Path:
    _, model_dir, _ = _bootstrap_paths()
    if not (model_dir / "llm.pt").exists() and not (model_dir / "config.yaml").exists():
        raise FileNotFoundError(
            f"model_dir {model_dir} incomplet — lancer snapshot_download (cf env_setup/SETUP.md)"
        )
    return model_dir


def synth(
    text: str,
    out_wav: str,
    model,
    language: str = DEFAULT_LANGUAGE,
    speaker: str | None = None,
    instruct: str | None = None,
    **kwargs,
) -> dict:
    """Synthese text->wav. zero_shot par defaut ; instruct2 si instruct fourni.

    language/speaker : records (CosyVoice3 n'a pas de voix premium nommees ; la
    langue pilote par le texte et l'instruct, la voix par le prompt wav).
    """
    import torch
    import torchaudio

    _, _, asset_wav = _bootstrap_paths()
    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    t0 = time.time()

    if instruct:
        prompt_text2 = f"{INSTRUCT_PREFIX} Speak in {language}. {instruct}{ENDOFPROMPT}"
        gen = model.inference_instruct2(
            text, prompt_text2, str(asset_wav), stream=False
        )
        mode = "instruct2"
    else:
        gen = model.inference_zero_shot(
            text, PROMPT_TEXT_ZH + ENDOFPROMPT, str(asset_wav), stream=False
        )
        mode = "zero_shot"

    chunks = [j["tts_speech"] for j in gen]
    wav = torch.cat(chunks, dim=-1) if len(chunks) > 1 else chunks[0]
    dt = time.time() - t0
    sr = model.sample_rate
    duration_s = wav.shape[-1] / sr
    rtf = dt / duration_s if duration_s > 0 else float("inf")
    torchaudio.save(out_wav, wav, sr)
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    return {
        "model": DEFAULT_MODEL_ID,
        "mode": mode,
        "language": language,
        "speaker": speaker,
        "instruct": instruct,
        "prompt_wav": str(asset_wav),
        "out_wav": str(out_wav),
        "sample_rate": int(sr),
        "duration_s": float(duration_s),
        "wallclock_s": float(dt),
        "rtf": float(rtf),
        "vram_peak_gb": float(vram_peak_gb),
        "n_samples": int(wav.shape[-1]),
        "n_chunks": len(chunks),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--language", default=DEFAULT_LANGUAGE)
    p.add_argument("--instruct", default=None)
    p.add_argument("--device", default="cuda")
    p.add_argument("--dtype", default="bf16", choices=["bf16", "fp16", "fp32"])
    args = p.parse_args()
    model = load_model(device=args.device, dtype=args.dtype)
    result = synth(text=args.text, out_wav=args.out, model=model,
                   language=args.language, instruct=args.instruct)
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
