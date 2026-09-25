"""Client Qwen3-TTS-12Hz-1.7B-CustomVoice pour Phase A0 #17586 bakeoff_large.

Modèle : Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice (Apache-2.0, FR natif, 9 voix premium,
style contrôlable via instructions NL).

Installation (env propre, règle F) :
    py -3.12 -m venv _runtime/venv-qwen3tts
    _runtime/venv-qwen3tts/Scripts/python.exe -m pip install qwen-tts
    _runtime/venv-qwen3tts/Scripts/python.exe -m pip install torch==2.14.0 torchaudio==2.14.0 --index-url https://download.pytorch.org/whl/cu126

Dépendance native :
    sox (https://sourceforge.net/projects/sox/files/sox/14.4.2/) — extrait dans
    C:/ProgramData/sox-portable/sox-14.4.2/ et ajouté au PATH (cf. _runtime/SETUP.md).

Interface uniforme (cf. __init__.py) :
    synth(text, out_wav, **kwargs) -> dict :
        text    : str — texte à synthétiser
        out_wav : str — chemin absolu .wav de sortie (24 kHz mono)
        language: str — 'French' (défaut), autres 9 langues supportées
        speaker : str — voix premium (cf. get_supported_speakers()), défaut 'serena' (snake_case, voir get_supported_speakers())
        instruct: str — instruction NL de style (ex: "voix posée, débit lent, ton narratif")
        kwargs  : generation kwargs HF Transformers (max_new_tokens, top_p, temperature, etc.)
        Returns : dict avec sample_rate, duration_s, rtf, vram_peak_gb, n_frames

CLI :
    python clients/qwen3_tts_customvoice.py --text "..." --out <wav> [--language French] [--speaker serena] [--instruct "..."] [--device cuda]

Tell c.c.c.d.sota-not-workaround Prong A : organ-first = qwen-tts 0.1.1 (paquet PyPI officiel Qwen).
Pas de réimplémentation locale du wrapper transformers.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

# qwen_tts >= 0.1.1
import torch


DEFAULT_MODEL_ID = "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice"
DEFAULT_SPEAKER = "serena"  # Tell c.c.c.d.G.1 ★★★★ — vérif first-hand c.818, snake_case lowercase
DEFAULT_LANGUAGE = "French"
SAMPLE_RATE = 24000  # Qwen3-TTS 12 Hz output upsample to 24 kHz


def get_supported_speakers() -> list[str]:
    """Retourne la liste des voix premium supportées par le CustomVoice 1.7B.

    Tell c.c.c.d.G.1 ★★★★ — vérif first-hand c.818 16:42Z :
    model._validate_speakers(['Chelsie']) → ValueError "Unsupported speakers: ['Chelsie'].
    Supported: ['aiden', 'dylan', 'eric', 'ono_anna', 'ryan', 'serena', 'sohee', 'uncle_fu', 'vivian']"
    La doc README affichait des Capitalized names ('Chelsie', 'Ethan', etc.) qui ne sont PAS
    les speaker_id réels du modèle 1.7B CustomVoice. Noms en snake_case/lowercase.
    """
    return [
        "aiden", "dylan", "eric", "ono_anna",
        "ryan", "serena", "sohee", "uncle_fu", "vivian",
    ]


def get_supported_languages() -> list[str]:
    """10 langues + variantes dialectales CN."""
    return [
        "Chinese", "English", "Japanese", "Korean", "German",
        "French", "Russian", "Portuguese", "Spanish", "Italian",
    ]


def load_model(model_id: str = DEFAULT_MODEL_ID, device: str = "cuda", dtype: str = "bf16"):
    """Charge Qwen3-TTS CustomVoice avec mesure VRAM pic."""
    from qwen_tts import Qwen3TTSModel
    torch_dtype = {"bf16": torch.bfloat16, "fp16": torch.float16, "fp32": torch.float32}[dtype]
    print(f"  [Qwen3-TTS] Loading {model_id} on {device} ({dtype})...")
    t0 = time.time()
    model = Qwen3TTSModel.from_pretrained(
        model_id,
        device_map=device,
        dtype=torch_dtype,
    )
    dt = time.time() - t0
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    print(f"  [Qwen3-TTS] Loaded in {dt:.1f}s, VRAM peak {vram_peak_gb:.2f} GB")
    return model


def synth(
    text: str,
    out_wav: str,
    model,
    language: str = DEFAULT_LANGUAGE,
    speaker: str = DEFAULT_SPEAKER,
    instruct: str | None = None,
    **kwargs,
) -> dict:
    """Synthèse text→wav via generate_custom_voice. Retourne dict avec sample_rate, duration_s, rtf, vram_peak_gb."""
    import soundfile as sf

    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    t0 = time.time()
    # qwen_tts 0.1.1 API: model.generate_custom_voice(text=, language=, speaker=, instruct=, **hf_kwargs)
    wavs, sr = model.generate_custom_voice(
        text=text,
        language=language,
        speaker=speaker,
        instruct=instruct,
        **kwargs,
    )
    dt = time.time() - t0
    # wavs est typiquement une List[ndarray] (batch) — single input → [ndarray]
    wav = wavs[0] if isinstance(wavs, list) else wavs
    duration_s = len(wav) / sr
    rtf = dt / duration_s if duration_s > 0 else float("inf")
    sf.write(out_wav, wav, sr)
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    return {
        "model": DEFAULT_MODEL_ID,
        "language": language,
        "speaker": speaker,
        "instruct": instruct,
        "out_wav": str(out_wav),
        "sample_rate": int(sr),
        "duration_s": float(duration_s),
        "wallclock_s": float(dt),
        "rtf": float(rtf),
        "vram_peak_gb": float(vram_peak_gb),
        "n_samples": int(len(wav)),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text", required=True, help="Texte à synthétiser")
    p.add_argument("--out", required=True, help="Chemin .wav de sortie")
    p.add_argument("--language", default=DEFAULT_LANGUAGE, choices=get_supported_languages())
    p.add_argument("--speaker", default=DEFAULT_SPEAKER, help="Voix premium (parmi get_supported_speakers())")
    p.add_argument("--instruct", default=None, help="Instruction NL de style")
    p.add_argument("--model-id", default=DEFAULT_MODEL_ID)
    p.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    p.add_argument("--dtype", default="bf16", choices=["bf16", "fp16", "fp32"])
    p.add_argument("--max-new-tokens", type=int, default=None)
    p.add_argument("--top-p", type=float, default=None)
    p.add_argument("--temperature", type=float, default=None)
    args = p.parse_args()

    model = load_model(args.model_id, device=args.device, dtype=args.dtype)

    hf_kwargs = {}
    if args.max_new_tokens is not None:
        hf_kwargs["max_new_tokens"] = args.max_new_tokens
    if args.top_p is not None:
        hf_kwargs["top_p"] = args.top_p
    if args.temperature is not None:
        hf_kwargs["temperature"] = args.temperature

    result = synth(
        text=args.text,
        out_wav=args.out,
        model=model,
        language=args.language,
        speaker=args.speaker,
        instruct=args.instruct,
        **hf_kwargs,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
