"""Client Zonos v0.1-transformer pour Phase A0 #17586 bakeoff_large.

Modèle : Zyphra/Zonos-v0.1-transformer (Apache-2.0, FR par code eSpeak
`fr-fr`, clonage de voix par embedding de référence).

Installation (env propre, règle F) — ATTENTION : le paquet PyPI `zonos` est un
placeholder squatté (0.1.0.dev0, wheel vide, sans module) ; le paquet officiel
s'installe depuis le repo GitHub Zyphra/Zonos :
    py -3.10 -m venv _runtime/venv-zonos
    _runtime/venv-zonos/Scripts/python.exe -m pip install --upgrade pip
    _runtime/venv-zonos/Scripts/python.exe -m pip install torch==2.11.0 torchaudio==2.11.0 --index-url https://download.pytorch.org/whl/cu126
    git clone --depth 1 https://github.com/Zyphra/Zonos.git _runtime/Zonos
    _runtime/venv-zonos/Scripts/python.exe -m pip install -e ./_runtime/Zonos soundfile faster-whisper

Variante TRANSFORMER (pas hybride) : la variante hybride
(`Zyphra/Zonos-v0.1-hybrid`) exige mamba-ssm + causal-conv1d (extras `compile`,
noyaux CUDA compilés, sans wheels Windows) ; la variante pure transformer est
un checkpoint officiel du même repo, sans dépendance CUDA compilée — choix de
variante documenté, pas un contournement.

Interface uniforme (cf. __init__.py) :
    load_model(device, dtype) -> model
    synth(text, out_wav, model, language='French', **kw) -> dict

    - language : 'French' (mappé vers le code eSpeak 'fr-fr' de Zonos ; les
      autres langues Zonos passent aussi par leur nom anglais)
    - speaker/instruct : non applicables à Zonos v0.1 (ignorés) — le timbre
      vient du wav de référence (clonage), la langue du code ISO.

Voix de référence : asset zh `zero_shot_prompt.wav` du repo CosyVoice du
_runtime (même convention que le client cosyvoice3 — timbre identique entre
clients du bakeoff, clonage cross-lingual zh->FR, capacité sous test).

CLI :
    python clients/zonos.py --text "..." --out <wav> [--language French] [--device cuda]
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import torch
import torchaudio


DEFAULT_MODEL_ID = "Zyphra/Zonos-v0.1-transformer"
DEFAULT_LANGUAGE = "French"

# Nom bench -> code eSpeak conditionné par Zonos (make_cond_dict language=)
_LANGUAGE_CODES = {
    "english": "en-us",
    "french": "fr-fr",
    "german": "de",
    "spanish": "es",
    "italian": "it",
    "portuguese": "pt",
    "polish": "pl",
    "dutch": "nl",
    "russian": "ru",
}


def _reference_wav() -> Path:
    """Asset de référence (voix zh) : runtime CosyVoice du worktree voisin,
    sinon _runtime local. Identique entre clients du bakeoff."""
    here = Path(__file__).resolve()
    for _ in range(10):
        if (here / "_runtime").exists():
            break
        here = here.parent
    candidates = [
        here / "_runtime" / "CosyVoice" / "asset" / "zero_shot_prompt.wav",
        here.parent / "CoursIA-17586-cosyvoice3" / "_runtime" / "CosyVoice" / "asset" / "zero_shot_prompt.wav",
        here.parent.parent / "CoursIA-17586-cosyvoice3" / "_runtime" / "CosyVoice" / "asset" / "zero_shot_prompt.wav",
    ]
    for c in candidates:
        if c.exists():
            return c
    return candidates[0]


def get_supported_languages() -> list[str]:
    return [k.capitalize() for k in _LANGUAGE_CODES]


def load_model(model_id: str = DEFAULT_MODEL_ID, device: str = "cuda", dtype: str = "bf16"):
    """Charge Zonos transformer avec mesure VRAM pic.

    Le paramètre `dtype` du banc est non applicable : `from_pretrained` force
    le backbone en bfloat16 (`.to(device, torch.bfloat16)` dans le repo) —
    accepté ici seulement pour l'interface uniforme.
    """
    from zonos.model import Zonos

    print(f"  [Zonos] Loading {model_id} on {device} (bf16, forced by loader)...")
    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    t0 = time.time()
    model = Zonos.from_pretrained(model_id, device=device)
    dt = time.time() - t0
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    print(f"  [Zonos] Loaded in {dt:.1f}s, VRAM peak {vram_peak_gb:.2f} GB")
    return model


def synth(
    text: str,
    out_wav: str,
    model,
    language: str = DEFAULT_LANGUAGE,
    speaker: str | None = None,  # non applicable Zonos (clonage par référence)
    instruct: str | None = None,  # non applicable Zonos v0.1
    **kwargs,
) -> dict:
    """Synthèse text->wav par clonage cross-lingual de l'asset de référence."""
    from zonos.conditioning import make_cond_dict

    lang_code = _LANGUAGE_CODES.get(language.strip().lower())
    if lang_code is None:
        raise ValueError(
            f"Langue {language!r} non supportée par le client zonos "
            f"(supportées : {', '.join(sorted(set(_LANGUAGE_CODES)))})"
        )

    ref_path = _reference_wav()
    if not ref_path.exists():
        raise FileNotFoundError(
            f"Voix de référence absente : {ref_path} — cloner le repo CosyVoice "
            "(git clone --recursive https://github.com/FunAudioLLM/CosyVoice.git) "
            "ou poser un wav de référence à cet emplacement."
        )
    spkref, sr = torchaudio.load(str(ref_path))
    # Speaker = embedding calculé par le modèle (make_speaker_embedding),
    # pas le wav brut — cf sample.py du repo officiel.
    spk_emb = model.make_speaker_embedding(spkref, sr)

    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    t0 = time.time()
    cond_dict = make_cond_dict(
        text=text,
        language=lang_code,
        speaker=spk_emb,
    )
    conditioning = model.prepare_conditioning(cond_dict)
    codes = model.generate(conditioning)
    wavs = model.autoencoder.decode(codes).cpu()
    dt = time.time() - t0

    wav = wavs[0]
    out_sr = int(model.autoencoder.sampling_rate)
    torchaudio.save(out_wav, wav, out_sr)
    duration_s = float(wav.shape[-1] / out_sr)
    rtf = dt / duration_s if duration_s > 0 else float("inf")
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    return {
        "model": DEFAULT_MODEL_ID,
        "language": language,
        "language_code": lang_code,
        "reference_wav": str(ref_path),
        "out_wav": str(out_wav),
        "sample_rate": out_sr,
        "duration_s": duration_s,
        "wallclock_s": float(dt),
        "rtf": float(rtf),
        "vram_peak_gb": float(vram_peak_gb),
        "n_samples": int(wav.shape[-1]),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text", required=True, help="Texte à synthétiser")
    p.add_argument("--out", required=True, help="Chemin .wav de sortie")
    p.add_argument("--language", default=DEFAULT_LANGUAGE, choices=get_supported_languages())
    p.add_argument("--model-id", default=DEFAULT_MODEL_ID)
    p.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    p.add_argument("--dtype", default="bf16", choices=["bf16", "fp16", "fp32"])
    args = p.parse_args()

    model = load_model(args.model_id, device=args.device, dtype=args.dtype)
    result = synth(text=args.text, out_wav=args.out, model=model, language=args.language)
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
