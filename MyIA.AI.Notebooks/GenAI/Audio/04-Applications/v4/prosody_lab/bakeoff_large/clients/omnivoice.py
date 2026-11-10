"""Client OmniVoice (k2-fsa) pour la mission #21568 / Phase A0 #17586.

Modèle : k2-fsa/OmniVoice. Licence : le CODE est Apache-2.0, les POIDS sont
CC-BY-NC — carte HF, verbatim : « Our code is released under the Apache 2.0
License. The pre-trained model is licensed under the CC-BY-NC due to constraints
from its training data (e.g., Emilia). » Le tokenizer audio embarqué
(audio_tokenizer/) relève en outre de la Boson Higgs Audio 2 Community License
(dérivée Llama 3 : accord à embarquer, mention « Built with Higgs Materials »,
seuil de 100 000 utilisateurs actifs). Une redistribution commerciale n'est donc
pas acquise par la seule licence du code.

Poids du checkpoint : model.safetensors 2450 Mo + audio_tokenizer/model.safetensors
806 Mo + tokenizer.json 11 Mo = 3,27 Go (F32, 313 tenseurs, ~0,61 B paramètres ;
chargé en bf16/fp16 il tient en ~2 Go de VRAM).

Trois modes, tous servis par le même `model.generate()` :
    - clonage  : `ref_audio` (+ `ref_text` ; sans lui, OmniVoice transcrit la
                 référence par Whisper — on passe toujours `ref_text` pour
                 éviter de charger l'ASR) ;
    - design   : `instruct` — attributs libres (genre, âge, hauteur, accent) ;
                 entraîné zh+en seulement, généralise mal sur les autres langues ;
    - auto     : aucun prompt, la voix est choisie par le modèle.

Langues : `docs/languages.md` du dépôt k2-fsa porte le français à sa ligne 189
(`| 180 | French | fr | fra | 23675.32 |`) — la langue se nomme ou se code, et
`_resolve_language` accepte les deux formes.

Installation (env propre, règle F) — convention des clients frères : `_runtime`
à la RACINE du dépôt (`.gitignore` racine ligne `/_runtime/`) :

    py -3.13 -m venv _runtime/venv-omnivoice
    _runtime/venv-omnivoice/Scripts/python.exe -m pip install -U pip
    _runtime/venv-omnivoice/Scripts/python.exe -m pip install "git+https://github.com/k2-fsa/OmniVoice.git"
    _runtime/venv-omnivoice/Scripts/python.exe -c "from huggingface_hub import snapshot_download; \
        snapshot_download('k2-fsa/OmniVoice', local_dir='_runtime/models/OmniVoice')"

Poids et venv peuvent vivre ailleurs : `OMNIVOICE_MODEL_DIR` force le dossier
du checkpoint (le mode `local_dir` est préféré au cache HF — le contrôle de
propriété du checkpoint reste ainsi lisible sur disque).

Interface uniforme (cf. `clients/__init__.py`) :
    load_model(model_id, device, dtype) -> model
    synth(text, out_wav, model, language='French', speaker=None, instruct=None,
          ref_audio=None, ref_text=None, **kw) -> dict

CLI (depuis bakeoff_large/, forme module — l'invocation directe
`python clients/omnivoice.py` casse sur une collision de nom : sys.path[0]
vaut alors clients/, et `from omnivoice import OmniVoice` résolu par
load_model trouve le présent fichier au lieu du paquet, défaut de famille
partagé avec clients/zonos.py) :
    python -m clients.omnivoice --text "..." --out <wav> [--language French]
        [--instruct "..."] [--ref-audio ref.wav --ref-text "..."]
        [--device cuda] [--dtype fp16] [--num-step 32] [--speed 1.0]
"""
from __future__ import annotations

import argparse
import json
import os
import time
from pathlib import Path

import numpy as np
import soundfile as sf


DEFAULT_MODEL_ID = "k2-fsa/OmniVoice"
DEFAULT_LANGUAGE = "French"

# Sortie du modèle : liste de np.ndarray mono à 24 kHz (README, section
# « Voice Cloning »). Aucun `sample_rate` n'est retourné par generate().
SAMPLE_RATE = 24000

# Tags non-verbaux documentés (README k2-fsa, « Non-Verbal & Pronunciation
# Control »). Les tags `question-*`/`surprise-*` sont des particules zh/en ;
# seuls `[laughter]` et `[sigh]` sont des candidats pour une narration FR.
NONVERBAL_TAGS = (
    "[laughter]",
    "[sigh]",
    "[confirmation-en]",
    "[question-en]",
    "[question-ah]",
    "[question-oh]",
    "[question-ei]",
    "[question-yi]",
    "[surprise-ah]",
    "[surprise-oh]",
    "[surprise-wa]",
    "[surprise-yo]",
    "[dissatisfaction-hnn]",
)


def _dtype_map(dtype: str):
    import torch

    return {
        "fp16": torch.float16,
        "half": torch.float16,
        "bf16": torch.bfloat16,
        "fp32": torch.float32,
        "float": torch.float32,
    }[dtype]


def _repo_root() -> Path:
    """Racine du worktree : premier ancêtre portant `.git` ou `_runtime`."""
    p = Path(__file__).resolve()
    for _ in range(10):
        if (p / ".git").exists() or (p / "_runtime").exists():
            break
        p = p.parent
    return p


def _resolve_model_dir() -> Path | None:
    """Dossier local du checkpoint, ou None pour laisser `from_pretrained`
    résoudre l'identifiant HF (cache `~/.cache/huggingface`)."""
    forced = os.environ.get("OMNIVOICE_MODEL_DIR")
    if forced:
        return Path(forced)
    root = _repo_root()
    for cand in (root / "_runtime" / "models" / "OmniVoice",
                 root / ".tmp" / "models" / "OmniVoice"):
        if cand.exists():
            return cand
    return None


def load_model(model_id: str = DEFAULT_MODEL_ID, device: str = "cuda", dtype: str = "fp16"):
    """Charge OmniVoice et mesure la VRAM pic du chargement."""
    import torch
    from omnivoice import OmniVoice

    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    target = _resolve_model_dir()
    source = str(target) if target is not None else model_id
    device_map = device if device != "cpu" else "cpu"
    print(f"  [OmniVoice] Loading {source} on {device_map} ({dtype})...")
    t0 = time.time()
    model = OmniVoice.from_pretrained(source, device_map=device_map, dtype=_dtype_map(dtype))
    dt = time.time() - t0
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    print(f"  [OmniVoice] Loaded in {dt:.1f}s, VRAM peak {vram_peak_gb:.2f} GB, sr={SAMPLE_RATE}")
    return model


def synth(
    text: str,
    out_wav: str,
    model,
    language: str = DEFAULT_LANGUAGE,
    speaker: str | None = None,
    instruct: str | None = None,
    ref_audio: str | None = None,
    ref_text: str | None = None,
    voice_clone_prompt=None,
    num_step: int | None = None,
    speed: float | None = None,
    normalize_text: bool = False,
    seed: int | None = None,
    **kwargs,
) -> dict:
    """Synthèse text->wav. Clonage si `ref_audio`/`voice_clone_prompt`,
    design si `instruct`, voix auto sinon.

    `language` est transmis à `generate()` : le modèle documente qu'un id
    (`fr`) ou un nom (`French`) améliore légèrement la génération, et
    `_resolve_language` accepte les deux (646 entrées dans `LANG_NAME_TO_ID`,
    vérifié). `speaker` reste un record : OmniVoice n'a pas de voix premium
    nommées — le timbre vient du clonage ou de l'`instruct`.

    `seed` : OmniVoice **n'expose aucune graine** (ni paramètre, ni champ de
    `OmniVoiceGenerationConfig` — inspecté dans le paquet installé). On pose
    donc la graine torch globale avant l'appel : la génération devient
    reproductible pour peu que l'échantillonnage tire de ce RNG, sans prétendre
    à une graine native. Le champ est écrit tel quel dans le run de banc.
    """
    import torch

    if seed is not None:
        torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.reset_peak_memory_stats()
    t0 = time.time()

    gen_kwargs: dict = {"language": language} if language else {}
    if num_step is not None:
        gen_kwargs["num_step"] = num_step
    if speed is not None:
        gen_kwargs["speed"] = speed
    if normalize_text:
        gen_kwargs["normalize_text"] = True

    if voice_clone_prompt is not None:
        mode = "clone_prompt"
        audio = model.generate(text=text, voice_clone_prompt=voice_clone_prompt, **gen_kwargs)
    elif ref_audio is not None:
        mode = "clone"
        audio = model.generate(text=text, ref_audio=ref_audio, ref_text=ref_text, **gen_kwargs)
    elif instruct:
        mode = "design"
        audio = model.generate(text=text, instruct=instruct, **gen_kwargs)
    else:
        mode = "auto"
        audio = model.generate(text=text, **gen_kwargs)

    dt = time.time() - t0
    wav = audio[0] if isinstance(audio, (list, tuple)) else audio
    wav = np.asarray(wav, dtype=np.float32).reshape(-1)
    duration_s = len(wav) / SAMPLE_RATE
    rtf = dt / duration_s if duration_s > 0 else float("inf")
    sf.write(out_wav, wav, SAMPLE_RATE)
    vram_peak_gb = torch.cuda.max_memory_allocated() / 1024**3 if torch.cuda.is_available() else 0.0
    return {
        "model": DEFAULT_MODEL_ID,
        "mode": mode,
        "language": language,
        "speaker": speaker,
        "instruct": instruct,
        "ref_audio": str(ref_audio) if ref_audio is not None else None,
        "seed": seed,
        "out_wav": str(out_wav),
        "sample_rate": int(SAMPLE_RATE),
        "duration_s": float(duration_s),
        "wallclock_s": float(dt),
        "rtf": float(rtf),
        "vram_peak_gb": float(vram_peak_gb),
        "n_samples": int(len(wav)),
        "n_chunks": len(audio) if isinstance(audio, (list, tuple)) else 1,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--text", required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--language", default=DEFAULT_LANGUAGE)
    p.add_argument("--instruct", default=None)
    p.add_argument("--ref-audio", default=None)
    p.add_argument("--ref-text", default=None)
    p.add_argument("--device", default="cuda")
    p.add_argument("--dtype", default="fp16", choices=["fp16", "bf16", "fp32"])
    p.add_argument("--num-step", type=int, default=None)
    p.add_argument("--speed", type=float, default=None)
    p.add_argument("--seed", type=int, default=None, help="graine torch globale (aucune graine native OmniVoice)")
    args = p.parse_args()
    model = load_model(device=args.device, dtype=args.dtype)
    result = synth(
        text=args.text,
        out_wav=args.out,
        model=model,
        language=args.language,
        instruct=args.instruct,
        ref_audio=args.ref_audio,
        ref_text=args.ref_text,
        num_step=args.num_step,
        speed=args.speed,
        seed=args.seed,
    )
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()