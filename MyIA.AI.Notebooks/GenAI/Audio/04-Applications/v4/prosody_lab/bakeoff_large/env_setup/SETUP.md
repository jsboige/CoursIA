# Setup env Phase A0 #17586 bakeoff_large

Tell c.c.c.d.F strict fondateur (règle globale) : **RÉPARER, ne JAMAIS contourner**. L'env Python 3.13 système de la machine po-2023 a `transformers==5.12.1` (largement utilisé par le dépôt) qui est **incompatible** avec `qwen-tts==0.1.1` (qui exige `transformers<5`). Downgrader transformers casserait une grande partie des notebooks existants.

**Solution** : venv Python 3.12 dédié `qwen3tts`, isolé du système.

## Prérequis natifs

### sox 14.4.2 (Windows portable)

`qwen-tts` exige `sox` au runtime. Pas dans choco par défaut. Install manuelle :

```bash
mkdir -p /c/ProgramData/sox-portable
curl -L -o /c/ProgramData/sox-portable/sox.zip https://sourceforge.net/projects/sox/files/sox/14.4.2/sox-14.4.2-win32.zip/download
cd /c/ProgramData/sox-portable && powershell -NoProfile -Command "Expand-Archive -Path sox.zip -DestinationPath . -Force"
# PATH local pour cette session :
export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
sox --version  # SoX v14.4.2
```

Pour rendre sox permanent : ajouter `C:\ProgramData\sox-portable\sox-14.4.2` au PATH système via `sysdm.cpl` → Environment Variables → Path (action user one-time, RECOVERABLE-USER-HAND).

## Création du venv Python 3.12

```bash
cd D:/Dev/CoursIA-17586
py -3.12 -m venv _runtime/venv-qwen3tts --prompt qwen3tts
_runtime/venv-qwen3tts/Scripts/python.exe -m pip install --upgrade pip
```

## Installation des dépendances

### torch CUDA (CUDA 12.6)

```bash
_runtime/venv-qwen3tts/Scripts/python.exe -m pip install torch==2.14.0 torchaudio==2.14.0 --index-url https://download.pytorch.org/whl/cu126
```

Vérif :

```bash
_runtime/venv-qwen3tts/Scripts/python.exe -c "import torch; print(torch.__version__, torch.cuda.is_available())"
# 2.14.0+cu126 True
```

### qwen-tts 0.1.1 + dépendances

```bash
export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
_runtime/venv-qwen3tts/Scripts/python.exe -m pip install qwen-tts
# Installe : accelerate, einops, gradio, librosa, onnxruntime, soundfile, sox, torchaudio, transformers==4.57.3
```

Vérif import :

```bash
export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
_runtime/venv-qwen3tts/Scripts/python.exe -c "import qwen_tts; print('OK', qwen_tts.Qwen3TTSModel)"
# OK <class 'qwen_tts.inference.qwen3_tts_model.Qwen3TTSModel'>
```

## GPU cible

- **RTX 3090** (24 GB VRAM) — cible primaire, ~15 GB libre mesuré
- RTX 3080 Ti Laptop GPU (16 GB) — fallback si RTX 3090 occupée

Tell c.c.c.d.767-L1 strict fondateur : **zero-dep-manifeste ≠ zero-dep-réel**. Le test ci-dessus (import + GPU dispo) est OBLIGATOIRE avant tout client.py.

## Zonos (client `zonos.py`, venv `venv-zonos`)

Slot 3 shortlist — Kyutai/Zonos-v0.1-transformer (Apache-2.0, FR par code ISO `fr`).
Chemin officiel (règle F + Prong A) : **paquet PyPI `zonos`** du repo Kyutai/Zonos.

**Variante transformer, pas hybride** : `Kyutai/Zonos` (hybride) exige `mamba-ssm` +
`causal-conv1d` (noyaux CUDA compilés, pas de wheels Windows) ;
`Kyutai/Zonos-v0.1-transformer` est un checkpoint officiel du même repo sans
dépendance compilée — choix de variante documenté, pas un contournement.

```bash
# 1. venv Python 3.10
cd D:/Dev/CoursIA-17586-zonos
py -3.10 -m venv _runtime/venv-zonos
_runtime/venv-zonos/Scripts/python.exe -m pip install --upgrade pip

# 2. torch cu126 — PIE 2.11.0 : l'index cu126 ne porte torchaudio que jusqu'a
#    2.11.0 (torchaudio==2.14.0 introuvable, mesure 29/09) ; 2.11.0 >> exigence Zonos
_runtime/venv-zonos/Scripts/python.exe -m pip install torch==2.11.0 torchaudio==2.11.0 --index-url https://download.pytorch.org/whl/cu126

# 3. zonos + jambe WER du banc
_runtime/venv-zonos/Scripts/python.exe -m pip install zonos soundfile faster-whisper
```

Verif pre-banc (767-L1 zero-dep-manifeste != zero-dep-reel) :

```bash
_runtime/venv-zonos/Scripts/python.exe -c "import torch; from zonos.model import Zonos; from zonos.conditioning import make_cond_dict; print('OK', torch.__version__, torch.cuda.is_available())"
```

Banc :

```bash
_runtime/venv-zonos/Scripts/python.exe bakeoff_large/banc_phase_a0.py \
    --client zonos --language French \
    --out-root <GDrive>/run-<id>/A0-bakeoff/zonos
```

**Voix de reference (clonage)** : asset zh `zero_shot_prompt.wav` du repo
CosyVoice du worktree voisin `CoursIA-17586-cosyvoice3/_runtime/CosyVoice/asset/`
— meme timbre que le client cosyvoice3 (comparabilite bakeoff, cross-lingual
zh->FR). Le client le resolve par candidats (`clients/zonos.py::_reference_wav`) ;
sans lui : `git clone --recursive https://github.com/FunAudioLLM/CosyVoice.git`
dans `_runtime/`. Zonos n'a NI speaker nomme NI instruct NL (v0.1) — les kwargs
`speaker`/`instruct` du banc sont ignores.
