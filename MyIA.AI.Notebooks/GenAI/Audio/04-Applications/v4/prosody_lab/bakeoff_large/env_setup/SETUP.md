# Setup env Phase A0 #17586 bakeoff_large

Tell c.c.c.d.F strict fondateur (règle globale) : **RÉPARER, ne JAMAIS contourner**. L'env Python 3.13 système de la machine po-2023 a `transformers==5.12.1` (largement utilisé par le dépôt) qui est **incompatible** avec `qwen-tts==0.1.1` (qui exige `transformers<5`). Downgrader transformers casserait une grande partie des notebooks existants.

**Solution** : venv Python 3.12 dédié `qwen3tts`, isolé du système.

## Prérequis natifs

### sox 14.4.2 (Windows portable)

`qwen-tts` exige `sox` au runtime. Pas dans choco par défaut. Install manuelle :

```bash
mkdir -p /c/ProgramData/sox-portable
curl -L -o /c/ProgramData/sox-portable/sox.zip "https://sourceforge.net/projects/sox/files/sox/14.4.2/sox-14.4.2-win32.zip/download"
cd /c/ProgramData/sox-portable && powershell -NoProfile -Command "Expand-Archive -Path sox.zip -DestinationPath . -Force"
# PATH local pour cette session :
export PATH="/c/ProgramData/sox-portable/sox-14.4.2:$PATH"
sox --version  # SoX v14.4.2
```

Pour rendre sox permanent : ajouter `C:\ProgramData\sox-portable\sox-14.4.2` au PATH système via `sysdm.cpl` → Environment Variables → Path (action user one-time, RECOVERABLE-USER-HAND).

### espeak-ng 1.52.0 (Zonos)

`zonos.conditioning.phonemize` exige le binaire `espeak-ng` au runtime.
**Scoop (userspace, sans admin)** — la voie retenue sur po-2023 :

```bash
# une fois par machine (userspace, pas d'elevation) :
powershell -NoProfile -Command "irm get.scoop.sh -OutFile \"$env:TEMP\install-scoop.ps1\"; & \"$env:TEMP\install-scoop.ps1\" -ScoopDir 'C:\ProgramData\scoop-user'"
C:\ProgramData\scoop-user\shims\scoop.cmd install espeak-ng
```

Variables d'env requises pour le client Zonos (session ou shell) :

```bash
export PATH="/c/ProgramData/scoop-user/apps/espeak-ng/current:$PATH"
export PHONEMIZER_ESPEAK_LIBRARY="C:\\ProgramData\\scoop-user\\apps\\espeak-ng\\current\\libespeak-ng.dll"
export PHONEMIZER_ESPEAK_DATA_PATH="C:\\ProgramData\\scoop-user\\apps\\espeak-ng\\current\\espeak-ng-data"
```

Vérif :

```bash
"/c/ProgramData/scoop-user/apps/espeak-ng/current/espeak-ng.exe" --version
# eSpeak NG text-to-speech: 1.52.0  Data at: C:\ProgramData\scoop-user\apps\espeak-ng\current\espeak-ng-data
```

PIE : le MSI officiel exige l'admin (erreur 1925 en non-élevé) et l'extraction
CAB manuelle produit des DLLs corrompues (access violation). Scoop fait les
deux correctement en userspace.

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

## CosyVoice3 (client `cosyvoice3.py`, venv `venv-cosyvoice3`)

Slot 1 shortlist — FunAudioLLM/Fun-CosyVoice3-0.5B-2512 (Apache-2.0, FR natif).
Chemin officiel carte HF (regle F + Prong A) : **repo package**, pas transformers brut.

```bash
# 1. venv Python 3.10 (carte : py3.10 ; transformers pince 4.51.3 par requirements)
cd D:/Dev/CoursIA-17586-cosyvoice3
py -3.10 -m venv _runtime/venv-cosyvoice3
_runtime/venv-cosyvoice3/Scripts/python.exe -m pip install --upgrade pip

# 2. repo + submodule (Matcha-TTS)
cd _runtime
git clone --recursive https://github.com/FunAudioLLM/CosyVoice.git

# 3. requirements (torch 2.3.1 cu121 ; deepspeed/tensorrt sont linux-only par marqueurs)
_runtime/venv-cosyvoice3/Scripts/python.exe -m pip install -r CosyVoice/requirements.txt

# 4. complement banc : WER faster-whisper (absent des requirements CosyVoice)
_runtime/venv-cosyvoice3/Scripts/python.exe -m pip install faster-whisper

# 5. modeles (~1-2 GB)
_runtime/venv-cosyvoice3/Scripts/python.exe -c "from huggingface_hub import snapshot_download; snapshot_download('FunAudioLLM/Fun-CosyVoice3-0.5B-2512', local_dir=r'pretrained_models/Fun-CosyVoice3-0.5B'); snapshot_download('FunAudioLLM/CosyVoice-ttsfrd', local_dir=r'pretrained_models/CosyVoice-ttsfrd')"
# ttsfrd (wheels linux cp310) reste NON installe : fallback wetext automatique (carte : "not necessary")
```

## Zonos (client `zonos.py`, venv `venv-zonos`)

Slot 3 shortlist — Zyphra/Zonos-v0.1-transformer (Apache-2.0, FR par code eSpeak `fr-fr`).

**PIE — PyPI `zonos` est un placeholder squatté** (0.1.0.dev0, wheel vide,
Home-page `github.com/yourusername/zonos`, Auteur "Your Name") : `pip install zonos`
rend rc=0 sans livrer aucun module `zonos` (mesuré 29/09). Le paquet officiel
vient du repo GitHub **Zyphra/Zonos** (install éditable — règle F + Prong A).

**Variante transformer, pas hybride** : `Zyphra/Zonos-v0.1-hybrid` exige
`mamba-ssm` + `causal-conv1d` (extras `compile` du pyproject : noyaux CUDA
compilés, pas de wheels Windows) ; `Zyphra/Zonos-v0.1-transformer` est un
checkpoint officiel du même repo sans dépendance compilée — choix de variante
documenté, pas un contournement.

```bash
# 1. venv Python 3.10
cd D:/Dev/CoursIA-17586-zonos
py -3.10 -m venv _runtime/venv-zonos
_runtime/venv-zonos/Scripts/python.exe -m pip install --upgrade pip

# 2. torch cu126 — PIE 2.11.0 : l'index cu126 ne porte torchaudio que jusqu'a
#    2.11.0 (torchaudio==2.14.0 introuvable, mesure 29/09) ; 2.11.0 >> exigence Zonos (>=2.5.1)
_runtime/venv-zonos/Scripts/python.exe -m pip install torch==2.11.0 torchaudio==2.11.0 --index-url https://download.pytorch.org/whl/cu126

# 3. zonos officiel (repo, PAS PyPI) + jambe WER du banc
git clone --depth 1 https://github.com/Zyphra/Zonos.git _runtime/Zonos
_runtime/venv-zonos/Scripts/python.exe -m pip install -e ./_runtime/Zonos soundfile faster-whisper
```

Verif pre-banc (767-L1 zero-dep-manifeste != zero-dep-reel) :

```bash
_runtime/venv-cosyvoice3/Scripts/python.exe -c "import sys; sys.path[:0]=[r'_runtime/CosyVoice', r'_runtime/CosyVoice/third_party/Matcha-TTS']; from cosyvoice.cli.cosyvoice import AutoModel; import faster_whisper, torch; print('OK', torch.__version__, torch.cuda.is_available())"
_runtime/venv-zonos/Scripts/python.exe -c "import torch; from zonos.model import Zonos; from zonos.conditioning import make_cond_dict; print('OK', torch.__version__, torch.cuda.is_available())"
```

Banc (cf. banc_phase_a0.py) :

```bash
_runtime/venv-cosyvoice3/Scripts/python.exe bakeoff_large/banc_phase_a0.py \
    --client cosyvoice3 --language French \
    --out-root <GDrive>/run-<id>/A0-bakeoff/cosyvoice3
# variante instruct2 : --instruct "voix posee, debit lent, ton narratif"

_runtime/venv-zonos/Scripts/python.exe bakeoff_large/banc_phase_a0.py \
    --client zonos --language French \
    --out-root <GDrive>/run-<id>/A0-bakeoff/zonos
```

Prompt vocal par defaut (CosyVoice3) : asset repo `asset/zero_shot_prompt.wav`
(voix zh, transcript carte) -> clone cross-lingual zero-shot FR, capacite sous
test, reproductible.

**Voix de reference (clonage, Zonos)** : asset zh `zero_shot_prompt.wav` du repo
CosyVoice du worktree voisin `CoursIA-17586-cosyvoice3/_runtime/CosyVoice/asset/`
— meme timbre que le client cosyvoice3 (comparabilite bakeoff, cross-lingual
zh->FR). Le client le resolve par candidats (`clients/zonos.py::_reference_wav`) ;
sans lui : `git clone --recursive https://github.com/FunAudioLLM/CosyVoice.git`
dans `_runtime/`. Zonos n'a NI speaker nomme NI instruct NL (v0.1) — les kwargs
`speaker`/`instruct` du banc sont ignores.

## Pieges constates au premier banc (29/09, run-20260929-1851)

1. **`pkg_resources` meurt APRES requirements** : `requirements.txt` remonte
   `setuptools` a 84.x (supprime `pkg_resources`), casse `cosyvoice.flow.flow_matching`.
   Re-pinner **apres** l'etape 3 : `pip install "setuptools<81"` (reparé 80.10.2).
   L'openai-whisper du meme requirements exige de toute facon
   `setuptools<81` + `wheel` + `--no-build-isolation` (chaine sdist connue).
2. **CosyVoice3 exige `<|endofprompt|>` dans `prompt_text`**, y compris en
   `inference_zero_shot` (`cosyvoice/llm/llm.py:479`, assert token 151646) ;
   `frontend_zero_shot` ne l'ajoute PAS — c'est a l'appelant. Le client
   `clients/cosyvoice3.py` l'appende (`ENDOFPROMPT`).
3. **Jamais d'arret de remontee sur `.gitignore` intermediaire** (ex.
   `GenAI/.gitignore`) dans un bootstrap de racine : le venv du banc vit a la
   racine du worktree (`_runtime/`), pas sous `GenAI/`.
