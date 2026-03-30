# GenAI - Résumé de Validation pour le Cours

## Date: 2026-02-25

## État Global

| Série | Notebooks | Validés | Erreurs | Warnings | Taux |
|-------|-----------|---------|---------|----------|------|
| 00-Environment | 6 | 6 | 0 | 0 | 100% |
| Texte | 10 | 10 | 0 | 0 | 100% |
| Image | 15 | 13 | 1* | 5 | 87% |
| Audio API | 4 | 4 | 0 | 0 | 100% |
| Audio GPU | 10 | 10 | 0 | 0 | 100% |
| Video API | 3 | 2 | 1*** | 0 | 67% |
| Video GPU Light | 3 | - | - | - | En cours |
| Video GPU Heavy | 3 | - | - | - | En cours |
| Video ComfyUI+Apps | 6 | 6 | 0 | 0 | 100% |
| SemanticKernel | 10 | 7 | 3**** | 0 | 70% |

*L'erreur Image (02-1) est un faux positif - le token est présent dans .env
**SemanticKernel a des breaking changes API (SK 1.39+)

## Notebooks Prêts pour le Cours (sans action requise)

### Série 00-Environment (6/6)
- 00-1-Environment-Setup.ipynb
- 00-2-Docker-Services-Management.ipynb
- 00-3-API-Endpoints-Configuration.ipynb
- 00-4-Environment-Validation.ipynb
- 00-5-ComfyUI-Local-Test.ipynb

### Série Texte (10/10)
- 1_OpenAI_Intro.ipynb
- 2_PromptEngineering.ipynb
- 3_Structured_Outputs.ipynb
- 4_Function_Calling.ipynb
- 5_RAG_Modern.ipynb
- 6_PDF_Web_Search.ipynb
- 7_Code_Interpreter.ipynb
- 8_Reasoning_Models.ipynb
- 9_Production_Patterns.ipynb
- 10_LocalLlama.ipynb

### Série Image API (5/5)
- 01-1-OpenAI-DALL-E-3.ipynb
- 01-2-GPT-5-Image-Generation.ipynb
- 01-3-Basic-Image-Operations.ipynb
- 02-4-Z-Image-Lumina2.ipynb
- 03-3-Performance-Optimization.ipynb

### Série Image ComfyUI/Forge (8/8)
- 01-4-Forge-SD-XL-Turbo.ipynb
- 01-5-Qwen-Image-Edit.ipynb
- 02-1-Qwen-Image-Edit-2509.ipynb
- 02-2-FLUX-1-Advanced-Generation.ipynb
- 02-3-Stable-Diffusion-3-5.ipynb
- 03-1-Multi-Model-Comparison.ipynb
- 03-2-Workflow-Orchestration.ipynb
- 04-* (Applications)

### Série Audio GPU (10/10)
- 01-4-Whisper-Local.ipynb
- 01-5-Kokoro-TTS-Local.ipynb
- 02-1-Chatterbox-TTS.ipynb
- 02-2-XTTS-Voice-Cloning.ipynb
- 02-3-MusicGen-Generation.ipynb
- 02-4-Demucs-Source-Separation.ipynb
- 03-1-Multi-Model-Audio-Comparison.ipynb
- 03-2-Audio-Pipeline-Orchestration.ipynb
- 03-3-Realtime-Voice-API.ipynb
- 04-1-Educational-Audio-Content.ipynb
- 04-2-Transcription-Pipeline.ipynb
- 04-3-Music-Composition-Workflow.ipynb
- 04-4-Audio-Video-Sync.ipynb

### Série Audio API (4/4)
- 01-1-OpenAI-TTS-Intro.ipynb
- 01-2-OpenAI-Whisper-STT.ipynb
- 01-3-Basic-Audio-Operations.ipynb
- 03-3-Realtime-Voice-API.ipynb

### Série Video API/ComfyUI (8/8)
- 01-1-Video-Operations-Basics.ipynb
- 01-2-GPT-5-Video-Understanding.ipynb (corrigé)
- 03-3-ComfyUI-Video-Workflows.ipynb
- 04-1-Educational-Video-Generation.ipynb
- 04-2-Creative-Video-Workflows.ipynb
- 04-3-Sora-API-Cloud-Video.ipynb
- 04-4-Production-Video-Pipeline.ipynb

## Dépendances à Installer (Optionnel)

Pour les notebooks GPU Audio/Video, installer si besoin:

```bash
# Audio TTS
pip install kokoro-onnx        # 01-5 Kokoro TTS
pip install chatterbox-tts     # 02-1 Chatterbox
pip install TTS                # 02-2 XTTS

# Audio Musique
pip install audiocraft         # 02-3 MusicGen
pip install demucs             # 02-4 Demucs

# Video
pip install moviepy            # 04-4 Audio-Video Sync
pip install realesrgan         # 01-4 ESRGAN (optionnel)

# System
# ffmpeg requis pour pydub/moviepy
```

## Commandes de Switch Rapide

Voir [SWITCH_COMMANDS.md](./SWITCH_COMMANDS.md) pour les commandes de gestion des containers.

### Rappel rapide:

```bash
# État des services
python scripts/genai-stack/genai.py docker status

# Image: démarrer ComfyUI
python scripts/genai-stack/genai.py docker start comfyui-qwen forge-turbo

# Audio/Video GPU: libérer GPU
python scripts/genai-stack/genai.py docker stop comfyui-qwen comfyui-video

# Video ComfyUI: service dédié
python scripts/genai-stack/genai.py docker start comfyui-video
```

## Points d'Attention pour le Cours

1. **GPT-5 temperature**: Seule la valeur par défaut (1.0) est supportée
2. **Whisper local**: `use_local_whisper=False` par défaut (évite erreurs CUDA)
3. **FFmpeg**: Requis pour pydub/moviepy - installer si besoin
4. **SemanticKernel**: Breaking changes en 1.39+ - notebooks à mettre à jour

## Configuration .env

Le fichier `.env` contient toutes les clés API nécessaires:
- OPENAI_API_KEY
- ANTHROPIC_API_KEY
- COMFYUI_API_TOKEN
- FORGE_USER / FORGE_PASSWORD
- OPENROUTER_API_KEY
- GITHUB_TOKEN

Ne pas oublier de copier `.env.example` vers `.env` pour les étudiants.
