# GenAI - Commandes de Switch Rapide pour le Cours

## État des Services (actuel)

```
forge-turbo    : UP   (GPU 1 - RTX 3090, port 17861)
comfyui-qwen   : DOWN (GPU 0 - RTX 3080 Ti, port 8188)
comfyui-video  : DOWN (GPU 0 - RTX 3080 Ti, port 8189)
```

## Commandes Rapides

### Vérifier l'état
```bash
python scripts/genai-stack/genai.py docker status
python scripts/genai-stack/genai.py gpu
```

### Profils GPU par Série

#### Série Image (01-1 à 04-3)
```bash
# Démarrer les services Image
python scripts/genai-stack/genai.py docker start comfyui-qwen forge-turbo

# Vérifier
python scripts/genai-stack/genai.py docker status
```

#### Série Audio - API Only (01-1, 01-2, 01-3, 03-3)
```bash
# Pas de GPU requis, services inchangés
# Les notebooks utilisent OpenAI API
```

#### Série Audio - GPU Local (01-4, 01-5, 02-1 à 02-4)
```bash
# Libérer GPU 0 pour les kernels
python scripts/genai-stack/genai.py docker stop comfyui-qwen comfyui-video

# forge-turbo peut rester actif sur GPU 1
```

#### Série Video - API Only (01-1, 01-2, 04-3)
```bash
# Pas de GPU requis
# Les notebooks utilisent OpenAI API
```

#### Série Video - GPU Léger (01-4, 02-2, 02-3, 02-4)
```bash
# Libérer GPU 0 et/ou GPU 1
python scripts/genai-stack/genai.py docker stop comfyui-qwen comfyui-video

# LTX, Wan, SVD fonctionnent sur RTX 3080 Ti (8-10GB)
```

#### Série Video - GPU Lourd (01-3, 01-5, 02-1)
```bash
# Arrêter TOUS les services
python scripts/genai-stack/genai.py docker stop all

# HunyuanVideo, Qwen-VL, AnimateDiff nécessitent 18-24GB (RTX 3090)
```

#### Série Video - ComfyUI (03-3)
```bash
# Démarrer ComfyUI Video
python scripts/genai-stack/genai.py docker start comfyui-video

# Arrêter les autres services GPU 0
python scripts/genai-stack/genai.py docker stop comfyui-qwen
```

## Matrice de Compatibilité GPU

| Série/Notebook | GPU 0 (3080 Ti 16GB) | GPU 1 (3090 24GB) | Services requis |
|----------------|----------------------|-------------------|-----------------|
| Image API      | -                    | -                 | Aucun           |
| Image ComfyUI  | comfyui-qwen         | forge-turbo       | comfyui-qwen    |
| Audio API      | -                    | -                 | Aucun           |
| Audio GPU      | kernel (10GB)        | forge-turbo       | Aucun           |
| Video API      | -                    | -                 | Aucun           |
| Video Léger    | kernel ou libre      | kernel (8GB)      | Aucun           |
| Video Lourd    | -                    | kernel (18-24GB)  | Aucun           |
| Video ComfyUI  | comfyui-video        | -                 | comfyui-video   |

## En Cas de Problème

### Reset complet
```bash
python scripts/genai-stack/genai.py docker stop all
python scripts/genai-stack/genai.py gpu
# Vérifier que VRAM est libérée
```

### Redémarrer un service
```bash
python scripts/genai-stack/genai.py docker restart forge-turbo
```

### Vérifier les logs
```bash
docker logs forge-turbo --tail 50
docker logs comfyui-qwen --tail 50
docker logs comfyui-video --tail 50
```

## Dépendances Manquantes (à installer si besoin)

```bash
# Audio
pip install kokoro-onnx       # 01-5 Kokoro TTS
pip install audiocraft        # 02-3 MusicGen
pip install chatterbox-tts    # 02-1 Chatterbox
pip install TTS               # 02-2 XTTS
pip install demucs            # 02-4 Demucs

# Video
pip install moviepy           # 04-4 Audio-Video Sync
pip install realesrgan        # 01-4 ESRGAN (optionnel, fallback OK)

# System
# ffmpeg requis pour pydub/moviepy
```
