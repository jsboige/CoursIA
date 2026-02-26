# Session Étudiants Avancés - GenAI Series

## Contexte

- **Durée** : 3h
- **Date** : 26/02/2026
- **Public** : Étudiants ayant terminé leur projet (PR faite)
- **Objectif** : Explorer la série GenAI complète avec challenges bonus

## État des Projets (au 25/02)

| Groupe | Statut | PR |
|--------|--------|-----|
| RobinVaz | Projet Review | Merged |
| devinjayasuriya | Projet Review | Merged |
| NacimAfrikou | Extracteur Documents | Merged |

**3 groupes prêts** pour la session avancée.

---

## Infrastructure GenAI - Vue Complète

### GPUs Disponibles

| GPU | Modèle | VRAM | Services actifs |
|-----|--------|------|-----------------|
| GPU 0 | RTX 3080 Ti Laptop | 16 GB | whisper-webui (local) |
| GPU 1 | RTX 3090 | 24 GB | forge-turbo, vllm-zimage |

### Services Docker - État Actuel

| Service | Container | URL Locale | URL Distante | GPU | VRAM | Status |
|---------|-----------|------------|--------------|-----|------|--------|
| forge-turbo | UP | `http://localhost:17861` | `https://turbo.stable-diffusion-webui-forge.myia.io` | GPU 1 (3090) | ~8 GB | OK |
| vllm-zimage | UP | `http://localhost:8001` | `https://z-image.myia.io` | GPU 1 (3090) | ~15 GB | OK |
| whisper-webui | Local | `http://localhost:36540` | `https://whisper-webui.myia.io` | GPU 0 (3080 Ti) | ~10 GB | OK |
| comfyui-qwen | UP | `http://localhost:8188` | `https://qwen-image-edit.myia.io` | GPU 1 (3090) | ~18 GB | OK - GGUF Q4_K_M workflow validé |

### Modèles Locaux (sans container)

#### Audio
| Modèle | Type | GPU | VRAM | Notebook |
|--------|------|-----|------|----------|
| Whisper large-v3 | STT | GPU 0 | ~10 GB | Audio/01-4 |
| Kokoro TTS | TTS | GPU 0 | ~2 GB | Audio/01-5 |
| Chatterbox TTS | TTS | GPU 0 | ~8 GB | Audio/02-1 |
| XTTS v2 | TTS | GPU 0 | ~6 GB | Audio/02-2 |
| MusicGen Large | Music | GPU 0 | ~10 GB | Audio/02-3 |
| Demucs v4 | Separation | GPU 0 | ~4 GB | Audio/02-4 |

#### Video
| Modèle | Type | GPU | VRAM | Notebook |
|--------|------|-----|------|----------|
| Qwen2.5-VL-7B | VQA | GPU 1 | ~18 GB | Video/01-3 |
| Real-ESRGAN | Upscale | GPU 0 | ~4 GB | Video/01-4 |
| RIFE | Interpolation | GPU 0 | ~4 GB | Video/01-4 |
| AnimateDiff | Animation | GPU 1 | ~12 GB | Video/01-5 |
| HunyuanVideo | Generation | GPU 1 | ~18 GB | Video/02-1 |
| LTX-Video | Generation | GPU 0 | ~8 GB | Video/02-2 |
| Wan 2.1/2.2 | Generation | GPU 1 | ~10 GB | Video/02-3 |
| SVD | Generation | GPU 1 | ~10 GB | Video/02-4 |

---

## Stratégie GPU - Switch par Domaine

### Profils GPU

| Profil | GPU 0 (3080 Ti) | GPU 1 (3090) | Services |
|--------|-----------------|--------------|----------|
| `audio_api` | Libre | forge-turbo | OpenAI TTS/STT |
| `audio_local_gpu` | Whisper local | forge-turbo | Audio local |
| `video_local_light` | Libre | forge-turbo + zimage | Video légère |
| `video_local_heavy` | Tout arrêter | Qwen2.5-VL | Video lourde |
| `video_comfyui` | Libre | ComfyUI Qwen | Edition image |

### Commandes de Switch

```bash
# Appliquer un profil GPU
python scripts/genai-stack/genai.py gpu profile apply <profil>

# Vérifier l'état GPU
python scripts/genai-stack/genai.py gpu

# Démarrer/arrêter un service
python scripts/genai-stack/genai.py docker start <service>
python scripts/genai-stack/genai.py docker stop <service>
```

---

## Séquence d'Exécution Autonome

### Ordre Optimisé par GPU

**Batch 1 : API-only (pas de GPU)**
- Texte/1_OpenAI_Intro.ipynb
- Texte/2_PromptEngineering.ipynb
- Texte/3_Structured_Outputs.ipynb
- Texte/4_Function_Calling.ipynb
- Texte/5_RAG_Modern.ipynb
- Audio/01-1-OpenAI-TTS-Intro.ipynb
- Audio/01-2-OpenAI-Whisper-STT.ipynb

**Batch 2 : GPU léger (forge-turbo actif)**
- Image/01-1-OpenAI-DALL-E-3.ipynb
- Image/01-4-Stable-Diffusion-Local.ipynb
- Video/01-1-Video-Operations-Basics.ipynb
- Video/01-2-GPT-5-Video-Understanding.ipynb

**Batch 3 : Audio GPU (Whisper local)**
- Profil: `audio_local_gpu`
- Audio/01-3-Basic-Audio-Operations.ipynb
- Audio/01-4-Local-Whisper.ipynb
- Audio/01-5-Kokoro-TTS.ipynb
- Audio/02-3-MusicGen-Generation.ipynb

**Batch 4 : Video GPU lourde**
- Profil: `video_local_heavy`
- Video/01-3-Qwen-Video-Understanding.ipynb
- Video/02-1-HunyuanVideo.ipynb

### Workflow d'Exécution

```python
# Pour chaque notebook:
1. Vérifier profil GPU actuel
2. Si changement nécessaire: appliquer nouveau profil
3. Exécuter notebook avec Papermill
4. Valider outputs (erreurs, warnings)
5. Extraire images/vidéos générées
6. Valider avec sk-agent vision
7. Corriger si nécessaire
8. Commit par batch
```

---

## Séquence pour Étudiants Avancés

### Phase 1 : Setup et Texte (45 min)
*Profil: `audio_api` - Pas de GPU requis*

1. `00-1-Environment-Setup.ipynb` - Vérifier .env
2. `Texte/1_OpenAI_Intro.ipynb` - Bases API
3. `Texte/2_PromptEngineering.ipynb` - Techniques de prompt

**Challenge #1** : Prompt en cascade pour histoire (0.5 pt)
- Générer un personnage JSON, puis un conflit, puis une résolution
- Pattern : mémoire conversationnelle + few-shot

---

### Phase 2 : Texte Avancé (45 min)
*Profil: `audio_api` - Pas de GPU requis*

1. `Texte/3_Structured_Outputs.ipynb` - JSON structuré
2. `Texte/4_Function_Calling.ipynb` - Fonctions

**Challenge #2** : Assistant de planification multi-outils (0.5 pt)
- Définir 3 outils : événements, temps de trajet, restaurant
- Pattern : `run_conversation()` avec tools

---

### Phase 3 : Audio API (45 min)
*Profil: `audio_api` - GPU libre pour Whisper local*

1. `Audio/01-1-OpenAI-TTS-Intro.ipynb` - Text-to-Speech

**Challenge #8** : Narration multi-voix (0.5 pt)
- Créer un dialogue avec 2+ voix différentes

2. `Audio/01-2-OpenAI-Whisper-STT.ipynb` - Speech-to-Text

**Challenge #9** : Sous-titrage automatique (0.5 pt)
- Générer sous-titres SRT synchronisés

3. `Audio/01-3-Basic-Audio-Operations.ipynb` - Opérations audio

**Challenge #3** : Analyse et transformation conditionnelle (0.5 pt)
- Analyser audio avec librosa, appliquer transformations avec pydub

---

### Phase 4 : Image et Video (60 min)
*Profil: `video_local_light` - forge-turbo actif*

1. `Image/01-1-OpenAI-DALL-E-3.ipynb` - Génération DALL-E

**Challenge #4** : Icône d'application (0.5 pt)
- Générer une icône style "app store"

2. `Video/01-1-Video-Operations-Basics.ipynb` - Opérations vidéo

**Challenge #7** : Slideshow vidéo (0.5 pt)
- Créer une vidéo avec 5 frames message

3. `Video/01-2-GPT-5-Video-Understanding.ipynb` - Analyse vidéo

**Challenge #10** : Analyse de vidéo personnalisée (0.5 pt)
- Analyser une vidéo avec GPT-5

---

### Phase 5 : RAG et Musique (optionnel, si temps)
*Profil: `audio_local_gpu` - Whisper/MusicGen local*

1. `Texte/5_RAG_Modern.ipynb` - Retrieval Augmented Generation

**Challenge #5** : Mini FAQ engine avec RAG (0.5 pt)
- Créer une base Q/R et implémenter la recherche

2. `Audio/02-3-MusicGen-Generation.ipynb` - Génération musicale

**Challenge #6** : Musique pour scène vidéo (0.5 pt)
- Générer 2 versions avec paramètres différents

---

## Système de Points

| Action | Points |
|--------|-------|
| Compléter Challenge #1 | 0.5 pts |
| Compléter Challenge #2 | 0.5 pts |
| Compléter Challenge #3 | 0.5 pts |
| Compléter Challenge #4 | 0.5 pts |
| Compléter Challenge #5 | 0.5 pts |
| Compléter Challenge #6 | 0.5 pts |
| Compléter Challenge #7 | 0.5 pts |
| Compléter Challenge #8 | 0.5 pts |
| Compléter Challenge #9 | 0.5 pts |
| Compléter Challenge #10 | 0.5 pts |
| Faire une PR avec solutions | +0.5 pts |
| Aider un autre étudiant | +0.2 pts/interaction |

**Récompenses (bonus sur note /20)** :
- 3+ challenges : +0.5 pt
- 5+ challenges : +1.0 pt
- 7+ challenges : +1.5 pts (max)
- 10 challenges + aide + PR : +2.0 pts (max théorique)

---

## Déroulement Optimal (3h)

| Temps | Activité | Notebooks | Profil GPU |
|------|----------|----------|------------|
| 0-5 min | Introduction et setup | Environment | - |
| 5-50 min | Phase 1 : Texte | 3 notebooks | audio_api |
| 50-95 min | Phase 2 : Texte avancé | 2 notebooks | audio_api |
| 95-140 min | Phase 3 : Audio API | 3 notebooks | audio_api |
| 140-200 min | Phase 4 : Image/Video | 3 notebooks | video_local_light |
| 200-180 min | Phase 5 : RAG/Musique | 2 notebooks | audio_local_gpu |

---

## Pour l'enseignant

### Services Docker - Commandes Rapides

```bash
# Statut complet
python scripts/genai-stack/genai.py docker status

# Démarrer tout
python scripts/genai-stack/genai.py docker start all

# Arrêter tout
python scripts/genai-stack/genai.py docker stop all

# Tester endpoints
python scripts/genai-stack/genai.py docker test --remote
```

### URLs de Production (IIS Reverse Proxy)

| Service | URL | Auth |
|---------|-----|------|
| Forge Turbo | `https://turbo.stable-diffusion-webui-forge.myia.io` | Basic (admin/changeme) |
| Whisper WebUI | `https://whisper-webui.myia.io` | Aucune |
| Z-Image vLLM | `https://z-image.myia.io` | Aucune |
| Qwen Image Edit | `https://qwen-image-edit.myia.io` | Bearer Token |

### Points d'attention

- **Tous les challenges principaux fonctionnent avec OpenAI API uniquement**
- MusicGen utilise le GPU local (pas de container)
- Vérifier que chaque étudiant a bien configuré son `.env`
- Les challenges doivent être soumis via PR sur le fork du repo
- Prévoir des sessions de debug pour les groupes en difficulté

---

## Liste complète des Challenges

| # | Notebook | Challenge | Compétences | GPU |
|---|----------|-----------|------------|-----|
| 1 | `Texte/2_PromptEngineering.ipynb` | Prompt en cascade | Few-shot, mémoire | Non |
| 2 | `Texte/4_Function_Calling.ipynb` | Assistant planification | Tools, boucle agentique | Non |
| 3 | `Audio/01-3-Basic-Audio-Operations.ipynb` | Analyse + transformation | librosa, pydub | Non |
| 4 | `Image/01-1-OpenAI-DALL-E-3.ipynb` | Icône application | DALL-E 3 prompting | Non |
| 5 | `Texte/5_RAG_Modern.ipynb` | Mini FAQ engine | Embeddings, recherche vectorielle | Non |
| 6 | `Audio/02-3-MusicGen-Generation.ipynb` | Musique scène vidéo | MusicGen, paramètres | Oui (~10GB) |
| 7 | `Video/01-1-Video-Operations-Basics.ipynb` | Slideshow vidéo | PIL, imageio | Non |
| 8 | `Audio/01-1-OpenAI-TTS-Intro.ipynb` | Narration multi-voix | TTS, voices | Non |
| 9 | `Audio/01-2-OpenAI-Whisper-STT.ipynb` | Sous-titrage | Whisper, timestamps | Non |
| 10 | `Video/01-2-GPT-5-Video-Understanding.ipynb` | Analyse vidéo | GPT-5 multimodal | Non |

---

## Validation Autonome par Claude

### Utilisation de sk-agent

```python
# Validation d'image
mcp__sk-agent__call_agent(
    agent="vision-local",
    attachment=str(image_path),
    prompt="Rate this image 1-10 for quality. Identify artifacts."
)

# Analyse d'erreur
mcp__sk-agent__call_agent(
    agent="analyst",
    prompt=f"Analyse cette erreur: {error_message}"
)
```

### Commandes de Validation

```bash
# Valider la stack GenAI
/validate-genai all --local

# Exécuter un notebook
/execute-notebook <path> --save

# Vérifier les notebooks
/verify-notebooks GenAI --quick
```

---

## Checklist Pré-Session

- [x] Vérifier .env des étudiants (clés API)
- [x] Confirmer que les notebooks sont bien exécutables
- [x] Préparer grille de notation
- [x] Créer fork template pour PRs challenges
- [x] Planifier sessions de debug individuelles
- [x] Télécharger modèles Qwen Image Edit GGUF Q4_K_M
- [x] Tester workflow ComfyUI Qwen GGUF
- [ ] Valider tous les challenges avec sk-agent

---

## Workflow ComfyUI Qwen Image Edit - GGUF Q4_K_M

### Modèles (dans container comfyui-qwen)

| Composant | Fichier | Taille | Dossier |
|-----------|---------|--------|---------|
| Transformer | `qwen-image-edit-2511-Q4_K_M.gguf` | 13 GB | `/models/unet/` |
| Text Encoder | `Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf` | 4.4 GB | `/models/clip/` |
| VAE | `qwen_image_vae.safetensors` | 243 MB | `/models/vae/` |

**Total VRAM**: ~18 GB (fits RTX 3090 24GB)

### Workflow JSON (testé et validé)

```json
{
  "1": {"class_type": "UnetLoaderGGUF", "inputs": {"unet_name": "qwen-image-edit-2511-Q4_K_M.gguf"}},
  "2": {"class_type": "CLIPLoaderGGUF", "inputs": {"clip_name": "Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf", "type": "qwen_image"}},
  "3": {"class_type": "VAELoader", "inputs": {"vae_name": "qwen_image_vae.safetensors"}},
  "4": {"class_type": "QwenVLEmptyLatent", "inputs": {"width": 1024, "height": 1024, "batch_size": 1}},
  "5": {"class_type": "TextEncodeQwenImageEdit", "inputs": {"clip": ["2", 0], "prompt": "...", "vae": ["3", 0]}},
  "6": {"class_type": "ConditioningZeroOut", "inputs": {"conditioning": ["5", 0]}},
  "7": {"class_type": "ModelSamplingAuraFlow", "inputs": {"model": ["1", 0], "shift": 3.0}},
  "8": {"class_type": "CFGNorm", "inputs": {"model": ["7", 0], "strength": 1.0}},
  "9": {"class_type": "KSampler", "inputs": {"model": ["8", 0], "seed": 12345, "steps": 20, "cfg": 1.0, "sampler_name": "euler", "scheduler": "beta", "positive": ["5", 0], "negative": ["6", 0], "latent_image": ["4", 0], "denoise": 1.0}},
  "10": {"class_type": "VAEDecode", "inputs": {"samples": ["9", 0], "vae": ["3", 0]}},
  "11": {"class_type": "SaveImage", "inputs": {"filename_prefix": "qwen_gguf", "images": ["10", 0]}}
}
```

### Paramètres critiques

- **scheduler**: `beta` (obligatoire pour Qwen)
- **cfg**: `1.0` (CFGNorm gère le guidance)
- **shift**: `3.0` (ModelSamplingAuraFlow)
- **type CLIP**: `qwen_image`

### Authentification API

```bash
TOKEN='$2b$12$I7V9gQuddnQh12jZCfO4v.RFxI24tRpZ4Y3ymnuGridhmyA3O7ekC'
curl -H "Authorization: Bearer $TOKEN" http://localhost:8188/prompt -d @workflow.json
```

---

## Services Exposés pour Étudiants (myia.io)

### Services Actuellement Exposés

| Service | URL | Port Local | Usage | Auth |
|---------|-----|------------|-------|------|
| Forge Turbo | `https://turbo.stable-diffusion-webui-forge.myia.io` | 17861 | SDXL Lightning | Basic (admin/changeme) |
| Qwen Image Edit | `https://qwen-image-edit.myia.io` | 8188 | ComfyUI GGUF | Bearer Token |
| Whisper WebUI | `https://whisper-webui.myia.io` | 36540 | STT/TTS | Aucune |
| Z-Image vLLM | `https://z-image.myia.io` | 8001 | Text-to-Image | Aucune |

### Services Additionnels Suggérés

Pour les étudiants sans machine suffisante, les services suivants pourraient être exposés :

| Service | URL Proposée | Port | GPU | Intérêt |
|---------|--------------|------|-----|---------|
| OpenAI-Compatible API | `api.genai.myia.io` | 8000 | GPU 0 | Remplace OpenAI API |
| Kokoro TTS | `tts.genai.myia.io` | 5000 | GPU 0 | Synthèse vocale locale |
| MusicGen | `music.genai.myia.io` | 7860 | GPU 0 | Génération musicale |

### Pattern de Configuration IIS

1. **Créer le dossier** : `D:\Production\<domaine>.myia.io\`
2. **Créer web.config** :
```xml
<configuration>
    <system.webServer>
        <webSocket enabled="true" />
        <proxy><preserveHostHeader>true</preserveHostHeader></proxy>
        <rewrite>
            <rules>
                <rule name="ReverseProxyInboundRule" stopProcessing="true">
                    <match url="(.*)" />
                    <action type="Rewrite" url="http://localhost:<PORT>/{R:1}" />
                    <serverVariables>
                        <set name="HTTP_SEC_WEBSOCKET_EXTENSIONS" value="nodata" />
                    </serverVariables>
                </rule>
            </rules>
        </rewrite>
    </system.webServer>
</configuration>
```
3. **Créer le site IIS** : `New-Website -Name "<domaine>.myia.io" -PhysicalPath "D:\Production\<domaine>.myia.io" -Port 80 -HostHeader "<domaine>.myia.io"`
4. **Certificat SSL** : `D:\Production\win-acme.v2.2.9.1701.x64.pluggable\wacs.exe`

### Note Importante

Les services API (OpenAI, Claude) nécessitent que chaque étudiant ait sa propre clé API. Les services exposés sur myia.io sont des **alternatives locales** pour les modèles hébergés sur la machine de l'enseignant.
