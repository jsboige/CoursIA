# 02-Advanced - Génération Vidéo Avancée

[← Video Foundation](../01-Foundation/) | [↑ Video](../README.md) | [→ Video Orchestration](../03-Orchestration/)

Ce module explore les modèles de génération vidéo de pointe : HunyuanVideo, LTX Video/LTX-2, Wan Video, SVD et CogVideoX, jusqu'à l'étude de licence d'un modèle fermé de référence (MiniMax H3).

**Dans le cadre du fil rouge pipeline vidéo pédagogique** : ce niveau fournit les modèles génératifs. [02-1](02-1-HunyuanVideo-Generation.ipynb) produit des vidéos haute qualité (cinématographique). [02-3](02-3-Wan-Video-Generation.ipynb) offre une génération rapide avec support multilingue. [02-4](02-4-SVD-Image-to-Video.ipynb) anime une image existante -- utile pour transformer un diagramme ou une illustration en séquence animée. Le duo final traite la question juridique de bout en bout : [02-6](02-6-MiniMax-H3-Architecture-Licensing.ipynb) établit *pourquoi* un modèle puissant (MiniMax H3) est hors d'atteinte en UE sur la voie auto-hébergée (bifurcation licence des poids ≠ ToS du service), et [02-7](02-7-CogVideoX-Text-to-Video.ipynb) en est le pendant exécutable : génération texte → vidéo sur un modèle open-weights Apache-2.0 vérifié *firsthand*.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Kernel | Python 3 |
| Durée estimée | ~6-8h |
| GPU requis | 8-24GB |

> Le décompte canonique des notebooks de la série réside dans `CATALOG-STATUS.json` du dépôt, pas dans cette page.

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [02-1-HunyuanVideo-Generation](02-1-HunyuanVideo-Generation.ipynb) | Génération Hunyuan | Local GPU | ~18GB |
| 2 | [02-2-LTX-Video-Lightweight](02-2-LTX-Video-Lightweight.ipynb) | Génération légère LTX | Local GPU | ~8GB |
| 3 | [02-3-Wan-Video-Generation](02-3-Wan-Video-Generation.ipynb) | Génération Wan | Local GPU | ~10GB |
| 4 | [02-4-SVD-Image-to-Video](02-4-SVD-Image-to-Video.ipynb) | SVD (Image → Vidéo) | ComfyUI | ~10GB |
| 5 | [02-5-LTX2-Audiovisual](02-5-LTX2-Audiovisual.ipynb) | LTX-2 audio+vidéo conjoint (22B) | Local GPU | ~14-24GB (fp8-cast natif, GGUF Q4 en prod) |
| 6 | [02-6-MiniMax-H3-Architecture-Licensing](02-6-MiniMax-H3-Architecture-Licensing.ipynb) | Architecture et bifurcation juridique MiniMax H3 (licence poids ≠ ToS service) | Étude documentaire (CPU) | — |
| 7 | [02-7-CogVideoX-Text-to-Video](02-7-CogVideoX-Text-to-Video.ipynb) | Génération texte → vidéo CogVideoX-2b (Apache-2.0, couple discriminant Prong B) | Local GPU | ~16-20GB |

## Prérequis

### Docker Services
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

### GPU Requirements
- **Minimum** : 8 GB VRAM (LTX Video)
- **Recommandé** : 10-12 GB VRAM (SVD, Wan Video)
- **Optimal** : 18+ GB VRAM (HunyuanVideo, CogVideoX-2b)

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
pip install -r requirements-comfyui.txt
```

## Progression recommandée

1. **02-1-HunyuanVideo-Generation** - Qualité maximale
2. **02-2-LTX-Video-Lightweight** - Performance/équilibre
3. **02-3-Wan-Video-Generation** - Alternative rapide
4. **02-4-SVD-Image-to-Video** - Animation d'images
5. **02-5-LTX2-Audiovisual** - Vidéo + audio synchronisé (génération conjointe)
6. **02-6-MiniMax-H3-Architecture-Licensing** - Vérifier une licence *firsthand* : pourquoi H3 est hors d'atteinte en UE auto-hébergé (et ce que la voie service ouvre)
7. **02-7-CogVideoX-Text-to-Video** - Le pendant exécutable du 02-6 : texte → vidéo sur poids ouverts Apache-2.0

## Technologies clés

### HunyuanVideo (Tencent)
- **Spécialité** : Vidéo haute qualité, réaliste
- **Durée** : Jusqu'à plusieurs secondes
- **VRAM** : ~18GB

### LTX Video (Lightweight)
- **Spécialité** : Rapidité, efficacité
- **Durée** : Courtes vidéos
- **VRAM** : ~8GB

### Wan Video
- **Spécialité** : Animation, mouvement fluide
- **Durée** : Courts clips
- **VRAM** : ~10GB

### SVD (Stable Video Diffusion)
- **Spécialité** : Image → Vidéo
- **Durée** : Courtes animations
- **VRAM** : ~10GB

### LTX-2 (Lightricks, audiovisuel conjoint)
- **Spécialité** : Génération **vidéo + audio synchronisés** en une passe (premier DiT audio-video fondationnel)
- **Paramètres** : 22B (quantization obligatoire : `fp8-cast` natif borderline sur 24 GB, GGUF Q4 en production ~14 GB)
- **VRAM** : ~16-24GB
- **Licence** : LTX-2 Community (non-OSI, seuil commercial)

### MiniMax H3 (Hailuo 3.0, étude documentaire)
- **Spécialité** : Modèle fermé de référence (« Sora at home »), étudié sans exécution : architecture (composants du dépôt officiel, dont le codec `FL2VA`), capacités annoncées, matrice de décision face aux alternatives
- **Juridique** : **Bifurcation fondamentale** — la *Community License* des **poids** exclut explicitement l'UE (usage, hébergement et Outputs) → INTRINSIC pour l'auto-hébergement UE ; les *Terms of Service* du **service** hébergé sont un second instrument, sans exclusion UE (lus *firsthand*)
- **Verdict SOTA** : INTRINSIC (voie auto-hébergée UE) + voie service cloud ouverte
- **VRAM** : — (aucune génération locale ; vérificateur de juridiction et sélecteur de modèle en CPU)

### CogVideoX-2b (THUDM, open weights)
- **Spécialité** : Génération texte → vidéo (6 s @ 8 fps) sur pipeline `diffusers` ; structure 3D VAE + transformer temporel
- **VRAM** : ~16-20GB
- **Licence** : Apache-2.0 — vérifiée *firsthand* dans le notebook (pas d'Excluded Territory ni de clause Outputs)
- **Prong B** : couple discriminant exécuté pour rendre visible ce que le moteur apporte au-delà d'une suite de bas niveau

## Comparatif

| Modèle | Qualité | Vitesse | VRAM | Cas d'usage |
|--------|---------|---------|------|-------------|
| HunyuanVideo | Exceptionnelle | Lent | ~18GB | Production premium |
| LTX Video | Bonne | Rapide | ~8GB | Prototypage rapide |
| Wan Video | Bonne | Moyen | ~10GB | Animation fluide |
| SVD | Variable | Moyen | ~10GB | Animation d'images |
| CogVideoX-2b | Bonne | Moyen | ~16-20GB | Texte → vidéo open weights (Apache-2.0) |

MiniMax H3 n'apparaît pas dans ce comparatif : il n'est **pas exécutable** sur la voie auto-hébergée UE (exclusion territoriale de sa licence communautaire) — son étude complète vit dans [02-6](02-6-MiniMax-H3-Architecture-Licensing.ipynb).

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Architecture ComfyUI](../../../../docs/genai/genai-services.md)
