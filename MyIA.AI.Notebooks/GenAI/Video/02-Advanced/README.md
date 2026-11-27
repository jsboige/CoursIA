# 02-Advanced - Génération Vidéo Avancée

[← Video Foundation](../01-Foundation/) | [↑ Video](../README.md) | [→ Video Orchestration](../03-Orchestration/)

Ce module explore les modèles de génération vidéo de pointe : HunyuanVideo, LTX Video/LTX-2, Wan Video, SVD et CogVideoX, jusqu'à l'étude de licence d'un modèle fermé de référence (MiniMax H3).

**Dans le cadre du fil rouge pipeline vidéo pédagogique** : ce niveau fournit les modèles génératifs. [02-1](02-1-Generation-Video-Locale.ipynb) produit des vidéos haute qualité (cinématographique). [02-3](02-3-Wan-Video-Generation.ipynb) offre une génération rapide avec support multilingue. [02-4](02-4-Image-to-Video-Diffusion.ipynb) anime une image existante -- utile pour transformer un diagramme ou une illustration en séquence animée. Le duo final traite la question juridique de bout en bout : [02-6](02-6-Video-Architecture-Licensing.ipynb) établit *pourquoi* un modèle puissant (MiniMax H3) est hors d'atteinte en UE sur la voie auto-hébergée (bifurcation licence des poids ≠ ToS du service), et [02-7](02-7-Text-to-Video-Poids-Ouverts.ipynb) en est le pendant exécutable : génération texte → vidéo sur un modèle open-weights Apache-2.0 vérifié *firsthand*. Le carnet [02-8](02-8-PAN2-Modele-du-Monde-GLP.ipynb) ferme la série côté *technique* : la formalisation de PAN 2 (architecture GLP) — la thèse du modèle du monde, les cinq dimensions de design, la différence entre JEPA et GLP, et la factorisation en trois facteurs — rejouable sur CPU, les 29 B du modèle restant un paramètre d'exécution.

## Comment lire ce README

- Vous voulez **la meilleure qualité** : [02-1](02-1-Generation-Video-Locale.ipynb) (HunyuanVideo, ~18 GB) est le carnet cinématographique ; [02-5](02-5-Video-Audio-Conjoint.ipynb) ajoute la génération audio+vidéo conjointe (22B, quantification obligatoire).
- Vous voulez **du prototypage rapide** : [02-2](02-2-Generation-Video-Legere.ipynb) (LTX, pic mesuré 14,1 GB) et [02-3](02-3-Wan-Video-Generation.ipynb) (Wan, ~10 GB) — lisez aussi les prérequis GPU avant de lancer l'un ou l'autre.
- Vous voulez **animer une image existante** : [02-4](02-4-Image-to-Video-Diffusion.ipynb) (SVD, image → vidéo) est le seul carnet de ce niveau qui part d'un visuel au lieu d'un prompt.
- Vous voulez **la question juridique** : [02-6](02-6-Video-Architecture-Licensing.ipynb) (étude documentaire, CPU) puis [02-7](02-7-Text-to-Video-Poids-Ouverts.ipynb) son pendant exécutable Apache-2.0 — la paire se lit dans cet ordre.

Cette navigation par niveaux suit le principe des séries à plusieurs vitesses décrit dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Kernel | Python 3 |
| Durée estimée | ~6-8h |
| GPU requis | 10-24GB selon le carnet (voir le tableau ci-dessous) |

> Le décompte canonique des notebooks de la série réside dans `CATALOG-STATUS.json` du dépôt, pas dans cette page.

## Notebooks

| # | Notebook | Contenu | Service | VRAM | Ce qu'on y apprend |
|---|----------|---------|---------|------ |--------------------|
| 1 | [02-1-Generation-Video-Locale](02-1-Generation-Video-Locale.ipynb) | Génération Hunyuan | Local GPU | ~18GB | Générer une vidéo cinématographique et mesurer le coût VRAM (~18 GB) que la qualité impose |
| 2 | [02-2-Generation-Video-Legere](02-2-Generation-Video-Legere.ipynb) | Génération légère LTX | Local GPU | 16GB (pic mesuré : 14.1GB) | Générer rapidement sur GPU contraint, et vérifier le pic réel (14,1 GB) plutôt que la valeur annoncée |
| 3 | [02-3-Wan-Video-Generation](02-3-Wan-Video-Generation.ipynb) | Génération Wan | Local GPU | ~10GB | Une alternative rapide et multilingue pour le prototypage à ~10 GB |
| 4 | [02-4-Image-to-Video-Diffusion](02-4-Image-to-Video-Diffusion.ipynb) | SVD (Image → Vidéo) | Local GPU (diffusers) | ~10GB | Animer une image existante au lieu de partir d'un prompt — le seul carnet image → vidéo du niveau |
| 5 | [02-5-Video-Audio-Conjoint](02-5-Video-Audio-Conjoint.ipynb) | LTX-2 audio+vidéo conjoint (22B) | Local GPU | ~14-24GB (fp8-cast natif, GGUF Q4 en prod) | Générer vidéo et audio synchronisés en une passe, et quantifier pour tenir dans une carte de 24 GB |
| 6 | [02-6-Video-Architecture-Licensing](02-6-Video-Architecture-Licensing.ipynb) | Architecture et bifurcation juridique MiniMax H3 (licence poids ≠ ToS service) | Étude documentaire (CPU) | — | Lire une licence firsthand et distinguer licence des poids et ToS du service (exclusion UE de la voie auto-hébergée) |
| 7 | [02-7-Text-to-Video-Poids-Ouverts](02-7-Text-to-Video-Poids-Ouverts.ipynb) | Génération texte → vidéo CogVideoX-2b (Apache-2.0, couple discriminant Prong B) | Local GPU | ~16-20GB | Générer texte → vidéo sur poids ouverts Apache-2.0, et exécuter le couple discriminant qui prouve la valeur du moteur |
| 8 | [02-8-PAN2-Modele-du-Monde-GLP](02-8-PAN2-Modele-du-Monde-GLP.ipynb) | Formalisation de PAN 2 / GLP : thèse du modèle du monde, 5 dimensions de design, JEPA dégénéré vs GLP, factorisation `p_h . p_f . p_g` | Étude technique (CPU) | — | Formuler la these du modele du monde, distinguer un JEPA degenere d'une GLP, et poser la factorisation `p_h . p_f . p_g` |

## Prérequis

### Docker Services
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

### GPU Requirements
- **Minimum** : 10 GB VRAM pour 02-3 (Wan) et 02-4 (SVD) ; **16 GB pour le carnet 02-2** (LTX Video), pic mesuré 14.1 GB (RTX 4090, 704x480, 25 frames, bf16) — sous 16 GB, la cellule de chargement du carnet bascule en offload CPU
- **Recommandé** : 10-12 GB VRAM (SVD, Wan Video), 16-24 GB dès que 02-2 est au programme
- **Optimal** : 18+ GB VRAM (HunyuanVideo, CogVideoX-2b)

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
pip install -r requirements-comfyui.txt
```

## Progression recommandée

1. **02-1-Generation-Video-Locale** - Qualité maximale
2. **02-2-Generation-Video-Legere** - Performance/équilibre
3. **02-3-Wan-Video-Generation** - Alternative rapide
4. **02-4-Image-to-Video-Diffusion** - Animation d'images
5. **02-5-Video-Audio-Conjoint** - Vidéo + audio synchronisé (génération conjointe)
6. **02-6-Video-Architecture-Licensing** - Vérifier une licence *firsthand* : pourquoi H3 est hors d'atteinte en UE auto-hébergé (et ce que la voie service ouvre)
7. **02-7-Text-to-Video-Poids-Ouverts** - Le pendant exécutable du 02-6 : texte → vidéo sur poids ouverts Apache-2.0
8. **02-8-PAN2-Modele-du-Monde-GLP** - La technique d'un modèle du monde : GLP, ses cinq dimensions, ses trois niveaux de prédiction, et ce que le décodeur change (CPU, sans GPU)

## Technologies clés

### HunyuanVideo (Tencent)
- **Spécialité** : Vidéo haute qualité, réaliste
- **Durée** : Jusqu'à plusieurs secondes
- **VRAM** : ~18GB

### LTX Video (Lightweight)
- **Spécialité** : Rapidité, efficacité
- **Durée** : Courtes vidéos
- **VRAM** : 16 GB ou plus (pic mesuré : 14.1 GB sur RTX 4090, 704x480, 25 frames, bf16)

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

### PAN 2 / GLP (modèle du monde, étude technique)
- **Spécialité** : Modèle du monde **généraliste** (IFM/MBZUAI) — il simule l'issue d'une action avant qu'elle ne soit jouée, pour un **raisonnement simulatif** ; sortie = vidéo jusqu'à 20 s
- **Architecture** : GLP — bottleneck génératif + backbone LLM + prédicteur de next-embedding par diffusion ; factorisation `p_PAN(o'|o,a) = p_h . p_f . p_g`
- **Distinction clé** : face à JEPA (distribution **dégénérée**, masse de Dirac), le **décodeur** de GLP ferme la boucle et sert de **diagnostic** : il révèle une représentation trop perdante
- **VRAM** : — (le carnet est CPU ; le modèle, lui, est un backbone MMDiT de 29 B servi sur 4×B300 / 8×H200)
- **Licence** : Apache-2.0 (model card `IFM/PAN2`) — le carnet n'exécute pas le modèle, il en rejoue la formalisation

## Comparatif

| Modèle | Qualité | Vitesse | VRAM | Cas d'usage |
|--------|---------|---------|------|-------------|
| HunyuanVideo | Exceptionnelle | Lent | ~18GB | Production premium |
| LTX Video | Bonne | Rapide | 16GB (pic mesuré : 14.1GB) | Prototypage rapide |
| Wan Video | Bonne | Moyen | ~10GB | Animation fluide |
| SVD | Variable | Moyen | ~10GB | Animation d'images |
| CogVideoX-2b | Bonne | Moyen | ~16-20GB | Texte → vidéo open weights (Apache-2.0) |

MiniMax H3 n'apparaît pas dans ce comparatif : il n'est **pas exécutable** sur la voie auto-hébergée UE (exclusion territoriale de sa licence communautaire) — son étude complète vit dans [02-6](02-6-Video-Architecture-Licensing.ipynb).

## Approfondissements

- **L'axe qualité / vitesse / contrainte** : 02-1 (qualité), 02-2 et 02-3 (vitesse sous contrainte VRAM), 02-5 (audio+vidéo conjoint quantifié) forment les trois points de la décision de moteur ; le comparatif ci-dessus en donne les chiffres, les carnets les mesurent.
- **La paire juridique se lit dans l'ordre** : [02-6](02-6-Video-Architecture-Licensing.ipynb) établit l'exclusion territoriale *firsthand*, [02-7](02-7-Text-to-Video-Poids-Ouverts.ipynb) exécute la voie qui reste ouverte (Apache-2.0) — un raisonnement complet, pas deux carnets voisins.
- **En amont et en aval** : les primitives vidéo (découpe, extraction audio, concaténation) vivent dans [01-Foundation](../01-Foundation/README.md) ; l'orchestration de ces générateurs dans un pipeline se poursuit dans [03-Orchestration](../03-Orchestration/README.md).

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Architecture ComfyUI](../../../../docs/genai/genai-services.md)
