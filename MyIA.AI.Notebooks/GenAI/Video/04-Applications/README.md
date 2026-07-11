# 04-Applications - Cas d'usage production Vidéo

[← Video Orchestration](../03-Orchestration/) | [↑ Video](../README.md) | [→ Texte](../../Texte/README.md)

Ce module présente des cas d'usage concrets et des workflows de production pour la génération vidéo.

**Dans le cadre du fil rouge pipeline vidéo pédagogique** : ce niveau met en oeuvre les workflows complets. [04-1](04-1-Educational-Video-Generation.ipynb) génère automatiquement du contenu vidéo éducatif à partir d'un script. [04-3](04-3-Sora-API-Cloud-Video.ipynb) explore la génération cloud via l'API Sora. [04-4](04-4-Production-Video-Pipeline.ipynb) assemble le pipeline bout-en-bout.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 4 |
| Kernel | Python 3 |
| Durée estimée | ~6-8h |
| GPU requis | 0-24GB |

## Aperçu — les cas d'usage production vidéo en images

Ce niveau met en oeuvre les workflows complets : génération automatique de contenu éducatif, workflows créatifs, génération cloud via l'API Sora, et pipeline de production bout-en-bout. Les aperçus de frames ci-dessous, regroupés par cas d'usage, illustrent chaque workflow.

### Vidéo éducative (04-1)

Génération automatique de contenu pédagogique : le workflow produit des séquences de frames illustrant un concept, prêtes à être intégrées dans un module de cours.

<p align="center">
  <img src="assets/readme/vid4-educational.png" alt="Génération vidéo éducative — aperçu des frames" width="480"/>
</p>

### Workflows créatifs (04-2)

Composition créative assistée : séquences générées et leurs variantes de composition, montrant comment le workflow explore différentes mises en scène à partir d'un même prompt.

<p align="center">
  <img src="assets/readme/vid4-creative.png" alt="Workflow créatif vidéo — séquence générée" width="480"/>
</p>

<p align="center">
  <img src="assets/readme/vid4-creative2.png" alt="Workflow créatif — variante de composition" width="480"/>
</p>

### Génération cloud via l'API Sora (04-3)

Appel à l'API Sora pour la génération cloud, avec aperçus des sorties et de leurs variantes alternatives.

<p align="center">
  <img src="assets/readme/vid4-sora.png" alt="Génération Sora via API cloud" width="480"/>
</p>

<p align="center">
  <img src="assets/readme/vid4-sora2.png" alt="Génération Sora — aperçu alternatif" width="480"/>
</p>

### Pipeline de production bout-en-bout (04-4)

Orchestration complète : du prompt à la vidéo finale, enchaînant génération, post-traitement et assemblage dans un pipeline reproductible.

<p align="center">
  <img src="assets/readme/vid4-pipeline.png" alt="Pipeline vidéo production — orchestration" width="480"/>
</p>

Provenance et poids de chaque figure : [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [04-1-Educational-Video-Generation](04-1-Educational-Video-Generation.ipynb) | Contenu éducatif | Mixed | ~12GB |
| 2 | [04-2-Creative-Video-Workflows](04-2-Creative-Video-Workflows.ipynb) | Workflows créatifs | ComfyUI | ~14GB |
| 3 | [04-3-Sora-API-Cloud-Video](04-3-Sora-API-Cloud-Video.ipynb) | Sora API cloud | OpenAI API | 0 |
| 4 | [04-4-Production-Video-Pipeline](04-4-Production-Video-Pipeline.ipynb) | Pipeline production | Mixed | ~18GB |

## Prérequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
```

### Docker Services (optionnel)
```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```
Accès : http://localhost:8188

### Dépendances
```bash
pip install -r requirements.txt
pip install -r requirements-video.txt
```

## Cas d'usage

### 04-1 Educational Video Generation
- **Objectif** : Automatiser la création de contenu vidéo éducatif
- **Technologies** : GPT-5 + modèles vidéo + post-production
- **Applications** : Cours vidéo, tutoriels, formations

### 04-2 Creative Video Workflows
- **Objectif** : Workflows créatifs automatisés
- **Technologies** : ComfyUI + modèles avancés
- **Applications** : Création artistique, publicités, clips musicaux

### 04-3 Sora API Cloud Video
- **Objectif** : Utiliser Sora d'OpenAI
- **Technologies** : OpenAI API + post-processing
- **Applications** : Prototypage rapide, contenu à grande échelle

### 04-4 Production Video Pipeline
- **Objectif** : Pipeline de production vidéo complet
- **Technologies** : Batch processing + monitoring + QC
- **Applications** : Production en série, contenu marketing

## Workflows

### Éducation
```
Brief → GPT-4o (script) → Modèle vidéo → Post-production → Vidéo finale
```

### Création
```
Idée → ComfyUI (génération) → Édition → Validation → Livraison
```

### Production
```
Batch → Queue → Processing → QC → Distribution → Analytics
```

## Ressources

- [Documentation Video principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [GenAI Services](../../../../docs/genai/genai-services.md)
