# 04-Applications - Cas d'usage production

[← Image Orchestration](../03-Orchestration/) | [↑ Image](../README.md) | [→ Audio](../../Audio/README.md)

Ce module présente des cas d'usage concrets et des workflows de production pour la génération d'images.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 4 |
| Kernel | Python 3 |
| Duree estimee | ~4-6h |
| GPU requis | 0-14GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [04-1-Educational-Content-Generation](04-1-Educational-Content-Generation.ipynb) | Contenu éducatif | Mixed | ~10GB |
| 2 | [04-2-Creative-Workflows](04-2-Creative-Workflows.ipynb) | Workflows créatifs | ComfyUI | Variable |
| 3 | [04-3-Production-Integration](04-3-Production-Integration.ipynb) | Intégration production | Mixed | ~10GB |
| 4 | [04-4-Cross-Stitch-Pattern-Maker-Legacy](04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb) | Point de croix (legacy) | Local | 0 |

## Prérequis

### API Keys
```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
COMFYUI_BEARER_TOKEN=...
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
pip install -r requirements-comfyui.txt
```

## Cas d'usage

### 04-1 Educational Content Generation
- **Objectif** : Automatiser la création de contenu pédagogique
- **Technologies** : DALL-E 3 + GPT-4o + post-processing
- **Applications** : Cours, supports de formation, illustrations

### 04-2 Creative Workflows
- **Objectif** : Workflows créatifs automatisés
- **Technologies** : ComfyUI + modèles avancés
- **Applications** : Design graphique, art numérique, prototypes

### 04-3 Production Integration
- **Objectif** : Intégration dans pipelines de production
- **Technologies** : API + batch processing + monitoring
- **Applications** : E-commerce, média, contenu à grande échelle

### 04-4 Cross-Stitch Pattern Maker
- **Objectif** : Conversion d'images en patrons de point de croix
- **Technologies** : PIL + algorithmes de conversion
- **Applications** : Artisanat, loisirs, design textile

## Workflows

### Éducation
```
Texte → GPT-4o (brief) → DALL-E 3 (images) → Post-processing → Support
```

### Création
```
Brief → ComfyUI (génération) → Édition → Validation → Livraison
```

### Production
```
Batch → Queue → Processing → QC → Output → Analytics
```

## Ressources

- [Documentation Image principale](../README.md)
- [Guide ComfyUI](../../00-GenAI-Environment/README.md)
- [Production Best Practices](../../docs/)