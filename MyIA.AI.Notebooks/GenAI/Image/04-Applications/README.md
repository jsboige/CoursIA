# 04-Applications - Cas d'usage production

[← Image Orchestration](../03-Orchestration/) | [↑ Image](../README.md) | [→ Audio](../../Audio/README.md)

Ce module présente des cas d'usage concrets et des workflows de production pour la génération d'images.

**Dans le cadre du fil rouge contenu visuel éducatif** : ce niveau met en oeuvre les workflows complets. [04-1](04-1-Educational-Content-Generation.html) automatise la création de visuels pédagogiques (brief texte vers images). [04-2](04-2-Creative-Workflows.html) gère les workflows créatifs. [04-3](04-3-Production-Integration.html) intègre le pipeline en production.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Kernel | Python 3 |
| Durée estimée | ~4-6h |
| GPU requis | 0-14GB |

## Notebooks

| # | Notebook | Contenu | Service | VRAM |
|---|----------|---------|---------|------ |
| 1 | [04-1-Educational-Content-Generation](04-1-Educational-Content-Generation.html) | Contenu éducatif | Mixed | ~10GB |
| 2 | [04-2-Creative-Workflows](04-2-Creative-Workflows.html) | Workflows créatifs | ComfyUI | Variable |
| 3 | [04-3-Production-Integration](04-3-Production-Integration.html) | Intégration production | Mixed | ~10GB |
| 4 | [04-4-Cross-Stitch-Pattern-Maker-Legacy](04-4-Cross-Stitch-Pattern-Maker-Legacy.html) | Point de croix (legacy) | Local | 0 |
| 5 | [04-5-MiniMax-Cloud-Image](04-5-MiniMax-Cloud-Image.html) | Images par API cloud | MiniMax Hailuo | 0 |

## Prérequis

### API Keys

Voir [`scripts/secrets/render_envs.py`](../../../../scripts/secrets/render_envs.py) + [`.claude/rules/secrets-hygiene.md`](../../../../.claude/rules/secrets-hygiene.md). Les clés sont centralisées dans `.secrets/master.env` (gitignored) et propagées via `python scripts/secrets/render_envs.py` vers `GenAI/.env`. **Jamais de littéraux inline** (`sk-...`, `Bearer ...`) ni dans ce README, ni dans le code, ni dans les cellules notebooks (cf incident 2026-05-14).

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

### 04-1 Génération de contenu pédagogique
- **Objectif** : Automatiser la création de contenu pédagogique
- **Technologies** : gpt-image-1 + GPT-4o + post-processing
- **Applications** : Cours, supports de formation, illustrations

### 04-2 Creative Workflows
- **Objectif** : Workflows créatifs automatisés
- **Technologies** : ComfyUI + modèles avancés
- **Applications** : Design graphique, art numérique, prototypes

### 04-3 Intégration en production
- **Objectif** : Intégration dans pipelines de production
- **Technologies** : API + batch processing + monitoring
- **Applications** : E-commerce, média, contenu à grande échelle

### 04-4 Cross-Stitch Pattern Maker
- **Objectif** : Conversion d'images en patrons de point de croix
- **Technologies** : PIL + algorithmes de conversion
- **Applications** : Artisanat, loisirs, design textile

### 04-5 MiniMax Hailuo — images par le service cloud
- **Objectif** : Générer des images par l'API cloud Hailuo (texte vers image, image vers image) quand la licence des poids exclut l'auto-hébergement en UE
- **Technologies** : API `image-01` via `urllib` + artefacts PNG et `metadata.json` commités
- **Applications** : Illustration à la demande, transfert de style, comparaison des voies cloud et locale

## Workflows

### Éducation
```
Texte → GPT-4o (brief) → gpt-image-1 (images) → Post-processing → Support
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
- [GenAI Services](../../../../docs/genai/genai-services.md)
