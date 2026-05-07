# Image - Génération d'Images par IA

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Docker Management](../00-GenAI-Environment/00-2-Docker-Services-Management.ipynb)

La generation d'images par IA est la deuxieme modalite generative la plus accessible apres le texte. Elle couvre un spectre large : generation from scratch (DALL-E, FLUX), edition d'images existantes (Qwen Image Edit), upscaling (Real-ESRGAN), et orchestration de workflows multi-modeles via ComfyUI. 19 notebooks repartis sur 5 niveaux progressifs.

## Fil rouge : construire un generateur de contenu visuel educatif

L'objectif fil rouge de cette serie est de construire un systeme capable de produire des visuels pedagogiques de qualite : diagrammes, illustrations conceptuelles, et images d'identite pour des supports de cours. Chaque niveau apporte une brique supplementaire : generation simple via API cloud (niveau 1), modeles avances et edition fine (niveau 2), comparaison et orchestration multi-modeles (niveau 3), workflows de production (niveau 4), et cas d'usage concrets par domaine (examples).

## Vue d'ensemble

19 notebooks organisés en 5 sous-dossiers, représentant environ 6 à 8 heures d'apprentissage intensif dans le domaine de la génération d'images par IA, avec un taux de validation de 100%.


## Structure

```
Image/
├── 01-Foundation/     # Modèles de base (5 notebooks)
├── 02-Advanced/       # Modèles avancés (4 notebooks)
├── 03-Orchestration/  # Multi-modèles (3 notebooks)
├── 04-Applications/   # Production (4 notebooks)
└── examples/          # Cas d'usage (3 notebooks)
```

## Progression par niveau

### 01-Foundation - Modeles de base

Avant de produire des visuels pedagogiques, il faut maitriser les outils de generation. Ce niveau couvre les deux approches : API cloud (DALL-E 3, GPT-5) pour la simplicite, et modeles locaux via ComfyUI (SD XL Turbo, Qwen) pour le controle fin. [01-3](01-Foundation/01-3-Basic-Image-Operations.ipynb) donne les bases de manipulation d'image (PIL, OpenCV) necessaires pour comprendre ce que font les modeles.

| Notebook | Contenu | Service |
|----------|---------|---------|
| [01-1-OpenAI-DALL-E-3](01-Foundation/01-1-OpenAI-DALL-E-3.ipynb) | Generation avec DALL-E 3 | OpenAI API |
| [01-2-GPT-5-Image-Generation](01-Foundation/01-2-GPT-5-Image-Generation.ipynb) | Generation avec GPT-5 | OpenAI API |
| [01-3-Basic-Image-Operations](01-Foundation/01-3-Basic-Image-Operations.ipynb) | Operations de base | PIL/OpenCV |
| [01-4-Forge-SD-XL-Turbo](01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb) | Stable Diffusion XL Turbo | ComfyUI |
| [01-5-Qwen-Image-Edit](01-Foundation/01-5-Qwen-Image-Edit.ipynb) | Introduction Qwen | ComfyUI |

[README 01-Foundation](01-Foundation/README.md)

### 02-Advanced - Modeles avances

Un visuel educatif de qualite demande des outils plus precis : edition d'images existantes (Qwen), generation haute qualite (FLUX), ou modeles legers et rapides (Z-Image/Lumina). Ce niveau explore les modeles de pointe et leurs compromis entre qualite, vitesse et ressources GPU.

| Notebook | Contenu | Service |
|----------|---------|---------|
| [02-1-Qwen-Image-Edit-2509](02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb) | Edition avancee Qwen | ComfyUI |
| [02-2-FLUX-1-Advanced-Generation](02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb) | Generation FLUX | ComfyUI |
| [02-3-Stable-Diffusion-3-5](02-Advanced/02-3-Stable-Diffusion-3-5.ipynb) | SD 3.5 | ComfyUI |
| [02-4-Z-Image-Lumina2](02-Advanced/02-4-Z-Image-Lumina2.ipynb) | Z-Image/Lumina | ComfyUI |

[README 02-Advanced](02-Advanced/README.md)

### 03-Orchestration - Multi-modeles

En production, un seul modele ne suffit pas toujours. Ce niveau compare les modeaux entre eux pour choisir le bon selon le contexte, orchestre des pipelines de traitement (generation puis edition puis upscaling), et optimise les performances pour le deploiement.

| Notebook | Contenu |
|----------|---------|
| [03-1-Multi-Model-Comparison](03-Orchestration/03-1-Multi-Model-Comparison.ipynb) | Comparaison multi-modeles |
| [03-2-Workflow-Orchestration](03-Orchestration/03-2-Workflow-Orchestration.ipynb) | Orchestration de workflows |
| [03-3-Performance-Optimization](03-Orchestration/03-3-Performance-Optimization.ipynb) | Optimisation performance |

[README 03-Orchestration](03-Orchestration/README.md)

### 04-Applications - Production

Ce niveau met en oeuvre les workflows complets : generation automatisee de contenu educatif, pipelines creatifs, integration en production, et un exemple concret de conversion d'images en patrons de point de croix.

| Notebook | Contenu |
|----------|---------|
| [04-1-Educational-Content-Generation](04-Applications/04-1-Educational-Content-Generation.ipynb) | Contenu educatif |
| [04-2-Creative-Workflows](04-Applications/04-2-Creative-Workflows.ipynb) | Workflows creatifs |
| [04-3-Production-Integration](04-Applications/04-3-Production-Integration.ipynb) | Integration production |
| [04-4-Cross-Stitch-Pattern-Maker-Legacy](04-Applications/04-4-Cross-Stitch-Pattern-Maker-Legacy.ipynb) | Point de croix (legacy) |

[README 04-Applications](04-Applications/README.md)

### examples/ - Cas d'usage

Applications directes par domaine : histoire-geographie (cartes, reconstitutions), litterature (illustrations de textes), et sciences (diagrammes, schemas techniques). Ces notebooks montrent comment adapter les techniques des niveaux precedents a des besoins concrets.

| Notebook | Domaine |
|----------|---------|
| [history-geography](examples/history-geography.ipynb) | Histoire-Geographie |
| [literature-visual](examples/literature-visual.ipynb) | Litterature |
| [science-diagrams](examples/science-diagrams.ipynb) | Diagrammes scientifiques |

## Technologies

| Technologie | Notebooks | Prerequis |
|-------------|-----------|-----------|
| **OpenAI DALL-E 3** | 01-1, 01-2 | `OPENAI_API_KEY` |
| **ComfyUI + Qwen** | 01-4, 01-5, 02-1 | Docker, ~29GB VRAM |
| **ComfyUI + FLUX** | 02-2 | Docker GPU |
| **ComfyUI + SD 3.5** | 02-3 | Docker GPU |
| **Z-Image/Lumina** | 02-4 | Docker, ~10GB VRAM |

## Prerequisites

### API Keys

```bash
# Dans GenAI/.env
OPENAI_API_KEY=sk-...
COMFYUI_BEARER_TOKEN=...
```

### Docker Services

```bash
cd docker-configurations/services/comfyui-qwen
docker-compose up -d
```

Acces : http://localhost:8188

## Parcours recommande

```
01-Foundation (bases)
    |
02-Advanced (modeles specifiques)
    |
03-Orchestration (comparaison, workflows)
    |
04-Applications (production)
```

| Objectif | Notebooks |
|----------|-----------|
| Decouverte rapide | 01-1, 01-3 |
| Generation avancee | 01-1 a 02-4 |
| Production | Tous + 03 + 04 |

## Recette : construire un generateur de contenu visuel educatif

Le fil rouge de cette serie est la creation d'un systeme de visuels pedagogiques. Voici comment les niveaux s'articulent :

1. **01-Foundation** (generation de base) : [01-1](01-Foundation/01-1-OpenAI-DALL-E-3.ipynb) et [01-2](01-Foundation/01-2-GPT-5-Image-Generation.ipynb) couvrent la generation via API cloud. [01-4](01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb) et [01-5](01-Foundation/01-5-Qwen-Image-Edit.ipynb) introduisent les modeles locaux. A la fin, vous savez generer une image a partir d'un texte.

2. **02-Advanced** (edition et qualite) : [02-1](02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb) permet d'editer une image existante pour corriger ou enrichir un visuel. [02-4](02-Advanced/02-4-Z-Image-Lumina2.ipynb) offre une generation rapide pour le prototypage. [02-2](02-Advanced/02-2-FLUX-1-Advanced-Generation.ipynb) pousse la qualite plus loin.

3. **03-Orchestration** (comparaison et pipelines) : [03-1](03-Orchestration/03-1-Multi-Model-Comparison.ipynb) compare les modeles pour choisir le meilleur rapport qualite/cout. [03-2](03-Orchestration/03-2-Workflow-Orchestration.ipynb) assemble un pipeline de generation complet.

4. **04-Applications** (production) : [04-1](04-Applications/04-1-Educational-Content-Generation.ipynb) applique le pipeline au contenu educatif. Les notebooks [examples/](examples/) montrent des cas d'usage par domaine (histoire, sciences, litterature).

## Licence

Voir la licence du repository principal.
