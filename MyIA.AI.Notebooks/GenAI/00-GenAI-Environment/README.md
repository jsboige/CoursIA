# 00-GenAI-Environment - Setup et Configuration

<!-- CATALOG-STATUS
series: GenAI-00-GenAI-Environment
pedagogical_count: 6
breakdown: Environment-Setup=1, Docker-Services=1, API-Endpoints=1, Environment-Validation=1, ComfyUI-Test=1, Local-Docker=1
maturity: BETA=5, PRODUCTION=1
-->

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Docker Services](00-2-Docker-Services-Management.ipynb)

## Introduction : Pourquoi cet setup est crucial

Avant de plonger dans l'univers des modèles de génération IA, prenez un moment pour comprendre pourquoi une configuration rigoureuse évite 80% des problèmes techniques. Les notebooks GenAI font appel à des services externes, des conteneurs Docker et des modèles complexes – une seule variable d'environnement manquante peut bloquer toute votre exploration. Ce module vous guide pas à pas pour créer une base solide, vous permettant de vous concentrer sur l'essentiel : apprendre et expérimenter avec l'IA.

## Vue d'Ensemble
[GREEN] Setup et Configuration

**Validation: 100% (6/6 notebooks)**

## Notebooks du Module

| # | Notebook | Description | Validation |
|---|----------|-------------|------------|
| 1 | [00-1-Environment-Setup](00-1-Environment-Setup.ipynb) | Configuration environnement complet | OK |
| 2 | [00-2-Docker-Services-Management](00-2-Docker-Services-Management.ipynb) | Gestion services conteneurises | OK |
| 3 | [00-3-API-Endpoints-Configuration](00-3-API-Endpoints-Configuration.ipynb) | Configuration endpoints API | OK |
| 4 | [00-4-Environment-Validation](00-4-Environment-Validation.ipynb) | Tests et validation setup | OK |
| 5 | [00-5-ComfyUI-Local-Test](00-5-ComfyUI-Local-Test.ipynb) | Test local des services ComfyUI | OK |
| 6 | [00-6-Local-Docker-Deployment](00-6-Local-Docker-Deployment.ipynb) | Deploiement Docker local complet | OK |

## Prérequis
- Configuration .env avec clés API
- Python 3.11+ avec dépendances
- Variables d'environnement OpenRouter

## Ce que vous saurez faire

À l'issue de ce module, vous serez capable de :
- Configurer un environnement Python complet pour le développement GenAI
- Gérer des services Docker conteneurisés (ComfyUI, modèles de langue)
- Paramétrer les endpoints API pour les services IA
- Valifier que chaque composant fonctionne correctement
- Déployer localement l'ensemble de l'infrastructure GenAI
- Résoudre les problèmes courants de configuration

## FAQ

### Les notebooks echouent avec "OPENAI_API_KEY not found" ou variable manquante

Le notebook [00-1-Environment-Setup](00-1-Environment-Setup.ipynb) configure les variables d'environnement, mais il faut les creer au prealable dans le fichier `.env` du repertoire `GenAI/` :

```bash
# Template .env (voir .env.example pour la liste complete)
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
OPENROUTER_API_KEY=sk-or-v1-...
COMFYUI_BEARER_TOKEN=...
```

Points frequents :

- Le fichier `.env` doit etre dans `MyIA.AI.Notebooks/GenAI/`, pas dans le sous-repertoire `00-GenAI-Environment/`.
- `OPENAI_API_KEY` et `OPENROUTER_API_KEY` sont deux cles differentes. OpenAI pour les modeaux OpenAI directs, OpenRouter pour l'acces multi-fournisseurs.
- Le script de validation (`python scripts/genai-stack/genai.py validate --full`) detecte les cles manquantes avant l'execution.

### Docker Desktop ne demarre pas ou les conteneurs echouent

Les notebooks [00-2](00-2-Docker-Services-Management.ipynb) et [00-6](00-6-Local-Docker-Deployment.ipynb) requierent Docker Desktop (v29.5.2+ recommande). Si erreur :

```bash
# Verifier Docker
docker --version
docker compose version

# Verifier que Docker Desktop est actif
docker ps
# Si erreur "Cannot connect to the Docker daemon", lancer Docker Desktop

# Verifier les ressources GPU (si applicable)
nvidia-smi
docker run --gpus all nvidia/cuda:12.4.0-base-ubuntu22.04 nvidia-smi
```

Pour les services ComfyUI (notebooks [00-5](00-5-ComfyUI-Local-Test.ipynb)), le conteneur doit avoir acces au GPU. Sur Windows : Docker Desktop > Settings > Resources > cocher "Enable GPU". Sur Linux : installer `nvidia-container-toolkit`.

### Le script de validation echoue sur certains services

Le notebook [00-4-Environment-Validation](00-4-Environment-Validation.ipynb) teste chaque service individuellement. Si certains echouent :

- **ComfyUI (401/502)** : le bearer token dans `.env` peut drift par rapport au token reel du conteneur. Recuperer le token actuel : `docker exec <container> cat login/PASSWORD` et mettre a jour `.env`.
- **vLLM/Z-Image** : le service peut etre DOWN si le GPU est insuffisant (16 GB VRAM minimum). Ce n'est pas bloquant pour les autres notebooks.
- **Reverse proxies (IIS)** : certains proxies (whisper, tts) peuvent retourner 404. Les endpoints directs fonctionnent (ports 8190+).

Le script `genai.py docker status` montre l'etat de chaque conteneur. Les services non critiques (vLLM, reverse proxies) peuvent etre ignores pour les notebooks de base.

### Quelle difference entre les endpoints API et les services Docker ?

| Approche | Notebooks | Avantage | Inconvenient |
|----------|-----------|----------|--------------|
| **API cloud** (OpenAI, Anthropic) | [00-3](00-3-API-Endpoints-Configuration.ipynb) | Aucun setup local | Cout par appel |
| **Docker local** (ComfyUI, Whisper) | [00-5](00-5-ComfyUI-Local-Test.ipynb), [00-6](00-6-Local-Docker-Deployment.ipynb) | Gratuit, controle total | GPU requise, setup lourd |
| **OpenRouter** | [00-3](00-3-API-Endpoints-Configuration.ipynb) | Multi-modeles, une cle | Depend d'OpenRouter |

Les notebooks GenAI utilisent un melange : APIs cloud pour les modeaux de langage (GPT, Claude), Docker local pour les modeaux d'image/audio (ComfyUI, Whisper). Le notebook [00-1](00-1-Environment-Setup.ipynb) configure les deux.

### Peut-on executer les notebooks GenAI sans Docker ?

Partiellement. Les notebooks qui utilisent uniquement des APIs cloud (OpenAI, Anthropic, OpenRouter) fonctionnent sans Docker. C'est le cas de la plupart des notebooks Texte, PostTraining et FineTuning. En revanche :

- **Image** (ComfyUI, Qwen) : Docker requis
- **Audio** (Whisper, Kokoro, MusicGen) : Docker requis
- **Video** (ComfyUI Video) : Docker requis
- **SemanticKernel** : API cloud uniquement, Docker non requis

Le notebook [00-6](00-6-Local-Docker-Deployment.ipynb) detaille le deploiement Docker complet. Si vous n'avez pas de GPU, utiliser Google Colab pour les notebooks GPU-intensifs.

## Utilisation

1. Configurer l'environnement selon 00-GenAI-Environment
2. Executer les notebooks dans l'ordre numerique
3. Verifier les outputs dans /outputs/
