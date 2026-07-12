# 00-GenAI-Environment - Setup et Configuration

<!-- CATALOG-STATUS
series: GenAI-00-GenAI-Environment
pedagogical_count: 6
breakdown: 00-GenAI-Environment=6
maturity: BETA=4, PRODUCTION=2
-->

[← GenAI](../README.md) | [↑ ..](../README.md) | [→ Image](../Image/README.md)

Ce module configure l'environnement technique avant toute exploration GenAI. Les notebooks couvrent le setup Python, la gestion des conteneurs Docker (ComfyUI, Whisper, MusicGen), la configuration des endpoints API, et un test complet de validation.

## Objectifs d'apprentissage

À l'issue de ce module, vous serez capable de :

1. **Configurer** un environnement Python complet pour le développement GenAI (dépendances, variables d'environnement, services Docker)
2. **Gérer** des services Docker conteneurisés (ComfyUI, modèles de langue) avec démarrage, arrêt et monitoring
3. **Paramétrer** les endpoints API pour les services IA (OpenAI, Anthropic, OpenRouter, services locaux)
4. **Valider** que chaque composant fonctionne correctement via les scripts de diagnostic
5. **Déployer** localement l'infrastructure GenAI complète sur un poste de travail

## Notebooks

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [00-1-Environment-Setup](00-1-Environment-Setup.ipynb) | Configuration environnement complet | 30 min |
| 2 | [00-2-Docker-Services-Management](00-2-Docker-Services-Management.ipynb) | Gestion services conteneurisés | 40 min |
| 3 | [00-3-API-Endpoints-Configuration](00-3-API-Endpoints-Configuration.ipynb) | Configuration endpoints API | 25 min |
| 4 | [00-4-Environment-Validation](00-4-Environment-Validation.ipynb) | Tests et validation setup | 30 min |
| 5 | [00-5-ComfyUI-Local-Test](00-5-ComfyUI-Local-Test.ipynb) | Test local des services ComfyUI | 25 min |
| 6 | [00-6-Local-Docker-Deployment](00-6-Local-Docker-Deployment.ipynb) | Déploiement Docker local complet | 45 min |

## Prérequis & environnement

| Besoin | Détail |
|--------|--------|
| Python | 3.10+ avec dépendances (`pip install -r requirements.txt`) |
| Docker Desktop | v29.5+ recommandé pour les notebooks GPU |
| Clés API | `.env` dans `GenAI/` : `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN` |
| GPU | Optionnel pour ce module, requis pour les sous-domaines Image/Audio/Video |

## FAQ

### Les notebooks échouent avec "OPENAI_API_KEY not found" ou variable manquante

Le notebook [00-1-Environment-Setup](00-1-Environment-Setup.ipynb) configure les variables d'environnement, mais il faut les créer au préalable dans le fichier `.env` du répertoire `GenAI/` :

```bash
# Template .env (voir .env.example pour la liste complète)
OPENAI_API_KEY=sk-...
ANTHROPIC_API_KEY=sk-ant-...
OPENROUTER_API_KEY=sk-or-v1-...
COMFYUI_BEARER_TOKEN=...
```

Points fréquents :

- Le fichier `.env` doit être dans `MyIA.AI.Notebooks/GenAI/`, pas dans le sous-répertoire `00-GenAI-Environment/`.
- `OPENAI_API_KEY` et `OPENROUTER_API_KEY` sont deux clés différentes. OpenAI pour les modeaux OpenAI directs, OpenRouter pour l'accès multi-fournisseurs.
- Le script de validation (`python scripts/genai-stack/genai.py validate --full`) détecte les clés manquantes avant l'exécution.

### Docker Desktop ne démarre pas ou les conteneurs échouent

Les notebooks [00-2](00-2-Docker-Services-Management.ipynb) et [00-6](00-6-Local-Docker-Deployment.ipynb) requièrent Docker Desktop (v29.5.2+ recommandé). Si erreur :

```bash
# Vérifier Docker
docker --version
docker compose version

# Vérifier que Docker Desktop est actif
docker ps
# Si erreur "Cannot connect to the Docker daemon", lancer Docker Desktop

# Vérifier les ressources GPU (si applicable)
nvidia-smi
docker run --gpus all nvidia/cuda:12.4.0-base-ubuntu22.04 nvidia-smi
```

Pour les services ComfyUI (notebooks [00-5](00-5-ComfyUI-Local-Test.ipynb)), le conteneur doit avoir accès au GPU. Sur Windows : Docker Desktop > Settings > Resources > cocher "Enable GPU". Sur Linux : installer `nvidia-container-toolkit`.

### Le script de validation échoue sur certains services

Le notebook [00-4-Environment-Validation](00-4-Environment-Validation.ipynb) teste chaque service individuellement. Si certains échouent :

- **ComfyUI (401/502)** : le bearer token dans `.env` peut drift par rapport au token réel du conteneur. Récupérer le token actuel : `docker exec <container> cat login/PASSWORD` et mettre à jour `.env`.
- **vLLM/Z-Image** : le service peut être DOWN si le GPU est insuffisant (16 GB VRAM minimum). Ce n'est pas bloquant pour les autres notebooks.
- **Reverse proxies (IIS)** : certains proxies (whisper, tts) peuvent retourner 404. Les endpoints directs fonctionnent (ports 8190+).

Le script `genai.py docker status` montre l'état de chaque conteneur. Les services non critiques (vLLM, reverse proxies) peuvent être ignorés pour les notebooks de base.

### Quelle différence entre les endpoints API et les services Docker ?

| Approche | Notebooks | Avantage | Inconvénient |
|----------|-----------|----------|--------------|
| **API cloud** (OpenAI, Anthropic) | [00-3](00-3-API-Endpoints-Configuration.ipynb) | Aucun setup local | Coût par appel |
| **Docker local** (ComfyUI, Whisper) | [00-5](00-5-ComfyUI-Local-Test.ipynb), [00-6](00-6-Local-Docker-Deployment.ipynb) | Gratuit, contrôle total | GPU requise, setup lourd |
| **OpenRouter** | [00-3](00-3-API-Endpoints-Configuration.ipynb) | Multi-modèles, une clé | Dépend d'OpenRouter |

Les notebooks GenAI utilisent un mélange : APIs cloud pour les modeaux de langage (GPT, Claude), Docker local pour les modeaux d'image/audio (ComfyUI, Whisper). Le notebook [00-1](00-1-Environment-Setup.ipynb) configure les deux.

### Peut-on exécuter les notebooks GenAI sans Docker ?

Partiellement. Les notebooks qui utilisent uniquement des APIs cloud (OpenAI, Anthropic, OpenRouter) fonctionnent sans Docker. C'est le cas de la plupart des notebooks Texte, PostTraining et FineTuning. En revanche :

- **Image** (ComfyUI, Qwen) : Docker requis
- **Audio** (Whisper, Kokoro, MusicGen) : Docker requis
- **Video** (ComfyUI Video) : Docker requis
- **SemanticKernel** : API cloud uniquement, Docker non requis

Le notebook [00-6](00-6-Local-Docker-Deployment.ipynb) détaille le déploiement Docker complet. Si vous n'avez pas de GPU, utiliser Google Colab pour les notebooks GPU-intensifs.

## Utilisation

1. Configurer l'environnement selon 00-GenAI-Environment
2. Exécuter les notebooks dans l'ordre numérique
3. Vérifier les outputs dans /outputs/
