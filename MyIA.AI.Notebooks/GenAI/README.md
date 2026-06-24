# GenAI - Écosystème IA Générative

<!-- CATALOG-STATUS
series: GenAI
pedagogical_count: 129
breakdown: Audio=30, SemanticKernel=20, Texte=18, Image=17, Video=17, 00-GenAI-Environment=6, PostTraining=6, FineTuning=5, Vibe-Coding=5, CaseStudies=4, root=1
maturity: PRODUCTION=89, BETA=30, ALPHA=5, TEMPLATE=3, DRAFT=2
-->

Ce parcours vous forme à la maîtrise de l'IA générative dans toute sa diversité : générer des images, synthétiser la voix, composer de la musique, produire des vidéos, orchestrer des agents autonomes, et déployer des applications en production. Chaque modalité suit une progression en quatre niveaux, du premier pas avec une API jusqu'aux pipelines multi-modèles de production. Les décomptes par sous-domaine et la maturité de chaque notebook se lisent dans le marqueur `CATALOG-STATUS` en tête de ce fichier.

## Pourquoi ce parcours ?

L'IA générative a transformé la création de contenu en 2024-2026. Un développeur qui sait piloter DALL-E pour générer une illustration, Whisper pour transcrire un podcast, MusicGen pour composer un fond sonore, et orchestrer tout cela via des agents autonomes, possède un avantage décisif sur le marché. Ce parcours ne se contente pas d'énumérer des APIs : il vous apprend à **comprendre** les modèles (leurs forces, leurs limites, leurs pièges), à **comparer** les approches (open-source vs cloud, local vs API), et à **combiner** les modalités dans des pipelines réels.

## Structure

```text
GenAI/
├── 00-GenAI-Environment/    # Setup et configuration
├── Image/                   # Génération d'images
├── Audio/                   # Speech, TTS, musique, séparation
├── Video/                   # Génération et compréhension vidéo
├── Texte/                   # LLMs et génération de texte
├── SemanticKernel/          # Microsoft Semantic Kernel
├── FineTuning/              # Fine-tuning de modèles : LoRA/QLoRA/SFT/DPO
├── PostTraining/            # Post-training SOTA : SFT/RLHF/DPO/GRPO/RLVR
├── CaseStudies/             # Études de cas étudiants
├── Playwright-OWUI/         # Tests E2E Playwright (5 modules, 30+ tests)
└── Vibe-Coding/             # Tutoriels Claude Code et Roo Code
```

---

## Les sous-domaines

### 00-GenAI-Environment - Votre point de départ

Avant de générer la moindre image ou le moindre son, il faut configurer l'environnement : clés API, services Docker, et validation que tout fonctionne. Ces 6 notebooks sont le passage obligatoire. Ils couvrent le setup Python, la gestion des conteneurs Docker (ComfyUI, Whisper, MusicGen), la configuration des endpoints API, et un test complet de validation.

[README complet](00-GenAI-Environment/README.md) | ~4h

---

### Image - Générer, éditer et orchestrer des images

On commence par les fondamentaux : appeler DALL-E 3 et GPT-5 pour générer des images depuis un prompt texte, puis manipuler ces images avec PIL et OpenCV. Le niveau avancé introduit les modèles open-source hébergés localement (Qwen Image Edit pour l'édition, FLUX pour la qualité, Stable Diffusion 3.5 pour la production, Z-Image/Lumina pour l'expérimental). En orchestration, on compare les modèles entre eux et on enchaîne les workflows. Les applications métier montrent comment intégrer tout cela dans des cas réels : contenu éducatif, workflows créatifs, motifs décoratifs.

**Fil rouge** : construire un générateur de contenu visuel pour l'éducation (diagrammes scientifiques, illustrations pédagogiques, motifs décoratifs).

[README complet](Image/README.md) | ~6-8h

---

### Audio - Parler, écouter, composer

Cette série couvre le spectre complet de l'audio IA : reconnaissance vocale (Whisper V3, OpenAI API), synthèse vocale (Kokoro, OpenAI TTS, Chatterbox), clonage de voix (XTTS v2), génération musicale (MusicGen, YuE), séparation de sources (Demucs), et pipelines complets (podcast automatique, transcription batch, synchronisation audio-vidéo). Le détail de chaque niveau et les services utilisés se trouve dans le [README Audio](Audio/README.md).

**Fil rouge** : produire un podcast automatique avec voix synthétique personnalisée et fond musical généré.

[README complet](Audio/README.md) | ~14-16h

---

### Video - Comprendre, générer et produire

La vidéo est la modalité la plus exigeante en ressources mais aussi la plus spectaculaire. On commence par comprendre des vidéos existantes (GPT-5, Qwen-VL), puis on génère (HunyuanVideo, Wan, Sora). Les notebooks d'orchestration combinent compréhension et génération dans des workflows de production vidéo. La série couvre aussi le surcadrage d'images (ESRGAN) et la synchronisation audio-vidéo.

**Fil rouge** : créer une vidéo pédagogique automatisée depuis un script texte.

[README complet](Video/README.md) | ~14h

---

### Texte - Maîtriser les LLMs et les APIs OpenAI

Le texte est le socle de toute interaction avec l'IA générative. Cette série va au-delà du simple "prompt engineering" : structured outputs pour des réponses fiables, function calling pour connecter les LLMs à vos outils, RAG pour injecter de la connaissance externe, code interpreter pour l'exécution dynamique, et les modèles de raisonnement (o-series) pour les tâches complexes. Les derniers notebooks couvrent les patterns de production et les LLMs locaux.

[README complet](Texte/README.md) | ~10h

---

### SemanticKernel - Orchestration agentique avec Microsoft

Semantic Kernel est le SDK Microsoft pour construire des applications agentiques. Il fournit les briques pour orchestrer les LLMs avec des plugins, des agents, des filtres, des vector stores, et des processus multi-étapes. Cette série couvre le SDK en Python et en C# (.NET Interactive), avec une progression qui va des fondamentaux aux patterns avancés (MCP, multi-modalité, interop CLR).

[README complet](SemanticKernel/README.md) | ~20h

---

### Vibe-Coding - Développer avec des agents IA

Le "vibe coding" est la compétence la plus demandée de 2026 : décrire ce qu'on veut à un agent IA et le laisser écrire, tester et déployer le code. Cette série couvre les deux outils majeurs du marché : Claude Code (Anthropic) et Roo Code (communautaire). Chaque outil est abordé en 5 modules, de la découverte à l'automatisation avancée.

[README complet](Vibe-Coding/README.md) | ~30h

---

### Playwright-OWUI - Tester les applications GenAI

Les applications GenAI doivent être testées rigoureusement. Cette série utilise Playwright pour écrire des tests de bout en bout sur Open WebUI, une interface réelle de chat LLM. On y apprend la navigation, l'authentification, le streaming de réponses, le RAG, les outils MCP, et le déploiement CI/CD.

[README complet](Playwright-OWUI/README.md) | ~14h

---

### CaseStudies - Projets étudiants

Projets réalisés par les étudiants : génération d'images style Barbie/Shrek, générateur de recettes, chatbot médical éducatif, challenges style Fort Boyard. Ces notebooks illustrent la diversité des applications possibles après le parcours.

[README complet](CaseStudies/README.md)

---

## Progression recommandée

### Découvreur (initiation rapide, ~20h)

Commencez par `00-GenAI-Environment/` pour le setup, puis choisissez une modalité qui vous intéresse : `Image/01-Foundation/` pour le visuel, ou `Audio/01-Foundation/` pour le son. L'objectif est de générer votre premier contenu en moins d'une journée.

### Praticien (maîtrise multi-modale, ~50h)

Couvrez les quatre modalités de base (Image, Audio, Video, Texte) au niveau Foundation, puis approfondissez une ou deux modalités au niveau Advanced. Vous serez capable de combiner texte, image et son dans un projet cohérent.

### Agentiste (full-stack agentic, ~90h)

Ajoutez SemanticKernel pour l'orchestration et Vibe-Coding pour le développement assisté. Vous construirez pipelines multi-modèles autonomes et des agents capables de chaînes de traitement complexes.

### Expert (avec production, ~120h+)

Complétez avec Playwright pour les tests E2E et les notebooks Applications de chaque modalité. Vous maîtrisez le cycle complet : génération, orchestration, tests, déploiement.

---

## Démarrage rapide

### 1. Configuration

```bash
cd MyIA.AI.Notebooks/GenAI
cp .env.example .env
# Éditez .env avec vos clés API (token fourni par l'enseignant)
```

### 2. Installation

```bash
pip install -r requirements.txt
python -c "import jupyter_client; print('Jupyter OK')"
```

### 3. Premier pas

Lancez Jupyter Lab et commencez par `00-GenAI-Environment/00-1-Environment-Setup.ipynb`. Ce notebook vérifie que votre environnement est opérationnel et guide la configuration des services.

---

## Authentification ComfyUI

Les services GenAI locaux (Qwen Image Edit, Z-Image, Whisper, etc.) sont protégés par authentification Bearer Token.

1. **Obtenir le token** : contactez votre enseignant
2. **Configuration** : ajoutez `COMFYUI_BEARER_TOKEN` dans `.env`
3. **Utilisation** : les notebooks chargent automatiquement les credentials via `comfyui_client.py`

Tous les notebooks supportent la graceful degradation : sans token, ils utilisent les APIs cloud en fallback.

---

## Variables d'environnement

Les clés essentielles dans `.env` :

| Variable | Usage | Requis pour |
| ---------- | ------- | ------------- |
| `OPENAI_API_KEY` | DALL-E 3, GPT-5, Whisper, TTS | Image, Audio, Texte |
| `ANTHROPIC_API_KEY` | Claude Vision | Video |
| `HUGGINGFACE_TOKEN` | Modèles HF open-source | Image, Video |
| `COMFYUI_BEARER_TOKEN` | Services locaux ComfyUI | Image (local), Video |

Template complet : [`.env.example`](.env.example)

---

## Outils de validation

```bash
# Validation structure (metadata, outputs, kernel)
python scripts/notebook_tools/notebook_tools.py validate <path>

# Exécution complète (Papermill)
python scripts/notebook_tools/notebook_tools.py execute <path>

# Analyse structure (stats cellules, outputs)
python scripts/notebook_tools/notebook_tools.py analyze <path>
```

---

## Acquis d'apprentissage

À l'issue du parcours, vous êtes capable de :

- **Sélectionner le bon modèle** pour une tâche donnée — connaître les forces/faiblesses des modèles cloud (DALL-E, GPT, Whisper, Sora) face aux modèles open-source locaux (FLUX, SD 3.5, Qwen-Image, Whisper-local, MusicGen, HunyuanVideo) et arbitrer sur coût / qualité / souveraineté des données.
- **Combiner les modalités** dans des pipelines cohérents — texte vers image, image vers vidéo, audio vers texte vers audio, sans casser la chaîne d'inférence ni perdre le contexte sémantique.
- **Orchestrer des agents** via Semantic Kernel (plugins, agents, filtres, vector stores, processus multi-étapes) en Python et en C#/.NET Interactive.
- **Industrialiser une application GenAI** avec authentification ComfyUI, graceful degradation cloud/local, tests E2E Playwright sur Open WebUI, et intégration MCP.
- **Développer avec des agents IA** (Claude Code, Roo Code) en mode "vibe coding" — formuler les besoins, itérer sur les diffs, automatiser les workflows de développement.
- **Évaluer la qualité** des sorties générées — métriques objectives (FID, WER, BLEU), validation subjective structurée, comparaison de pipelines.

## Fil rouge transverse

Les sous-domaines ne sont pas isolés. Un projet final typique enchaîne :

1. **Texte** produit un script structuré (function calling, structured outputs)
2. **Image** illustre les concepts (DALL-E, FLUX, ou Qwen Image Edit pour les retouches)
3. **Audio** synthétise la narration (Kokoro/OpenAI TTS) + fond musical (MusicGen)
4. **Video** assemble le tout (HunyuanVideo pour la génération, Demucs pour la sync A/V)
5. **SemanticKernel** orchestre le pipeline en agents autonomes
6. **Playwright-OWUI** teste l'interface utilisateur du produit final

C'est ce parcours d'intégration qui différencie une démonstration jouet d'un produit déployable.

## FAQ

### Faut-il un GPU pour cette série ?

Non. Les notebooks Image utilisent ComfyUI hébergé sur un serveur distant (RTX 3090 dédiée, accessible via API). Les notebooks Texte utilisent les API cloud (OpenAI, Anthropic). Les notebooks Audio et Video peuvent tourner en CPU pour les démos (avec une latence plus élevée). Si vous avez un GPU local, les notebooks montrent aussi comment l'utiliser.

### Quels sont les coûts API attendus ?

La série est conçue pour minimiser les coûts. Les notebooks Texte utilisent principalement GPT-4o-mini (~0.15$/1M input tokens) et GPT-4o (~2.50$/1M input tokens). Les notebooks Image utilisent DALL-E 3 uniquement pour les exercices (les exemples utilisent ComfyUI/Qwen gratuit). Budget estimé : **5-15$ total** pour l'ensemble de la série, sauf appels itératifs intensifs.

### Quelle est la différence entre ComfyUI et DALL-E ?

**ComfyUI** est un serveur open-source hébergé localement qui exécute des modèles open-source (FLUX, SD 3.5, Qwen Image Edit). Avantages : gratuit, contrôle total sur les paramètres (seed, steps, CFG), pipelines personnalisables. **DALL-E 3** est l'API cloud d'OpenAI. Avantages : qualité élevée par défaut, simplicité d'usage (un appel API = une image). La série montre les deux et vous apprend à choisir selon le contexte.

### Peut-on suivre cette série en parallèle d'une autre ?

Oui. Chaque sous-domaine (Image, Audio, Video, Texte, SemanticKernel) est indépendant. Le parcours recommandé est de commencer par **Texte** (nécessaire pour comprendre les prompts utilisés partout) puis de choisir un sous-domaine selon votre projet.

### Erreur ComfyUI 401 Unauthorized

Vérifiez que `COMFYUI_BEARER_TOKEN` est configuré dans `.env`. Le token est disponible auprès de l'enseignant. Sans token, les notebooks basculent en mode cloud (DALL-E/OpenAI) si `OPENAI_API_KEY` est présent.

### Docker services ne démarrent pas

Vérifiez que Docker Desktop est en cours d'exécution et que les conteneurs sont actifs :

```bash
python scripts/genai-stack/genai.py docker status
```

Si les services sont DOWN, relancez avec `genai.py docker start`. Détails : [docs/genai/genai-services.md](../../docs/genai/genai-services.md).

Pour le troubleshooting avancé (timeout Papermill, OOM GPU, .NET), consultez le README de chaque sous-domaine.

## Concepts clés

| Concept | Description | Série principale |
|---------|-------------|-----------------|
| **Latent space** | Espace compressé où le modèle "pense" — toute génération commence ici | Image, Video |
| **Diffusion** | Processus itératif : bruit → image/audio/vidéo en N étapes | Image, Video, Audio |
| **VAE / VAE-Decoder** | Encodeur/décodeur entre pixel space et latent space | Image |
| **CFG (Classifier-Free Guidance)** | Paramètre contrôlant la fidélité au prompt vs liberté créatrice | Image |
| **LoRA / QLoRA** | Adaptateurs légers pour spécialiser un modèle sans ré-entraîner tout le poids | FineTuning |
| **DPO / RLHF** | Alignement des modèles sur les préférences humaines | PostTraining |
| **RAG** | Retrieval-Augmented Generation : injecter des documents externes dans le contexte LLM | Texte |
| **Function Calling** | Le LLM appelle vos fonctions — passerelle vers les outils et APIs | Texte |
| **Structured Outputs** | Forcer le LLM à respecter un schéma JSON précis | Texte |
| **SFT / GRPO / RLVR** | Post-training : Supervised Fine-Tuning, Group Relative Policy Optimization, RL with Verifiable Rewards | PostTraining |
| **Semantic Kernel** | SDK d'orchestration : plugins, agents, filtres, processus | SemanticKernel |
| **MCP (Model Context Protocol)** | Standard de connexion outils-modèles — le LLM découvre vos outils dynamiquement | SemanticKernel |
| **Whisper / STT** | Speech-to-Text : transcrire l'audio en texte avec timestamps | Audio |
| **TTS** | Text-to-Speech : synthétiser la voix depuis du texte | Audio |
| **ComfyUI** | Interface visuelle pour chaîner les modèles génératifs en workflows | Image, Video |
| **Playwright** | Framework de test E2E pour applications web GenAI | Playwright-OWUI |
