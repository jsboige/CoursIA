# GenAI - Ecosysteme IA Generative

<!-- CATALOG-STATUS
series: GenAI
pedagogical_count: 121
breakdown: Audio=30, SemanticKernel=20, Image=17, Video=16, Texte=11, 00-GenAI-Environment=6, PostTraining=6, FineTuning=5, Vibe-Coding=5, CaseStudies=4, root=1
maturity: PRODUCTION=85, BETA=26, ALPHA=5, TEMPLATE=3, DRAFT=2
-->

Ce parcours vous forme a la maitrise de l'IA generative dans toute sa diversite : generer des images, synthetiser la voix, composer de la musique, produire des videos, orchestrer des agents autonomes, et deployer des applications en production. Chaque modalite suit une progression en quatre niveaux, du premier pas avec une API jusqu'aux pipelines multi-modeles de production. Les decomptes par sous-domaine et la maturite de chaque notebook se lisent dans le marqueur `CATALOG-STATUS` en tete de ce fichier.

## Pourquoi ce parcours ?

L'IA generative a transforme la creation de contenu en 2024-2026. Un developpeur qui sait piloter DALL-E pour generer une illustration, Whisper pour transcrire un podcast, MusicGen pour composer un fond sonore, et orchestrer tout cela via des agents autonomes, possede un avantage decisive sur le marche. Ce parcours ne se contente pas d'enumerer des APIs : il vous apprend a **comprendre** les modeles (leurs forces, leurs limites, leurs pieges), a **comparer** les approches (open-source vs cloud, local vs API), et a **combiner** les modalites dans des pipelines reels.

## Structure

```text
GenAI/
├── 00-GenAI-Environment/    # Setup et configuration (6 notebooks)
├── Image/                   # Generation d'images (16 notebooks)
├── Audio/                   # Speech, TTS, musique, separation (30 notebooks)
├── Video/                   # Generation et comprehension video (16 notebooks)
├── Texte/                   # LLMs et generation de texte (11 notebooks)
├── SemanticKernel/          # Microsoft Semantic Kernel (20 notebooks)
├── FineTuning/              # Fine-tuning de modeles : LoRA/QLoRA/SFT/DPO (5 notebooks)
├── PostTraining/            # Post-training SOTA : SFT/RLHF/DPO/GRPO/RLVR (6 notebooks)
├── CaseStudies/             # Etudes de cas etudiants (4 notebooks)
├── Playwright-OWUI/         # Tests E2E Playwright (5 modules, 30+ tests)
└── Vibe-Coding/             # Tutorials Claude Code et Roo Code (5 notebooks)
```

---

## Les sous-domaines

### 00-GenAI-Environment - Votre point de depart

Avant de generer la moindre image ou le moindre son, il faut configurer l'environnement : cles API, services Docker, et validation que tout fonctionne. Ces 6 notebooks sont le passage obligatoire. Ils couvrent le setup Python, la gestion des conteneurs Docker (ComfyUI, Whisper, MusicGen), la configuration des endpoints API, et un test complet de validation.

[README complet](00-GenAI-Environment/README.md) | 6 notebooks | ~4h

---

### Image - Generer, editer et orchestrer des images

On commence par les fondamentaux : appeler DALL-E 3 et GPT-5 pour generer des images depuis un prompt texte, puis manipuler ces images avec PIL et OpenCV. Le niveau avance introduit les modeles open-source heberges localement (Qwen Image Edit pour l'edition, FLUX pour la qualite, Stable Diffusion 3.5 pour la production, Z-Image/Lumina pour l'experimental). En orchestration, on compare les modeles entre eux et on enchaine les workflows. Les applications metier montrent comment integrer tout cela dans des cas reels : contenu educatif, workflows creatifs, motifs decoratifs.

**Fil rouge** : construire un generateur de contenu visuel pour l'education (diagrammes scientifiques, illustrations pedagogiques, motifs decoratifs).

[README complet](Image/README.md) | 16 notebooks | ~6-8h

---

### Audio - Parler, ecouter, composer

Cette serie couvre le spectre complet de l'audio IA : reconnaissance vocale (Whisper V3, OpenAI API), synthese vocale (Kokoro, OpenAI TTS, Chatterbox), clonage de voix (XTTS v2), generation musicale (MusicGen, YuE), separation de sources (Demucs), et pipelines complets (podcast automatique, transcription batch, synchronisation audio-video). Le detail de chaque niveau et les services utilises se trouve dans le [README Audio](Audio/README.md).

**Fil rouge** : produire un podcast automatique avec voix synthetique personnalisee et fond musical genere.

[README complet](Audio/README.md) | 30 notebooks | ~14-16h

---

### Video - Comprendre, generer et produire

La video est la modalite la plus exigeante en ressources mais aussi la plus spectaculaire. On commence par comprendre des videos existantes (GPT-5, Qwen-VL), puis on genere (HunyuanVideo, Wan, Sora). Les notebooks d'orchestration combinent comprehension et generation dans des workflows de production video. La serie couvre aussi le surcadrage d'images (ESRGAN) et la synchronisation audio-video.

**Fil rouge** : creer une video pedagogique automatisee depuis un script texte.

[README complet](Video/README.md) | 16 notebooks | ~14h

---

### Texte - Maitriser les LLMs et les APIs OpenAI

Le texte est le socle de toute interaction avec l'IA generative. Cette serie va au-dela du simple "prompt engineering" : structured outputs pour des reponses fiables, function calling pour connecter les LLMs a vos outils, RAG pour injecter de la connaissance externe, code interpreter pour l'execution dynamique, et les modeles de raisonnement (o-series) pour les taches complexes. Les derniers notebooks couvrent les patterns de production et les LLMs locaux.

[README complet](Texte/README.md) | 11 notebooks | ~10h

---

### SemanticKernel - Orchestration agentique avec Microsoft

Semantic Kernel est le SDK Microsoft pour construire des applications agentiques. Il fournit les briques pour orchestrer des LLMs avec des plugins, des agents, des filtres, des vector stores, et des processus multi-etapes. Cette serie couvre le SDK en Python et en C# (.NET Interactive), avec une progression qui va des fundamentals aux patterns avances (MCP, multi-modalite, interop CLR).

[README complet](SemanticKernel/README.md) | 20 notebooks | ~20h

---

### Vibe-Coding - Developper avec des agents IA

Le "vibe coding" est la competence la plus demandee de 2026 : decrire ce qu'on veut a un agent IA et le laisser ecrire, tester et deployer le code. Cette serie couvre les deux outils majeurs du marche : Claude Code (Anthropic) et Roo Code (communautaire). Chaque outil est aborde en 5 modules, de la decouverte a l'automatisation avancee.

[README complet](Vibe-Coding/README.md) | 10 modules | ~30h

---

### Playwright-OWUI - Tester les applications GenAI

Les applications GenAI doivent etre testees rigoureusement. Cette serie utilise Playwright pour ecrire des tests de bout en bout sur Open WebUI, une interface reelle de chat LLM. On y apprend la navigation, l'authentification, le streaming de reponses, le RAG, les outils MCP, et le deploiement CI/CD.

[README complet](Playwright-OWUI/README.md) | 5 modules, 30+ tests | ~14h

---

### CaseStudies - Projets etudiants

Projets realises par les etudiants : generation d'images style Barbie/Shrek, generateur de recettes, chatbot medical educatif, challenges style Fort Boyard. Ces notebooks illustrent la diversite des applications possibles apres le parcours.

[README complet](CaseStudies/README.md) | 4 notebooks

---

## Progression recommandee

### Decouvreur (initiation rapide, ~20h)

Commencez par `00-GenAI-Environment/` pour le setup, puis choisissez une modalite qui vous interesse : `Image/01-Foundation/` pour le visuel, ou `Audio/01-Foundation/` pour le son. L'objectif est de generer votre premier contenu en moins d'une journee.

### Praticien (maitrise multi-modale, ~50h)

Couvrez les quatre modalites de base (Image, Audio, Video, Texte) au niveau Foundation, puis approfondissez une ou deux modalites au niveau Advanced. Vous serez capable de combiner texte, image et son dans un projet coherent.

### Agentiste (full-stack agentic, ~90h)

Ajoutez SemanticKernel pour l'orchestration et Vibe-Coding pour le developpement assiste. Vous construirez des pipelines multi-modeles autonomes et des agents capables de chaines de traitement complexes.

### Expert (avec production, ~120h+)

Compltez avec Playwright pour les tests E2E et les notebooks Applications de chaque modalite. Vous maitrisez le cycle complet : generation, orchestration, tests, deploiement.

---

## Demarrage rapide

### 1. Configuration

```bash
cd MyIA.AI.Notebooks/GenAI
cp .env.example .env
# Editez .env avec vos cles API (token fourni par l'enseignant)
```

### 2. Installation

```bash
pip install -r requirements.txt
python -c "import jupyter_client; print('Jupyter OK')"
```

### 3. Premier pas

Lancez Jupyter Lab et commencez par `00-GenAI-Environment/00-1-Environment-Setup.ipynb`. Ce notebook verifie que votre environnement est operationnel et guide la configuration des services.

---

## Authentification ComfyUI

Les services GenAI locaux (Qwen Image Edit, Z-Image, Whisper, etc.) sont proteges par authentification Bearer Token.

1. **Obtenir le token** : contactez votre enseignant
2. **Configuration** : ajoutez `COMFYUI_BEARER_TOKEN` dans `.env`
3. **Utilisation** : les notebooks chargent automatiquement les credentials via `comfyui_client.py`

Tous les notebooks supportent la graceful degradation : sans token, ils utilisent les APIs cloud en fallback.

---

## Variables d'environnement

Les cles essentielles dans `.env` :

| Variable | Usage | Requis pour |
| ---------- | ------- | ------------- |
| `OPENAI_API_KEY` | DALL-E 3, GPT-5, Whisper, TTS | Image, Audio, Texte |
| `ANTHROPIC_API_KEY` | Claude Vision | Video |
| `HUGGINGFACE_TOKEN` | Modeles HF open-source | Image, Video |
| `COMFYUI_BEARER_TOKEN` | Services locaux ComfyUI | Image (local), Video |

Template complet : [`.env.example`](.env.example)

---

## Outils de validation

```bash
# Validation structure (metadata, outputs, kernel)
python scripts/notebook_tools/notebook_tools.py validate <path>

# Execution complete (Papermill)
python scripts/notebook_tools/notebook_tools.py execute <path>

# Analyse structure (stats cellules, outputs)
python scripts/notebook_tools/notebook_tools.py analyze <path>
```

---

## Acquis d'apprentissage

A l'issue du parcours, vous etes capable de :

- **Selectionner le bon modele** pour une tache donnee — connaitre les forces/faiblesses des modeles cloud (DALL-E, GPT, Whisper, Sora) face aux modeles open-source locaux (FLUX, SD 3.5, Qwen-Image, Whisper-local, MusicGen, HunyuanVideo) et arbitrer sur cout / qualite / souverainete des donnees.
- **Combiner les modalites** dans des pipelines coherents — texte vers image, image vers video, audio vers texte vers audio, sans casser la chaine d'inference ni perdre le contexte semantique.
- **Orchestrer des agents** via Semantic Kernel (plugins, agents, filtres, vector stores, processus multi-etapes) en Python et en C#/.NET Interactive.
- **Industrialiser une application GenAI** avec authentification ComfyUI, graceful degradation cloud/local, tests E2E Playwright sur Open WebUI, et integration MCP.
- **Developper avec des agents IA** (Claude Code, Roo Code) en mode "vibe coding" — formuler les besoins, iterer sur les diffs, automatiser les workflows de developpement.
- **Evaluer la qualite** des sorties generees — metriques objectives (FID, WER, BLEU), validation subjective structuree, comparaison de pipelines.

## Fil rouge transverse

Les sous-domaines ne sont pas isoles. Un projet final typique enchaine :

1. **Texte** produit un script structure (function calling, structured outputs)
2. **Image** illustre les concepts (DALL-E, FLUX, ou Qwen Image Edit pour les retouches)
3. **Audio** synthetise la narration (Kokoro/OpenAI TTS) + fond musical (MusicGen)
4. **Video** assemble le tout (HunyuanVideo pour la generation, Demucs pour la sync A/V)
5. **SemanticKernel** orchestre le pipeline en agents autonomes
6. **Playwright-OWUI** teste l'interface utilisateur du produit final

C'est ce parcours d'integration qui differencie une demonstration jouet d'un produit deployable.

## FAQ

### Faut-il un GPU pour cette serie ?

Non. Les notebooks Image utilisent ComfyUI heberge sur un serveur distant (RTX 3090 dediee, accessible via API). Les notebooks Texte utilisent les API cloud (OpenAI, Anthropic). Les notebooks Audio et Video peuvent tourner en CPU pour les demos (avec une latence plus elevee). Si vous avez un GPU local, les notebooks montrent aussi comment l'utiliser.

### Quels sont les couts API attendus ?

La serie est concue pour minimiser les couts. Les notebooks Texte utilisent principalement GPT-4o-mini (~0.15$/1M input tokens) et GPT-4o (~2.50$/1M input tokens). Les notebooks Image utilisent DALL-E 3 uniquement pour les exercices (les exemples utilisent ComfyUI/Qwen gratuit). Budget estime : **5-15$ total** pour l'ensemble de la serie, sauf appels iteratifs intensifs.

### Quelle est la difference entre ComfyUI et DALL-E ?

**ComfyUI** est un serveur open-source heberge localement qui execute des modeles open-source (FLUX, SD 3.5, Qwen Image Edit). Avantages : gratuit, controle total sur les parametres (seed, steps, CFG), pipelines personnalisables. **DALL-E 3** est l'API cloud d'OpenAI. Avantages : qualite elevee par defaut, simplicite d'usage (un appel API = une image). La serie montre les deux et vous apprend a choisir selon le contexte.

### Peut-on suivre cette serie en parallele d'une autre ?

Oui. Chaque sous-domaine (Image, Audio, Video, Texte, SemanticKernel) est independant. Le parcours recommande est de commencer par **Texte** (necessaire pour comprendre les prompts utilises partout) puis de choisir un sous-domaine selon votre projet.

### Erreur ComfyUI 401 Unauthorized

Verifiez que `COMFYUI_BEARER_TOKEN` est configure dans `.env`. Le token est disponible aupres de l'enseignant. Sans token, les notebooks basculent en mode cloud (DALL-E/OpenAI) si `OPENAI_API_KEY` est present.

### Docker services ne demarrent pas

Verifiez que Docker Desktop est en cours d'execution et que les conteneurs sont actifs :

```bash
python scripts/genai-stack/genai.py docker status
```

Si les services sont DOWN, relancez avec `genai.py docker start`. Details : [docs/genai/genai-services.md](../../docs/genai/genai-services.md).

Pour le troubleshooting avance (timeout Papermill, OOM GPU, .NET), consultez le README de chaque sous-domaine.

## Concepts cles

| Concept | Description | Serie principale |
|---------|-------------|-----------------|
| **Latent space** | Espace comprime ou le modele "pense" — toute generation commence ici | Image, Video |
| **Diffusion** | Processus iteratif : bruit → image/audio/video en N etapes | Image, Video, Audio |
| **VAE / VAE-Decoder** | Encodeur/decodeur entre pixel space et latent space | Image |
| **CFG (Classifier-Free Guidance)** | Parametre controlant la fidelite au prompt vs liberte creatrice | Image |
| **LoRA / QLoRA** | Adaptateurs legers pour specialiser un modele sans re-entrainer tout le poids | FineTuning |
| **DPO / RLHF** | Alignement des modeaux sur les preferences humaines | PostTraining |
| **RAG** | Retrieval-Augmented Generation : injecter des documents externes dans le contexte LLM | Texte |
| **Function Calling** | Le LLM appelle vos fonctions — passerelle vers les outils et APIs | Texte |
| **Structured Outputs** | Forcer le LLM a respecter un schema JSON precis | Texte |
| **SFT / GRPO / RLVR** | Post-training : Supervised Fine-Tuning, Group Relative Policy Optimization, RL with Verifiable Rewards | PostTraining |
| **Semantic Kernel** | SDK d'orchestration : plugins, agents, filtres, processus | SemanticKernel |
| **MCP (Model Context Protocol)** | Standard de connexion outils-modeles — le LLM decouvre vos outils dynamiquement | SemanticKernel |
| **Whisper / STT** | Speech-to-Text : transcrire l'audio en texte avec timestamps | Audio |
| **TTS** | Text-to-Speech : synthetiser la voix depuis du texte | Audio |
| **ComfyUI** | Interface visuelle pour chainer les modeaux generatifs en workflows | Image, Video |
| **Playwright** | Framework de test E2E pour applications web GenAI | Playwright-OWUI |

## Cross-series Bridges

### Interne GenAI

| Serie | Lien | Connection |
|-------|------|------------|
| [Image](Image/README.md) | Source visuelle pour Video | Le pipeline Video/03-2 enchaine generation d'images puis animation ; SVD (Video/02-4) anime une image existante |
| [Audio](Audio/README.md) | Sync A/V + podcast | Audio/04-4 synchronise audio et video ; le pipeline podcast (Audio/03-2) enchaine STT, LLM (Texte) et TTS |
| [Texte](Texte/README.md) | Prompts et APIs | Les prompts structures (Texte/2) guident toute generation (Image, Audio, Video) ; function calling (Texte/4) pilote les APIs multimodales |
| [SemanticKernel](SemanticKernel/README.md) | Orchestration | Les pipelines multi-modeles de chaque serie suivent les patterns d'orchestration Semantic Kernel |

### Externe

| Serie | Lien | Connection |
|-------|------|-------------|
| [QuantConnect](../QuantConnect/README.md) | Trading algorithmique | L'analyse de sentiment par LLM (Texte/8_Reasoning_Models) alimente les strategies de trading du notebook QC-13 |
| [Probas](../Probas/README.md) | Modeles probabilistes | Les VAE et diffusion models (Image/02-Advanced, Video/02-Advanced) partagent les fondements probabilistes couverts dans Probas/Infer |

### Lecture transversale

[La mer qui monte](../../docs/grothendieckian-lens.md) : une grille de lecture grothendieckienne du depot — GenAI comme versant *simulation* (generer, calculer, experimenter) face au versant *preuve* des series formelles.
