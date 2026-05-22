# GenAI - Ecosysteme IA Generative

<!-- CATALOG-STATUS
series: GenAI
pedagogical_count: 107
breakdown: Audio=28, SemanticKernel=20, Image=16, Video=16, Texte=11, 00-GenAI-Environment=6, Vibe-Coding=5, CaseStudies=4, =1
maturity: BETA=52, PRODUCTION=38, DRAFT=12, TEMPLATE=3, ALPHA=2
-->

Ce parcours vous forme a la maitrise de l'IA generative dans toute sa diversite : generer des images, synthetiser la voix, composer de la musique, produire des videos, orchestrer des agents autonomes, et deployer des applications en production. Chaque modalite suit une progression en quatre niveaux, du premier pas avec une API jusqu'aux pipelines multi-modeles de production.

**107 notebooks** | **9 sous-domaines** | **~90-100h** | **95%+ valides**

## Pourquoi ce parcours ?

L'IA generative a transforme la creation de contenu en 2024-2026. Un developpeur qui sait piloter DALL-E pour generer une illustration, Whisper pour transcrire un podcast, MusicGen pour composer un fond sonore, et orchestrer tout cela via des agents autonomes, possede un avantage decisive sur le marche. Ce parcours ne se contente pas d'enumerer des APIs : il vous apprend a **comprendre** les modeles (leurs forces, leurs limites, leurs pieges), a **comparer** les approches (open-source vs cloud, local vs API), et a **combiner** les modalites dans des pipelines reels.

## Structure

```text
GenAI/
├── 00-GenAI-Environment/    # Setup et configuration (6 notebooks)
├── Image/                   # Generation d'images (19 notebooks)
├── Audio/                   # Speech, TTS, musique, separation (28 notebooks)
├── Video/                   # Generation et comprehension video (16 notebooks)
├── Texte/                   # LLMs et generation de texte (11 notebooks)
├── SemanticKernel/          # Microsoft Semantic Kernel (20 notebooks)
├── CaseStudies/              # Etudes de cas etudiants (4 notebooks)
├── Playwright-OWUI/         # Tests E2E Playwright (5 modules, 30+ tests)
└── Vibe-Coding/             # Tutorials Claude Code et Roo Code
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

L'audio est souvent le parent pauvre des parcours IA, pourtant c'est l'une des modalites les plus accessibles et les plus impressionnantes. Cette serie couvre le spectre complet : reconnaissance vocale (Whisper V3, OpenAI API), synthese vocale (Kokoro, OpenAI TTS, Chatterbox), clonage de voix (XTTS v2), generation musicale (MusicGen, YuE), separation de sources (Demucs), et pipelines complets (podcast automatique, transcription batch, synchronisation audio-video).

**Fil rouge** : produire un podcast automatique avec voix synthetique personnalisee et fond musical genere.

[README complet](Audio/README.md) | 28 notebooks | ~14-16h

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

## Statut par sous-domaine

| Sous-domaine | Notebooks | Validation |
| ------------ | --------- | ---------- |
| 00-GenAI-Environment | 6 | 100% |
| Image | 16 | 100% |
| Audio | 28 | 100% |
| Video | 16 | 100% |
| Texte | 11 | 100% |
| SemanticKernel | 20 | 85% |
| CaseStudies | 4 | 100% |
| Playwright-OWUI | 5 modules | 100% |
| Vibe-Coding | 5 notebooks | 100% |

---

Architecture SDDD | Compatible MCP | Derniere mise a jour : mai 2026

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [ML](../ML/README.md) | Pipelines ML, evaluation | Les modeles generatifs s'evaluent avec les memes metriques (precision, FID, WER) et s'integrent dans des pipelines ML |
| [SemanticKernel](SemanticKernel/README.md) | Orchestration agentique | Semantic Kernel orchestre les LLMs et outils GenAI dans des workflows de production |
| [QuantConnect](../QuantConnect/README.md) | Trading algorithmique | L'analyse de sentiment par LLM (Texte/8_Reasoning_Models) alimente les strategies de trading |
| [RL](../RL/README.md) | Apprentissage par renforcement | Les agents RL peuvent utiliser des modeles generatifs comme recompenses (images, texte) |
| [Probas](../Probas/README.md) | Modeles probabilistes | Les VAE, diffusion models et Bayesian neural networks partagent les memes fondements probabilistes |
