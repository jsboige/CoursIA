# Vibe-Coding - Ateliers IA Generative pour le Développement

<!-- CATALOG-STATUS
series: GenAI-Vibe-Coding
pedagogical_count: 5
breakdown: Vibe-Coding=5
maturity: PRODUCTION=4, BETA=1
-->

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Claude Discovery](Claude-Code/01-decouverte/README.md)

Cette série couvre les ateliers de **vibe-coding** : décrire ce que vous voulez construire en langage naturel, et l'IA écrit le code. Deux assistants majeurs sont couverts (Claude Code et Roo Code), avec des exercices progressifs allant de la découverte a l'automatisation avancée, plus un module d'agents autonomes (Claw Systems).

## Structure du répertoire

```text
Vibe-Coding/
├── Claude-Code/          # Ateliers Claude Code (5 modules)
├── Roo-Code/             # Ateliers Roo Code (5 modules + avances)
├── Claw-Systems/         # Agents IA autonomes (NanoClaw, OpenClaw)
├── Memoire-Semantique-Qdrant/   # Backend mémoire sémantique (Qdrant, grounding)
└── docs/                 # Documentation commune et introductions
```

## Claude Code - Ateliers

Assistant de codage agentique développé par Anthropic. Interface CLI + Extension VS Code.

| Module | Nom | Durée | Niveau | Description |
|--------|-----|-------|--------|-------------|
| 01 | [Découverte](Claude-Code/01-decouverte/) | 2-3h | Débutant | Installation, sessions, @-mentions, CLAUDE.md |
| 02 | [Orchestration](Claude-Code/02-orchestration-taches/) | 2-3h | Débutant+ | Agents Explore/Plan, recherche web |
| 03 | [Assistant Developpeur](Claude-Code/03-assistant-developpeur/) | 3h | Intermédiaire | /commit, /review, debug, refactoring |
| 04 | [Création de Code](Claude-Code/04-creation-code/) | 3h | Intermédiaire | Génération projet, tests, documentation |
| 05 | [Automatisation Avancée](Claude-Code/05-automatisation-avancee/) | 3-4h | Avancé | Skills, Subagents, MCP, Hooks |

**Durée totale : 13-16 heures**

### Ressources supplémentaires Claude Code

- `Scripts/` - Scripts PowerShell de preparation des workspaces
- `workspaces/` - Espaces de travail par participant
- `docs/` - Documentation spécifique Claude Code

### Installation Claude Code

```bash
# Installation CLI
npm install -g @anthropic-ai/claude-code

# Configuration OpenRouter (PowerShell)
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE"
```

## Roo Code - Ateliers

Framework de codage IA avec interface VS Code uniquement. Idéal pour les débutants.

| Module | Nom | Contenu |
|--------|-----|---------|
| 01 | [Découverte](Roo-Code/01-decouverte/) | Premiers pas, conversations, vision |
| 02 | [Orchestration des tâches](Roo-Code/02-orchestration-taches/) | Gestion des tâches et workflows |
| 03 | [Assistant Pro](Roo-Code/03-assistant-pro/) | Mode assistant professionnel |
| 04 | [Création de contenu](Roo-Code/04-creation-contenu/) | Génération de code et contenu |
| 05 | [Projets avancés](Roo-Code/05-projets-avances/) | Projets complexes et integration |

### Ressources supplémentaires Roo Code

- `Ateliers avances/` - Modules supplémentaires avancés
- `Corrections/` - Solutions des exercices
- `Demo-Roo-Capabilities/` - Démonstrations des capacités Roo
- `Scripts/` - Scripts de preparation
- `workspaces/` - Espaces de travail par participant
- `docs/` - Documentation spécifique Roo Code

### Préparation de l'environnement

```powershell
# Creer son workspace
./Scripts/prepare-workspaces.ps1 -UserName "VotreNom"

# Nettoyer apres la formation
./Scripts/clean-workspaces.ps1 -UserName "VotreNom"
```

## Claw Systems - Agents Autonomes

Plateformes d'agents IA conteneurisés, self-hosted, opérant de manière autonome via Telegram et API.

| Document | Description |
|----------|-------------|
| [README](Claw-Systems/README.md) | Vue d'ensemble, comparaison avec Claude/Roo |
| [Architecture](Claw-Systems/docs/NanoClaw-Architecture.md) | Architecture technique NanoClaw |
| [Déploiement](Claw-Systems/docs/NanoClaw-Deploy.md) | Guide de déploiement Docker |
| [ASR Integration](Claw-Systems/docs/ASR-Integration.md) | Transcription vocale Whisper |

**Cas d'usage** : Agent Telegram avec transcription vocale, orchestration multi-agents, déploiement production.

## Mémoire Sémantique Qdrant - Infrastructure de Grounding

Le **backend de mémoire sémantique** qui donne aux agents de codage une mémoire long-terme et les ancre dans des faits vérifiables (grounding) : une base de données vectorielle Qdrant qui indexe conversations et code, interrogée par le sens. Là où les sections ci-dessus décrivent les front-ends agents, celle-ci documente l'infrastructure qui les alimente -- avec les incidents d'ops réels (dérives de montage, pertes de données, durcissement des sauvegardes) comme matière pédagogique.

| Document | Description |
|----------|-------------|
| [README](Memoire-Semantique-Qdrant/README.md) | Vue d'ensemble, pipeline, écosystème |
| [Pourquoi la mémoire sémantique](Memoire-Semantique-Qdrant/docs/01-Pourquoi-Memoire-Semantique.md) | Grounding, SDDD, RAG, sémantique vs lexical |
| [Infrastructure Qdrant](Memoire-Semantique-Qdrant/docs/02-Infrastructure-Qdrant.md) | Docker, stockage WSL2, quantization TurboQuant, anti-split-brain |
| [Utilisation et indexation](Memoire-Semantique-Qdrant/docs/03-Utilisation-MCP-Indexation.md) | MCP, indexation code + conversations, requêtes |
| [Incidents et leçons](Memoire-Semantique-Qdrant/docs/04-Incidents-et-Lecons.md) | War-stories d'ops : dérive de montage, perte de données, sauvegardes |

**Cas d'usage** : donner à un assistant de codage une mémoire interrogeable par le sens, partagée entre machines, robuste aux pannes.

## Documentation commune

Le répertoire `docs/` contient :

| Document | Description |
|----------|-------------|
| [INTRO-GENAI.md](docs/INTRO-GENAI.md) | Introduction pratique a l'IA générative |
| [Claude-Code/docs/](Claude-Code/docs/) | Documentation Claude Code (installation, concepts, aide-memoire) |
| [Roo-Code/docs/](Roo-Code/docs/) | Documentation Roo Code (installation, guide) |
| [activites/](docs/activites/) | Activités pédagogiques |
| [sessions/](docs/sessions/) | Sessions de formation |

### Guides disponibles

**Claude Code :**
- `INTRO-CLAUDE-CODE.md` - Concepts et fonctionnalités
- `INSTALLATION-CLAUDE-CODE.md` - Guide d'installation avec OpenRouter
- `CHEAT-SHEET.md` - Commandes essentielles
- `CONCEPTS-AVANCES.md` - Skills, Subagents, Hooks, MCP
- `COMPARAISON-CLAUDE-ROO.md` - Comparaison Claude Code vs Roo Code

**Roo Code :**
- `INSTALLATION-ROO.md` - Guide d'installation
- `ROO-GUIDED-PATH.md` - Parcours d'apprentissage guide

## Prérequis techniques

- **VS Code** 1.60.0+
- **Node.js** 18+ (pour Claude Code CLI)
- Un compte **OpenRouter** avec une clé API
- Connaissances de base en programmation

## Objectifs d'apprentissage

A l'issue de cette série, vous serez capable de :

1. **Décrire** un projet en langage naturel et obtenir du code fonctionnel via l'IA
2. **Orchestrer** des workflows multi-agents (recherche, planification, execution)
3. **Automatiser** les tâches courantes du développeur (tests, documentation, déploiement)
4. **Configurer** des agents autonomes conteneurisés (Claw Systems)

## FAQ

### Claude Code ne s'installe pas ou erreur `command not found`

Claude Code (modules [01](Claude-Code/01-decouverte/) a [05](Claude-Code/05-automatisation-avancee/)) s'installe via npm. Si erreur `claude: command not found` après installation :

```bash
# Verifier Node.js (18+ requis)
node --version

# Installer globalement
npm install -g @anthropic-ai/claude-code

# Verifier l'installation
claude --version

# Si toujours introuvable, verifier le PATH npm
npm config get prefix
# Ajouter au PATH si necessaire (Windows)
# $env:PATH += ";$(npm config get prefix)"
```

Si vous utilisez VS Code uniquement (sans CLI), l'extension Claude Code dans le Marketplace suffit. Le module [01](Claude-Code/01-decouverte/) couvre les deux modes d'installation.

### Quelle différence entre Claude Code et Roo Code ?

| Critère | Claude Code | Roo Code |
|---------|-------------|----------|
| **Interface** | CLI + VS Code | VS Code uniquement |
| **Agents paralleles** | Jusqu'a 10 simultanés | Séquentiel |
| **MCP** | Support complet | Partiel |
| **Skills/Commands** | Écosystème standardisé | Configuration manuelle |
| **Courbe d'apprentissage** | Moyenne | Facile |
| **OpenRouter** | Oui | Oui |

**Recommandation** : débutants complets -> commencer par Roo Code ([module 01](Roo-Code/01-decouverte/)) ; développeurs -> Claude Code ([module 01](Claude-Code/01-decouverte/)) offre plus de puissance. Les deux coexistent dans le même VS Code. Voir le tableau comparatif ci-dessus pour les différences détaillées.

### Erreur d'authentification OpenRouter ou "401 Unauthorized"

Les ateliers Claude Code et Roo Code utilisent OpenRouter comme fournisseur LLM. Si erreur 401 :

```powershell
# Verifier les variables d'environnement
$env:ANTHROPIC_BASE_URL    # doit etre "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN   # doit commencer par "sk-or-v1-..."
```

Points fréquents :

- La clé OpenRouter doit être active sur [openrouter.ai/keys](https://openrouter.ai/keys) avec des credits disponibles.
- Ne pas confondre clé OpenAI (`sk-...`) et clé OpenRouter (`sk-or-v1-...`) -- les deux commencent par `sk-` mais ne sont pas interchangeables.
- Le guide d'installation ([INSTALLATION-CLAUDE-CODE.md](Claude-Code/docs/INSTALLATION-CLAUDE-CODE.md)) détaille la configuration pas-a-pas.

### Les scripts PowerShell de preparation échouent

Les scripts `Scripts/prepare-workspaces.ps1` et `Scripts/clean-workspaces.ps1` (references dans les modules Claude Code et Roo Code) préparent les espaces de travail individuels. Si erreur :

```powershell
# Verifier la politique d'execution PowerShell
Get-ExecutionPolicy
# Si "Restricted", autoriser les scripts locaux
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser

# Executer depuis le bon repertoire
cd MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code
./Scripts/prepare-workspaces.ps1 -UserName "VotreNom"
```

Si `UserName` contient des espaces, l'entourer de guillemets. Les workspaces sont créés dans le dossier `workspaces/` de chaque sous-répertoire (Claude Code et Roo Code séparent leurs espaces).

### NanoClaw / OpenClaw : comment déployer un agent autonome ?

Les Claw Systems ([README](Claw-Systems/README.md)) sont des agents IA conteneurisés qui opèrent via Telegram et API. Pour demarrer :

1. Lire l'[Architecture](Claw-Systems/docs/NanoClaw-Architecture.md) pour comprendre les composants (LLM, ASR Whisper, Telegram bot).
2. Suivre le [Guide de déploiement](Claw-Systems/docs/NanoClaw-Deploy.md) pour Docker Compose.
3. Configurer l'[ASR Whisper](Claw-Systems/docs/ASR-Integration.md) si la transcription vocale est requise.

**Prérequis** : Docker + Docker Compose, un token Telegram Bot (`@BotFather`), une clé API LLM (OpenRouter ou OpenAI). Le déploiement complet tourne sur un VPS 4 GB RAM minimum.

### Peut-on faire les ateliers sans OpenRouter ?

Oui, partiellement. OpenRouter est le fournisseur par défaut car il aggrege plusieurs modeaux (Claude, GPT, Gemini) sous une seule clé. Alternatives :

- **API Anthropic directe** : `$env:ANTHROPIC_API_KEY = "sk-ant-..."` (sans `ANTHROPIC_BASE_URL`). Fonctionne avec les modeaux Claude uniquement.
- **API OpenAI directe** : configurée via les settings Claude Code (sans OpenRouter). Modeaux GPT uniquement.
- **Mode hors-ligne** : les modules [01](Claude-Code/01-decouverte/) et [02](Claude-Code/02-orchestration-taches/) contiennent des exercices de découverte qui ne nécessitent pas d'API (exploration de l'interface, configuration CLAUDE.md, gestion de sessions).

Le module [05](Claude-Code/05-automatisation-avancee/) (Skills, Subagents, MCP) nécessite un LLM actif pour les démonstrations avancées.

---

*Version 1.0.0 - Février 2026*
