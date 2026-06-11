# Vibe-Coding - Ateliers IA Generative pour le Developpement

<!-- CATALOG-STATUS
series: GenAI-Vibe-Coding
pedagogical_count: 5
breakdown: Vibe-Coding=5
maturity: PRODUCTION=4, BETA=1
-->

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Claude Discovery](Claude-Code/01-decouverte/README.md)

Cette serie couvre les ateliers de **vibe-coding** : decrire ce que vous voulez construire en langage naturel, et l'IA ecrit le code. Deux assistants majeurs sont couverts (Claude Code et Roo Code), avec des exercices progressifs allant de la decouverte a l'automatisation avancee, plus un module d'agents autonomes (Claw Systems).

## Structure du repertoire

```text
Vibe-Coding/
├── Claude-Code/          # Ateliers Claude Code (5 modules)
├── Roo-Code/             # Ateliers Roo Code (5 modules + avances)
├── Claw-Systems/         # Agents IA autonomes (NanoClaw, OpenClaw)
└── docs/                 # Documentation commune et introductions
```

## Claude Code - Ateliers

Assistant de codage agentique developpe par Anthropic. Interface CLI + Extension VS Code.

| Module | Nom | Duree | Niveau | Description |
|--------|-----|-------|--------|-------------|
| 01 | [Decouverte](Claude-Code/01-decouverte/) | 2-3h | Debutant | Installation, sessions, @-mentions, CLAUDE.md |
| 02 | [Orchestration](Claude-Code/02-orchestration-taches/) | 2-3h | Debutant+ | Agents Explore/Plan, recherche web |
| 03 | [Assistant Developpeur](Claude-Code/03-assistant-developpeur/) | 3h | Intermediaire | /commit, /review, debug, refactoring |
| 04 | [Creation de Code](Claude-Code/04-creation-code/) | 3h | Intermediaire | Generation projet, tests, documentation |
| 05 | [Automatisation Avancee](Claude-Code/05-automatisation-avancee/) | 3-4h | Avance | Skills, Subagents, MCP, Hooks |

**Duree totale : 13-16 heures**

### Ressources supplementaires Claude Code

- `Scripts/` - Scripts PowerShell de preparation des workspaces
- `workspaces/` - Espaces de travail par participant
- `docs/` - Documentation specifique Claude Code

### Installation Claude Code

```bash
# Installation CLI
npm install -g @anthropic-ai/claude-code

# Configuration OpenRouter (PowerShell)
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE"
```

## Roo Code - Ateliers

Framework de codage IA avec interface VS Code uniquement. Ideal pour les debutants.

| Module | Nom | Contenu |
|--------|-----|---------|
| 01 | [Decouverte](Roo-Code/01-decouverte/) | Premiers pas, conversations, vision |
| 02 | [Orchestration des taches](Roo-Code/02-orchestration-taches/) | Gestion des taches et workflows |
| 03 | [Assistant Pro](Roo-Code/03-assistant-pro/) | Mode assistant professionnel |
| 04 | [Creation de contenu](Roo-Code/04-creation-contenu/) | Generation de code et contenu |
| 05 | [Projets avances](Roo-Code/05-projets-avances/) | Projets complexes et integration |

### Ressources supplementaires Roo Code

- `Ateliers avances/` - Modules supplementaires avances
- `Corrections/` - Solutions des exercices
- `Demo-Roo-Capabilities/` - Demonstrations des capacites Roo
- `Scripts/` - Scripts de preparation
- `workspaces/` - Espaces de travail par participant
- `docs/` - Documentation specifique Roo Code

### Preparation de l'environnement

```powershell
# Creer son workspace
./Scripts/prepare-workspaces.ps1 -UserName "VotreNom"

# Nettoyer apres la formation
./Scripts/clean-workspaces.ps1 -UserName "VotreNom"
```

## Claw Systems - Agents Autonomes

Plateformes d'agents IA conteneurises, self-hosted, operant de maniere autonome via Telegram et API.

| Document | Description |
|----------|-------------|
| [README](Claw-Systems/README.md) | Vue d'ensemble, comparaison avec Claude/Roo |
| [Architecture](Claw-Systems/docs/NanoClaw-Architecture.md) | Architecture technique NanoClaw |
| [Deploiement](Claw-Systems/docs/NanoClaw-Deploy.md) | Guide de deploiement Docker |
| [ASR Integration](Claw-Systems/docs/ASR-Integration.md) | Transcription vocale Whisper |

**Cas d'usage** : Agent Telegram avec transcription vocale, orchestration multi-agents, deploiement production.

## Documentation commune

Le repertoire `docs/` contient :

| Document | Description |
|----------|-------------|
| [INTRO-GENAI.md](docs/INTRO-GENAI.md) | Introduction pratique a l'IA generative |
| [Claude-Code/docs/](Claude-Code/docs/) | Documentation Claude Code (installation, concepts, aide-memoire) |
| [Roo-Code/docs/](Roo-Code/docs/) | Documentation Roo Code (installation, guide) |
| [activites/](docs/activites/) | Activites pedagogiques |
| [sessions/](docs/sessions/) | Sessions de formation |

### Guides disponibles

**Claude Code :**
- `INTRO-CLAUDE-CODE.md` - Concepts et fonctionnalites
- `INSTALLATION-CLAUDE-CODE.md` - Guide d'installation avec OpenRouter
- `CHEAT-SHEET.md` - Commandes essentielles
- `CONCEPTS-AVANCES.md` - Skills, Subagents, Hooks, MCP
- `COMPARAISON-CLAUDE-ROO.md` - Comparaison Claude Code vs Roo Code

**Roo Code :**
- `INSTALLATION-ROO.md` - Guide d'installation
- `ROO-GUIDED-PATH.md` - Parcours d'apprentissage guide

## Prerequis techniques

- **VS Code** 1.60.0+
- **Node.js** 18+ (pour Claude Code CLI)
- Un compte **OpenRouter** avec une cle API
- Connaissances de base en programmation

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Decrire** un projet en langage naturel et obtenir du code fonctionnel via l'IA
2. **Orchestrer** des workflows multi-agents (recherche, planification, execution)
3. **Automatiser** les taches courantes du developpeur (tests, documentation, deploiement)
4. **Configurer** des agents autonomes conteneurises (Claw Systems)

## FAQ

### Claude Code ne s'installe pas ou erreur `command not found`

Claude Code (modules [01](Claude-Code/01-decouverte/) a [05](Claude-Code/05-automatisation-avancee/)) s'installe via npm. Si erreur `claude: command not found` apres installation :

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

### Quelle difference entre Claude Code et Roo Code ?

| Critere | Claude Code | Roo Code |
|---------|-------------|----------|
| **Interface** | CLI + VS Code | VS Code uniquement |
| **Agents paralleles** | Jusqu'a 10 simultanes | Sequentiel |
| **MCP** | Support complet | Partiel |
| **Skills/Commands** | Ecosysteme standardise | Configuration manuelle |
| **Courbe d'apprentissage** | Moyenne | Facile |
| **OpenRouter** | Oui | Oui |

**Recommandation** : debutants complets -> commencer par Roo Code ([module 01](Roo-Code/01-decouverte/)) ; developpeurs -> Claude Code ([module 01](Claude-Code/01-decouverte/)) offre plus de puissance. Les deux coexistent dans le meme VS Code. Voir le tableau comparatif ci-dessus pour les differences detaillees.

### Erreur d'authentification OpenRouter ou "401 Unauthorized"

Les ateliers Claude Code et Roo Code utilisent OpenRouter comme fournisseur LLM. Si erreur 401 :

```powershell
# Verifier les variables d'environnement
$env:ANTHROPIC_BASE_URL    # doit etre "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN   # doit commencer par "sk-or-v1-..."
```

Points frequents :

- La cle OpenRouter doit etre active sur [openrouter.ai/keys](https://openrouter.ai/keys) avec des credits disponibles.
- Ne pas confondre cle OpenAI (`sk-...`) et cle OpenRouter (`sk-or-v1-...`) -- les deux commencent par `sk-` mais ne sont pas interchangeables.
- Le guide d'installation ([INSTALLATION-CLAUDE-CODE.md](Claude-Code/docs/INSTALLATION-CLAUDE-CODE.md)) detaille la configuration pas-a-pas.

### Les scripts PowerShell de preparation echouent

Les scripts `Scripts/prepare-workspaces.ps1` et `Scripts/clean-workspaces.ps1` (references dans les modules Claude Code et Roo Code) preparent les espaces de travail individuels. Si erreur :

```powershell
# Verifier la politique d'execution PowerShell
Get-ExecutionPolicy
# Si "Restricted", autoriser les scripts locaux
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser

# Executer depuis le bon repertoire
cd MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code
./Scripts/prepare-workspaces.ps1 -UserName "VotreNom"
```

Si `UserName` contient des espaces, l'entourer de guillemets. Les workspaces sont crees dans le dossier `workspaces/` de chaque sous-repertoire (Claude Code et Roo Code separent leurs espaces).

### NanoClaw / OpenClaw : comment deployer un agent autonome ?

Les Claw Systems ([README](Claw-Systems/README.md)) sont des agents IA conteneurises qui operent via Telegram et API. Pour demarrer :

1. Lire l'[Architecture](Claw-Systems/docs/NanoClaw-Architecture.md) pour comprendre les composants (LLM, ASR Whisper, Telegram bot).
2. Suivre le [Guide de deploiement](Claw-Systems/docs/NanoClaw-Deploy.md) pour Docker Compose.
3. Configurer l'[ASR Whisper](Claw-Systems/docs/ASR-Integration.md) si la transcription vocale est requise.

**Prerequis** : Docker + Docker Compose, un token Telegram Bot (`@BotFather`), une cle API LLM (OpenRouter ou OpenAI). Le deploiement complet tourne sur un VPS 4 GB RAM minimum.

### Peut-on faire les ateliers sans OpenRouter ?

Oui, partiellement. OpenRouter est le fournisseur par defaut car il aggrege plusieurs modeaux (Claude, GPT, Gemini) sous une seule cle. Alternatives :

- **API Anthropic directe** : `$env:ANTHROPIC_API_KEY = "sk-ant-..."` (sans `ANTHROPIC_BASE_URL`). Fonctionne avec les modeaux Claude uniquement.
- **API OpenAI directe** : configuree via les settings Claude Code (sans OpenRouter). Modeaux GPT uniquement.
- **Mode hors-ligne** : les modules [01](Claude-Code/01-decouverte/) et [02](Claude-Code/02-orchestration-taches/) contiennent des exercices de decouverte qui ne necessitent pas d'API (exploration de l'interface, configuration CLAUDE.md, gestion de sessions).

Le module [05](Claude-Code/05-automatisation-avancee/) (Skills, Subagents, MCP) necessite un LLM actif pour les demonstrations avancees.

---

*Version 1.0.0 - Fevrier 2026*
