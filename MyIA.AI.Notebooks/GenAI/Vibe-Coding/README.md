# Vibe-Coding - Ateliers IA Generative pour le Developpement

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Claude Discovery](Claude-Code/01-decouverte/README.md)

Bienvenue dans l'ère du **vibe-coding** - la compétence la plus demandée de 2026 ! Imaginez : vous décrivez ce que vous voulez construire en langage naturel, et l'IA écrit le code pour vous. Plus besoin de semaines de développement, mais des minutes pour transformer une idée en fonctionnalité réelle. Le vibe-coding révolutionne la programmation en rendant la barrière technique quasi invisible : votre seule limite est votre imagination.

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

## Comparaison Claude Code vs Roo Code

| Aspect | Claude Code | Roo Code |
|--------|-------------|----------|
| **Interface** | CLI + VS Code | VS Code uniquement |
| **Agents parallèles** | Jusqu'à 10 | Séquentiel |
| **MCP** | Support complet | Partiel |
| **Skills/Commands** | Écosystème standardisé | Configuration manuelle |
| **Courbe d'apprentissage** | Moyenne | Facile |
| **Idéal pour** | Projets complexes | Débutants |

**Recommandation :**
- **Debutants complets** : Commencer avec Roo Code
- **Developpeurs** : Claude Code offre plus de puissance
- **Les deux peuvent coexister** dans le meme environnement VS Code

## Prerequis techniques

- **VS Code** 1.60.0+
- **Node.js** 18+ (pour Claude Code CLI)
- Un compte **OpenRouter** avec une cle API
- Connaissances de base en programmation

## Origine

## Ce que vous saurez faire

À travers ces ateliers pratiques, vous acquerrez la capacité de :

- **Décrire vos projets** en langage naturel et voir l'IA les transformer en code fonctionnel
- **Écrire, tester, debugger et déployer** des applications complètes grâce à l'assistance IA
- **Orchestrer des workflows complexes** en multipliant les agents intelligents
- **Générer automatiquement** la documentation, les tests et les configurations
- **Automatiser des tâches complexes** allant du simple script au déploiement en production

---

*Version 1.0.0 - Fevrier 2026*
