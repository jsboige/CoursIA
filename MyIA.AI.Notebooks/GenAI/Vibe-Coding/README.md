# Vibe-Coding - Ateliers IA Generative pour le Developpement

Ce repertoire contient les ressources pedagogiques pour apprendre le "vibe-coding" avec des assistants IA generatifs. Le contenu couvre deux outils majeurs : **Claude Code** (Anthropic) et **Roo Code**, ainsi qu'une documentation introductive sur l'IA generative.

## Structure du repertoire

```
Vibe-Coding/
├── Claude-Code/          # Ateliers Claude Code (5 modules)
├── Roo-Code/             # Ateliers Roo Code (5 modules + avances)
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

## Documentation commune

Le repertoire `docs/` contient :

| Document | Description |
|----------|-------------|
| [INTRO-GENAI.md](docs/INTRO-GENAI.md) | Introduction pratique a l'IA generative |
| [claude-code/](docs/claude-code/) | Documentation Claude Code (installation, concepts, aide-memoire) |
| [roo-code/](docs/roo-code/) | Documentation Roo Code (installation, guide) |
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
| **Agents paralleles** | Jusqu'a 10 | Sequentiel |
| **MCP** | Support complet | Partiel |
| **Skills/Commands** | Ecosystem standardise | Configuration manuelle |
| **Courbe d'apprentissage** | Moyenne | Facile |
| **Ideal pour** | Projets complexes | Debutants |

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

Ce contenu pedagogique provient de la formation ECE 2026 sur l'IA generative.

---

*Version 1.0.0 - Fevrier 2026*
