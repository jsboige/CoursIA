# Ateliers Claude Code

Bienvenue dans les ateliers pratiques pour **Claude Code**, l'assistant de codage agentique développé par Anthropic.

## Objectifs de la formation

Cette formation vous permettra de :

- Maîtriser Claude Code (CLI et Extension VS Code)
- Utiliser efficacement les agents intégrés (Explore, Plan)
- Automatiser vos workflows de développement
- Créer des Skills et Slash Commands personnalisés
- Configurer des intégrations MCP et Hooks avancés

## Prérequis

- **VS Code** installé (version 1.60.0+)
- **Node.js** 18+ (pour Claude Code CLI)
- Un compte **OpenRouter** avec une clé API
- Connaissances de base en programmation

## Structure des ateliers

| N° | Atelier | Durée | Niveau | Description |
|----|---------|-------|--------|-------------|
| 01 | [Découverte](01-decouverte/) | 2-3h | Débutant | Installation, sessions, @-mentions, CLAUDE.md |
| 02 | [Orchestration](02-orchestration-taches/) | 2-3h | Débutant+ | Agents Explore/Plan, recherche web |
| 03 | [Assistant Développeur](03-assistant-developpeur/) | 3h | Intermédiaire | /commit, /review, debug, refactoring |
| 04 | [Création de Code](04-creation-code/) | 3h | Intermédiaire | Génération projet, tests, documentation |
| 05 | [Automatisation Avancée](05-automatisation-avancee/) | 3-4h | Avancé | Skills, Subagents, MCP, Hooks |

**Durée totale estimée : 13-16 heures**

## Installation rapide

### 1. Installer Claude Code CLI

```bash
# Installation via npm (recommandée)
npm install -g @anthropic-ai/claude-code

# Vérifier l'installation
claude --version
```

### 2. Configurer OpenRouter

**Windows (PowerShell):**
```powershell
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE"
$env:ANTHROPIC_API_KEY = ""
```

**macOS/Linux:**
```bash
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE"
export ANTHROPIC_API_KEY=""
```

### 3. Installer l'extension VS Code

Recherchez "Claude Code" dans le marketplace VS Code et installez l'extension officielle Anthropic.

### 4. Vérifier la configuration

```bash
claude /status
```

## Préparation de l'environnement

Chaque participant dispose d'un espace de travail isolé. Pour préparer votre environnement :

```powershell
# Windows - Préparer tous les ateliers
.\Scripts\prepare-workspaces.ps1 -UserName "VotreNom"

# Pour un atelier spécifique
.\Scripts\prepare-workspaces.ps1 -UserName "VotreNom" -Workshop "01-decouverte"

# Nettoyer après la formation
.\Scripts\clean-workspaces.ps1 -UserName "VotreNom"
```

## Progression recommandée

```
Semaine 1: Ateliers 01 + 02 (Bases et orchestration)
           - Installation et configuration
           - Première session interactive
           - Agents Explore et Plan

Semaine 2: Ateliers 03 + 04 (Développement pratique)
           - Workflow Git avec /commit et /review
           - Debug et refactoring
           - Génération de code et tests

Semaine 3: Atelier 05 (Automatisation avancée)
           - Slash Commands personnalisés
           - Skills et Subagents
           - Configuration MCP et Hooks
```

## Fonctionnalités couvertes par niveau

### Niveau Basique (Ateliers 01-02)

- Installation CLI + Extension VS Code
- Configuration OpenRouter multi-modèles
- Sessions interactives (`claude`, `claude -c`, `claude -p`)
- @-mentions et références de fichiers
- Commande `/init` et fichier CLAUDE.md
- Modèles (sonnet, opus, haiku)
- Agents intégrés (Explore, Plan)

### Niveau Intermédiaire (Ateliers 03-04)

- Slash commands `/commit` et `/review`
- Permissions et modes de travail
- Outils Read, Write, Edit, Bash
- Recherche avec Glob et Grep
- Génération de code structuré
- Tests automatisés

### Niveau Avancé (Atelier 05)

- Slash commands personnalisés (`.claude/commands/`)
- Skills avec fichier SKILL.md
- Subagents (jusqu'à 10 parallèles)
- Serveurs MCP (searxng, playwright, github)
- Hooks (PreToolUse, PostToolUse)
- Configuration projet avancée

## Notebooks Interactifs CLI

Une serie de **5 notebooks Jupyter** pour apprendre et experimenter avec `claude -p` en ligne de commande.

| Notebook | Duree | Description |
|----------|-------|-------------|
| [01-Claude-CLI-Bases](notebooks/01-Claude-CLI-Bases.ipynb) | 20 min | Installation, premiere commande, modeles |
| [02-Claude-CLI-Sessions](notebooks/02-Claude-CLI-Sessions.ipynb) | 25 min | Gestion des conversations et sessions |
| [03-Claude-CLI-References](notebooks/03-Claude-CLI-References.ipynb) | 25 min | @-mentions, contexte fichiers, CLAUDE.md |
| [04-Claude-CLI-Agents](notebooks/04-Claude-CLI-Agents.ipynb) | 30 min | Agents Explore, Plan, subagents |
| [05-Claude-CLI-Automatisation](notebooks/05-Claude-CLI-Automatisation.ipynb) | 30 min | Pipelines, scripts, hooks |

**Duree totale : 2h10** | [README des notebooks](notebooks/README.md)

## Documentation complémentaire

### Guides dans ce dépôt

| Document | Emplacement | Description |
|----------|-------------|-------------|
| **Introduction** | [docs/claude-code/INTRO-CLAUDE-CODE.md](../docs/claude-code/INTRO-CLAUDE-CODE.md) | Concepts et fonctionnalités |
| **Installation** | [docs/claude-code/INSTALLATION-CLAUDE-CODE.md](../docs/claude-code/INSTALLATION-CLAUDE-CODE.md) | Guide complet avec OpenRouter |
| **Modeles alternatifs** | [docs/claude-code/INSTALLATION-CLAUDE-CODE.md#modeles-alternatifs-via-openrouter](../docs/claude-code/INSTALLATION-CLAUDE-CODE.md#modeles-alternatifs-via-openrouter) | GLM-4.7, Qwen3 Coder via OpenRouter |
| **Aide-mémoire** | [docs/claude-code/CHEAT-SHEET.md](../docs/claude-code/CHEAT-SHEET.md) | Commandes essentielles |
| **Concepts avancés** | [docs/claude-code/CONCEPTS-AVANCES.md](../docs/claude-code/CONCEPTS-AVANCES.md) | Skills, Subagents, Hooks, MCP |
| **Comparaison** | [docs/claude-code/COMPARAISON-CLAUDE-ROO.md](../docs/claude-code/COMPARAISON-CLAUDE-ROO.md) | Claude Code vs Roo Code |

### Documentation officielle

- [Claude Code Docs](https://code.claude.com/docs)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [Agent Skills](https://code.claude.com/docs/en/skills)
- [MCP Documentation](https://code.claude.com/docs/en/mcp)

### Ressources communautaires

- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code) - Liste curatée de skills et hooks
- [SkillsMP Marketplace](https://skillsmp.com/) - Marketplace de skills
- [Best Practices](https://www.anthropic.com/engineering/claude-code-best-practices) - Guide officiel Anthropic

## Comparaison avec Roo Code

Si vous avez déjà utilisé les [Ateliers Roo Code](../Ateliers-roo-code/), voici les principales différences :

| Aspect | Claude Code | Roo Code |
|--------|-------------|----------|
| **Interface** | CLI + VS Code | VS Code uniquement |
| **Agents parallèles** | Jusqu'à 10 | Séquentiel |
| **MCP** | Support complet | Partiel |
| **Skills/Commands** | Ecosystem standardisé | Configuration manuelle |
| **Courbe d'apprentissage** | Moyenne | Facile |
| **Idéal pour** | Projets complexes | Débutants |

**Recommandation** :
- **Débutants complets** : Commencer avec [Roo Code](../Ateliers-roo-code/)
- **Développeurs** : Claude Code offre plus de puissance
- **Les deux peuvent coexister** dans le même environnement VS Code

## Aide-Mémoire rapide

### Commandes CLI essentielles

```bash
# Session interactive
claude

# Query ponctuelle
claude -p "explique ce code"

# Continuer dernière conversation
claude -c

# Avec modèle spécifique
claude --model opus

# Générer CLAUDE.md
claude
> /init

# Créer un commit
claude
> /commit

# Analyser les changements
claude
> /review
```

### Raccourcis VS Code

| Raccourci | Action |
|-----------|--------|
| `Cmd/Ctrl + Esc` | Toggle Claude Code |
| `Cmd/Ctrl + Shift + Esc` | Nouvelle conversation |
| `Alt + K` | Insérer @-mention |

## Résolution de problèmes

| Problème | Solution |
|----------|----------|
| `command not found: claude` | Vérifier PATH, réinstaller avec `npm install -g` |
| `Authentication failed` | Vérifier `ANTHROPIC_AUTH_TOKEN` et `ANTHROPIC_BASE_URL` |
| Extension ne se connecte pas | Activer "Disable Login Prompt" dans les settings |
| MCP timeout | Augmenter la variable `MCP_TIMEOUT` |

**Guide complet** : [INSTALLATION-CLAUDE-CODE.md](../docs/claude-code/INSTALLATION-CLAUDE-CODE.md#résolution-de-problèmes)

## Support

- **Questions techniques** : Consultez la [documentation](../docs/claude-code/)
- **Issues Claude Code** : [github.com/anthropics/claude-code/issues](https://github.com/anthropics/claude-code/issues)
- **Formation ECE** : Contactez votre formateur

---

**Bon apprentissage avec Claude Code !**

*Version 1.0.0 - Janvier 2026*
