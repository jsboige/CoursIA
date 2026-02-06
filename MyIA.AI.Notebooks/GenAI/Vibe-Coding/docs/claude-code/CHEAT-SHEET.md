# Claude Code - Aide-Memoire Rapide

Guide de reference rapide pour Claude Code CLI et Extension VS Code.

> **Documentation officielle** : [code.claude.com/docs](https://code.claude.com/docs)

## Commandes CLI Essentielles

### Demarrage et Sessions

```bash
# Demarrer une session interactive
claude

# Demarrer avec une question initiale
claude "explique ce projet"

# Query ponctuelle (sans interactivite)
claude -p "liste les dependances"

# Continuer la derniere conversation
claude -c

# Reprendre une session specifique
claude -r "nom-session"

# Creer une nouvelle session a chaque fois
claude --fork-session
```

### Selection de Modele

```bash
# Modele par defaut (Sonnet)
claude

# Utiliser Opus (plus puissant)
claude --model opus

# Utiliser Haiku (plus rapide)
claude --model haiku

# Utiliser un modele specifique
claude --model claude-sonnet-4-5-20250929
```

### System Prompts

```bash
# Ajouter des instructions au prompt systeme
claude --append-system-prompt "Utilise toujours TypeScript"

# Remplacer completement le prompt systeme
claude --system-prompt "Tu es un expert Python"

# Charger un prompt depuis un fichier
claude -p --system-prompt-file ./custom-prompt.txt "query"
```

### Gestion des Permissions

```bash
# Demarrer en mode planification (pas d'execution)
claude --permission-mode plan

# Mode auto-accept (prudent!)
claude --permission-mode auto-accept

# Mode acceptEdits (accepte lectures et ecritures, demande pour Bash)
claude --permission-mode acceptEdits

# Autoriser certains outils sans confirmation
claude --allowedTools "Bash(npm run *)" "Read"
```

### Output et Formats

```bash
# Output JSON
claude -p "analyse ce fichier" --output-format json

# Output JSON streaming
claude -p "query" --output-format stream-json

# Limiter le nombre de tours
claude -p "query" --max-turns 5

# Budget maximum en USD
claude -p "query" --max-budget-usd 0.50
```

### Agents Personnalises

```bash
# Utiliser un agent defini dans .claude/agents/
claude --agent reviewer

# Definir des agents en ligne
claude --agents '{"reviewer":{"description":"Revue code","prompt":"Tu es un reviewer"}}'
```

### Debugging

```bash
# Mode debug
claude --debug

# Debug avec filtres specifiques
claude --debug "api,mcp"

# Exclure certains logs
claude --debug "!statsig,!file"

# Mode verbose
claude --verbose
```

### Divers

```bash
# Mettre a jour Claude Code
claude update

# Afficher la version
claude --version

# Verifier le statut de connexion
claude /status

# Integration Chrome
claude --chrome

# Creer une session remote sur claude.ai
claude --remote "Fix le bug de login"
```

## Extension VS Code

### Raccourcis Clavier

| Action | Windows/Linux | macOS |
| --- | --- | --- |
| Toggle Claude Code | `Ctrl+Esc` | `Cmd+Esc` |
| Nouveau (Tab) | `Ctrl+Shift+Esc` | `Cmd+Shift+Esc` |
| Insert @-mention | `Alt+K` | `Alt+K` |
| Nouvelle conversation | `Ctrl+N` | `Cmd+N` |

### Commandes Palette (Cmd/Ctrl+Shift+P)

- `Claude Code: Open in New Tab`
- `Claude Code: Open in New Window`
- `Claude Code: Open in Side Bar`
- `Claude Code: Open in Terminal`
- `Developer: Show Logs` (pour debugging)

### Workflow Typique

1. **Ouvrir Claude** : Cliquer sur l'icone spark dans la barre laterale
1. **Selectionner code** : Surligner dans l'editeur
1. **Referencer** : `Alt+K` pour creer @-mention
1. **Poser question** : Taper dans Claude
1. **Revoir changements** : Examiner les diffs
1. **Accepter/Rejeter** : Valider ou refuser

### @-Mentions

```text
@fichier.py              # Fichier entier
@fichier.py:10-20        # Lignes 10 a 20
@dossier/                # Tout le dossier
```

## Gestion MCP Servers

### Commandes MCP

```bash
# Ajouter un serveur HTTP
claude mcp add --transport http nom https://url

# Ajouter un serveur local (stdio)
claude mcp add --transport stdio nom -- npx -y package

# Avec variables d'environnement
claude mcp add --transport stdio --env API_KEY=xxx nom -- command

# Lister les serveurs
claude mcp list

# Details d'un serveur
claude mcp get nom

# Supprimer un serveur
claude mcp remove nom

# Verifier statut (dans Claude Code)
/mcp
```

### Scopes MCP

```bash
# Serveur utilisateur (personnel, dans ~/.claude.json)
claude mcp add --scope user --transport http nom https://url

# Serveur projet (partage, versionne, dans .mcp.json)
claude mcp add --scope project --transport http nom https://url

# Local (par defaut, dans .claude.json du projet)
claude mcp add --transport http nom https://url
```

### Serveurs Populaires

```bash
# Recherche Web (SearXNG)
claude mcp add --transport http searxng https://search.myia.io/

# Playwright (automatisation navigateur)
claude mcp add --transport stdio playwright -- \
  npx -y @anthropic/mcp-server-playwright

# GitHub
claude mcp add --transport http github \
  https://api.githubcopilot.com/mcp/

# Context7 (documentation a jour)
claude mcp add --transport stdio context7 -- \
  npx -y @upstash/context7-mcp

# OpenMemory (memoire persistante)
claude mcp add --transport stdio openmemory -- \
  npx -y @mem0/openmemory-mcp

# PostgreSQL
claude mcp add --transport stdio db -- \
  npx -y @bytebase/dbhub --dsn "postgresql://..."
```

## Slash Commands Integres

```text
/init              # Generer CLAUDE.md pour le projet
/commit            # Creer un commit Git avec message auto
/review            # Analyser les changements avant commit
/mcp               # Gerer les serveurs MCP
/status            # Afficher statut de connexion
/hooks             # Configurer les hooks
/memory            # Gerer la memoire persistante
/help              # Afficher l'aide
```

## Configuration Fichiers

### Hierarchie de priorite (du plus fort au plus faible)

1. **Managed** : `C:\Program Files\ClaudeCode\` (Windows) ou `/etc/claude-code/` (Linux)
1. **Arguments CLI** : `--model`, `--permission-mode`, etc.
1. **Local** : `.claude/settings.local.json` (personnel, gitignore)
1. **Projet** : `.claude/settings.json` (partage avec l'equipe)
1. **User** : `~/.claude/settings.json` (global personnel)

### ~/.claude/settings.json (Global)

```json
{
  "permissions": {
    "allow": [
      "Read",
      "Bash(git log *)",
      "Bash(npm run *)"
    ],
    "deny": [
      "Bash(rm -rf *)",
      "Read(.env)",
      "Read(.env.*)"
    ]
  },
  "env": {
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": ""
  }
}
```

### .claude/settings.local.json (Projet, personnel)

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": ""
  },
  "permissions": {
    "additionalDirectories": ["../shared-lib/"]
  }
}
```

### .mcp.json (Serveurs MCP Projet)

```json
{
  "mcpServers": {
    "github": {
      "type": "http",
      "url": "https://api.githubcopilot.com/mcp/"
    },
    "db": {
      "command": "npx",
      "args": ["-y", "@bytebase/dbhub", "--dsn", "${DB_URL}"],
      "env": {
        "DB_URL": "postgresql://..."
      }
    }
  }
}
```

### CLAUDE.md (Memoire Projet)

```markdown
# Mon Projet

## Stack Technique
- TypeScript 5.3
- React 18
- Node.js 20

## Structure
- `src/components/` : Composants UI
- `src/lib/` : Utilitaires et logique

## Commandes
- `npm run dev` : Serveur de developpement
- `npm test` : Lancer les tests
- `npm run build` : Build production

## Conventions
- Utiliser 2 espaces pour l'indentation
- Preferer les arrow functions
- Imports absolus depuis `@/`

## Git
- Branches : `feature/nom`, `fix/nom`
- Commits conventionnels : `feat:`, `fix:`, `docs:`
```

### .claude/rules/ (Regles modulaires)

Les regles dans `.claude/rules/*.md` sont chargees automatiquement selon le contexte.
Ajoutez un frontmatter YAML pour limiter a certains fichiers :

```yaml
---
globs: ["*.py", "tests/**"]
---
Utilise pytest pour les tests.
Docstrings en Google style.
```

### .claude/skills/ (Competences)

Les skills dans `.claude/skills/*/SKILL.md` fournissent des connaissances specifiques.
Claude les applique automatiquement quand le contexte correspond.

```yaml
---
name: "deploy"
description: "Deploiement sur AWS"
user_invocable: true
---
# Deploiement
[contenu du skill...]
```

### .claude/agents/ (Sous-agents)

Les agents dans `.claude/agents/*.md` sont auto-decouverts et invocables via `--agent`.

```yaml
---
name: "reviewer"
model: "sonnet"
tools: ["Read", "Grep", "Glob"]
---
Tu es un expert en revue de code...
```

## Hooks (Automatisation)

Les hooks executent des scripts a des points cles du workflow.
A configurer dans `settings.json` :

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Write",
        "hooks": [
          {
            "type": "command",
            "command": "echo 'Fichier ecrit: $CLAUDE_TOOL_INPUT'"
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "python lint_check.py"
          }
        ]
      }
    ],
    "UserPromptSubmit": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "echo 'Prompt soumis'"
          }
        ]
      }
    ]
  }
}
```

**Codes retour des hooks :**

- Exit 0 : OK, continuer
- Exit 2 : Bloquer l'action (PreToolUse uniquement)
- Stdout : Feedback transmis a Claude

## Variables d'Environnement

### Configuration OpenRouter

```bash
# Windows (PowerShell)
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "sk-or-v1-VOTRE_CLE"
$env:ANTHROPIC_API_KEY = ""

# Linux/macOS (bash/zsh)
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE"
export ANTHROPIC_API_KEY=""
```

### Variables Claude Code

```bash
# Modele par defaut
export ANTHROPIC_MODEL="claude-sonnet-4-5-20250929"

# Aliases de modeles OpenRouter
export ANTHROPIC_DEFAULT_OPUS_MODEL="z-ai/glm-4.7"
export ANTHROPIC_DEFAULT_SONNET_MODEL="qwen/qwen3-coder-next"
export ANTHROPIC_DEFAULT_HAIKU_MODEL="z-ai/glm-4.7-flash"

# Tokens max en sortie (defaut: 32000, max: 64000)
export CLAUDE_CODE_MAX_OUTPUT_TOKENS=32000

# Niveau d'effort (Opus uniquement) : low, medium, high
export CLAUDE_CODE_EFFORT_LEVEL=high

# Shell personnalise
export CLAUDE_CODE_SHELL="/bin/zsh"

# Desactiver les mises a jour auto
export DISABLE_AUTOUPDATER=1

# Proxy HTTP
export HTTPS_PROXY="http://proxy.example.com:8080"
```

### Variables MCP

```bash
# Activer tool search automatique
export ENABLE_TOOL_SEARCH=auto:5

# Mode demo (masque email/org)
export IS_DEMO=1
```

## Resolution Problemes Rapide

| Probleme | Solution |
| --- | --- |
| `command not found: claude` | Verifier PATH, reinstaller, redemarrer terminal |
| `Authentication failed` | Verifier `ANTHROPIC_AUTH_TOKEN` et `ANTHROPIC_BASE_URL` |
| Extension ne se connecte pas | Verifier que le CLI est installe et dans le PATH |
| MCP server timeout | Augmenter `MCP_TIMEOUT` ou verifier le serveur |
| Modele non disponible | Verifier credits OpenRouter et nom du modele |
| `npx` echoue (Windows) | Utiliser `cmd /c npx ...` dans les commandes MCP |
| Hooks non executes | Verifier format dans `settings.json`, tester le script manuellement |
| macOS : variables perdues | Ajouter exports dans `~/.zshrc` (pas `.zprofile`) |

## Ressources

- [Documentation Officielle](https://code.claude.com/docs)
- [Best Practices](https://code.claude.com/docs/en/best-practices)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [VS Code Guide](https://code.claude.com/docs/en/vs-code)
- [Configuration](https://code.claude.com/docs/en/settings)
- [MCP Servers](https://github.com/modelcontextprotocol/servers)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)

### Documentation Locale

- [Introduction Claude Code](./INTRO-CLAUDE-CODE.md) - Vue d'ensemble et concepts de base
- [Installation](./INSTALLATION-CLAUDE-CODE.md) - Guide d'installation avec OpenRouter
- [Concepts Avances](./CONCEPTS-AVANCES.md) - Skills, Subagents, Hooks, MCP en detail
- [Comparaison Claude/Roo](./COMPARAISON-CLAUDE-ROO.md) - Choisir son outil

---

**Conseil** : Gardez cette page ouverte pendant vos sessions Claude Code !
