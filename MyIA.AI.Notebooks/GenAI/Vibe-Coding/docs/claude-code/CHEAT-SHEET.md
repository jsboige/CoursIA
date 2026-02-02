# Claude Code - Aide-Mémoire Rapide

Guide de référence rapide pour Claude Code CLI et Extension VS Code.

## 🚀 Commandes CLI Essentielles

### Démarrage et Sessions

```bash
# Démarrer une session interactive
claude

# Démarrer avec une question initiale
claude "explique ce projet"

# Query ponctuelle (sans interactivité)
claude -p "liste les dépendances"

# Continuer la dernière conversation
claude -c

# Reprendre une session spécifique
claude -r "nom-session"

# Créer une nouvelle session à chaque fois
claude --fork-session
```

### Sélection de Modèle

```bash
# Modèle par défaut (Sonnet)
claude

# Utiliser Opus (plus puissant)
claude --model opus

# Utiliser Haiku (plus rapide)
claude --model haiku

# Utiliser un modèle spécifique
claude --model claude-sonnet-4-5-20250929
```

### System Prompts

```bash
# Ajouter des instructions au prompt système
claude --append-system-prompt "Utilise toujours TypeScript"

# Remplacer complètement le prompt système
claude --system-prompt "Tu es un expert Python"

# Charger un prompt depuis un fichier
claude -p --system-prompt-file ./custom-prompt.txt "query"
```

### Gestion des Permissions

```bash
# Démarrer en mode planification (pas d'exécution)
claude --permission-mode plan

# Mode auto-accept (prudent!)
claude --permission-mode auto-accept

# Restreindre les outils disponibles
claude --tools "Read,Grep,Bash"

# Autoriser certains outils sans confirmation
claude --allowedTools "Bash(git log:*)" "Read"
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

### Agents Personnalisés

```bash
# Définir des agents en ligne
claude --agents '{"reviewer":{"description":"Revue code","prompt":"Tu es un reviewer"}}'

# Charger depuis un fichier
claude --agents @agents.json
```

### Debugging

```bash
# Mode debug
claude --debug

# Debug avec filtres spécifiques
claude --debug "api,mcp"

# Exclure certains logs
claude --debug "!statsig,!file"

# Mode verbose
claude --verbose
```

### Divers

```bash
# Mettre à jour Claude Code
claude update

# Afficher la version
claude --version

# Vérifier le statut de connexion
claude /status

# Intégration Chrome
claude --chrome

# Créer une session remote sur claude.ai
claude --remote "Fix le bug de login"
```

## 💻 Extension VS Code

### Raccourcis Clavier

| Action | Windows/Linux | macOS |
|--------|---------------|-------|
| **Toggle Claude Code** | `Ctrl+Esc` | `Cmd+Esc` |
| **Nouveau (Tab)** | `Ctrl+Shift+Esc` | `Cmd+Shift+Esc` |
| **Insert @-mention** | `Alt+K` | `Alt+K` |
| **Nouvelle conversation** | `Ctrl+N` | `Cmd+N` |

### Commandes Palette (Cmd/Ctrl+Shift+P)

- `Claude Code: Open in New Tab`
- `Claude Code: Open in New Window`
- `Claude Code: Open in Side Bar`
- `Claude Code: Open in Terminal`
- `Developer: Show Logs` (pour debugging)

### Workflow Typique

1. **Ouvrir Claude** : Cliquer sur ✱ (spark icon)
2. **Sélectionner code** : Surligner dans l'éditeur
3. **Référencer** : `Alt+K` pour créer @-mention
4. **Poser question** : Taper dans Claude
5. **Revoir changements** : Examiner les diffs
6. **Accepter/Rejeter** : Valider ou refuser

### @-Mentions

```
@fichier.py              # Fichier entier
@fichier.py:10-20        # Lignes 10 à 20
@dossier/                # Tout le dossier
```

## 🔌 Gestion MCP Servers

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

# Détails d'un serveur
claude mcp get nom

# Supprimer un serveur
claude mcp remove nom

# Vérifier statut (dans Claude Code)
/mcp
```

### Scopes

```bash
# Serveur utilisateur (personnel)
claude mcp add --scope user --transport http nom https://url

# Serveur projet (partagé, versionné)
claude mcp add --scope project --transport http nom https://url

# Local (par défaut, dans .claude.json du projet)
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

# Context7 (documentation à jour)
claude mcp add --transport stdio context7 -- \
  npx -y @upstash/context7-mcp

# OpenMemory (mémoire persistante)
claude mcp add --transport stdio openmemory -- \
  npx -y @mem0/openmemory-mcp

# Serena (agent code sémantique)
claude mcp add --transport stdio serena -- \
  uvx --from git+https://github.com/oraios/serena serena start-mcp-server --context claude-code

# PostgreSQL
claude mcp add --transport stdio db -- \
  npx -y @bytebase/dbhub --dsn "postgresql://..."
```

## 📝 Slash Commands Intégrés

```
/init              # Générer CLAUDE.md pour le projet
/commit            # Créer un commit Git avec message auto
/review            # Analyser les changements avant commit
/mcp               # Gérer les serveurs MCP
/status            # Afficher statut de connexion
/hooks             # Configurer les hooks
```

## 🛠️ Configuration Fichiers

### ~/.claude/settings.json (Global)

```json
{
  "permissionMode": "default",
  "allowedTools": ["Read", "Grep", "Bash(git log:*)"],
  "disallowedTools": ["Bash(rm:*)"],
  "anthropic": {
    "baseURL": "https://openrouter.ai/api",
    "authToken": "VOTRE_CLE",
    "apiKey": ""
  }
}
```

### .claude/settings.local.json (Projet)

```json
{
  "anthropic": {
    "baseURL": "https://openrouter.ai/api",
    "authToken": "VOTRE_CLE",
    "apiKey": ""
  },
  "workingDirectories": ["../apps", "../lib"]
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

### CLAUDE.md (Mémoire Projet)

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
- `npm run dev` : Serveur de développement
- `npm test` : Lancer les tests
- `npm run build` : Build production

## Conventions
- Utiliser 2 espaces pour l'indentation
- Préférer les arrow functions
- Imports absolus depuis `@/`

## Git
- Branches : `feature/nom`, `fix/nom`
- Commits conventionnels : `feat:`, `fix:`, `docs:`
```

## 🎯 Agents Personnalisés (agents.json)

```json
{
  "reviewer": {
    "description": "Revue de code après modifications",
    "prompt": "Tu es un senior code reviewer. Focus sur qualité et sécurité.",
    "tools": ["Read", "Grep", "Glob"],
    "model": "sonnet"
  },
  "tester": {
    "description": "Debugging et tests",
    "prompt": "Expert en tests. Analyse erreurs et propose fixes.",
    "model": "haiku"
  },
  "documenter": {
    "description": "Génération documentation",
    "prompt": "Documente le code de manière claire et complète.",
    "tools": ["Read", "Write"]
  }
}
```

## 🔑 Variables d'Environnement

### Configuration OpenRouter

```bash
# Windows (PowerShell)
$env:ANTHROPIC_BASE_URL = "https://openrouter.ai/api"
$env:ANTHROPIC_AUTH_TOKEN = "VOTRE_CLE"
$env:ANTHROPIC_API_KEY = ""

# Linux/macOS (bash/zsh)
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="VOTRE_CLE"
export ANTHROPIC_API_KEY=""
```

### Variables Avancées

```bash
# Timeout MCP (ms)
export MCP_TIMEOUT=10000

# Limite output MCP (tokens)
export MAX_MCP_OUTPUT_TOKENS=50000

# Activer tool search
export ENABLE_TOOL_SEARCH=auto:5

# Model par défaut
export ANTHROPIC_DEFAULT_SONNET_MODEL="anthropic/claude-sonnet-4"
```

## 🚨 Résolution Problèmes Rapide

| Problème | Solution |
|----------|----------|
| `command not found: claude` | Vérifier PATH, réinstaller, redémarrer terminal |
| `Authentication failed` | Vérifier variables d'env OpenRouter |
| Extension ne se connecte pas | Activer "Disable Login Prompt" |
| MCP server timeout | Augmenter `MCP_TIMEOUT` |
| Modèle non disponible | Vérifier crédits OpenRouter |
| `npx` échoue (Windows) | Utiliser `cmd /c npx ...` |

## 📚 Ressources Rapides

- [Documentation Officielle](https://code.claude.com/docs)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [VS Code Guide](https://code.claude.com/docs/en/vs-code)
- [MCP Servers](https://github.com/modelcontextprotocol/servers)
- [Best Practices](https://www.anthropic.com/engineering/claude-code-best-practices)

### Documentation Locale

- [Introduction Claude Code](./INTRO-CLAUDE-CODE.md) - Vue d'ensemble et concepts de base
- [Installation](./INSTALLATION-CLAUDE-CODE.md) - Guide d'installation avec OpenRouter
- [Concepts Avancés](./CONCEPTS-AVANCES.md) - Skills, Subagents, Hooks, MCP en détail
- [Comparaison Claude/Roo](./COMPARAISON-CLAUDE-ROO.md) - Choisir son outil

---

**Conseil** : Gardez cette page ouverte pendant vos sessions Claude Code ! 🚀
