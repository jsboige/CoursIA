# Demo 3 - MCP et Hooks

## Objectif

Étendre Claude Code avec des serveurs MCP et automatiser des actions avec des Hooks.

## Durée estimée

**50 minutes**

## Concepts

### MCP (Model Context Protocol)

MCP est un protocole standard pour connecter Claude Code à des outils externes.

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ Claude Code │ ──► │ MCP Server  │ ──► │ Service     │
│             │ ◄── │             │ ◄── │ (GitHub,    │
│             │     │             │     │  Search...) │
└─────────────┘     └─────────────┘     └─────────────┘
```

### Types de transport MCP

| Transport | Description | Usage |
|-----------|-------------|-------|
| HTTP | Requêtes REST | Serveurs web |
| Stdio | Processus local | CLI tools |
| SSE | Server-Sent Events | Streaming |

### Hooks

Les Hooks sont des actions automatiques déclenchées par des événements.

| Event | Déclencheur |
|-------|-------------|
| PreToolUse | Avant l'utilisation d'un outil |
| PostToolUse | Après l'utilisation d'un outil |
| UserPromptSubmit | Quand l'utilisateur envoie un message |
| Stop | Quand Claude termine |

## Étapes

### Étape 1 : Configurer un serveur MCP (15 min)

#### Configuration locale (.mcp.json)

```bash
cat > .mcp.json << 'EOF'
{
  "mcpServers": {
    "searxng": {
      "url": "https://search.myia.io/",
      "transport": "http",
      "description": "Moteur de recherche web distribué"
    }
  }
}
EOF
```

#### Vérifier la configuration

```bash
claude mcp list
```

#### Tester

```
Recherche les dernières nouveautés de Python 3.13
```

### Étape 2 : Ajouter le MCP GitHub (10 min)

#### Installation

```bash
# Ajouter au .mcp.json
cat > .mcp.json << 'EOF'
{
  "mcpServers": {
    "searxng": {
      "url": "https://search.myia.io/",
      "transport": "http"
    },
    "github": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-github"],
      "env": {
        "GITHUB_TOKEN": "${GITHUB_TOKEN}"
      },
      "transport": "stdio"
    }
  }
}
EOF
```

#### Configurer le token (non versionné)

```bash
cat > .claude/settings.local.json << 'EOF'
{
  "env": {
    "GITHUB_TOKEN": "ghp_votre_token_github"
  }
}
EOF

# Ajouter au .gitignore
echo ".claude/settings.local.json" >> .gitignore
```

#### Tester

```
Liste mes 5 derniers repositories GitHub
```

```
Crée une issue sur mon-repo avec le titre "Test MCP" et une description
```

### Étape 3 : Configurer des Hooks basiques (10 min)

#### Configuration dans settings.json

```bash
cat > .claude/settings.json << 'EOF'
{
  "permissions": {
    "allow": ["Read", "Write", "Edit", "Bash", "Glob", "Grep"]
  },
  "hooks": {
    "PostToolUse": {
      "Edit": {
        "command": "echo '✏️ Fichier modifié'",
        "timeout": 2000
      },
      "Write": {
        "command": "echo '📝 Fichier créé'",
        "timeout": 2000
      }
    }
  }
}
EOF
```

#### Tester

Modifiez un fichier et observez le message du hook.

### Étape 4 : Hook de linting automatique (10 min)

#### Configuration avancée

```bash
cat > .claude/settings.json << 'EOF'
{
  "permissions": {
    "allow": ["Read", "Write", "Edit", "Bash", "Glob", "Grep"]
  },
  "hooks": {
    "PostToolUse": {
      "Edit": {
        "command": "if [[ ${file} == *.py ]]; then python -m py_compile ${file} 2>&1 && echo '✅ Syntaxe OK' || echo '❌ Erreur de syntaxe'; fi",
        "timeout": 5000
      },
      "Write": {
        "command": "if [[ ${file} == *.py ]]; then black ${file} --quiet && echo '✨ Formaté avec Black'; fi",
        "timeout": 10000
      }
    }
  }
}
EOF
```

#### Variables disponibles dans les hooks

| Variable | Description |
|----------|-------------|
| `${file}` | Chemin du fichier concerné |
| `${tool}` | Nom de l'outil utilisé |
| `${result}` | Résultat de l'outil |

### Étape 5 : Hook de notification (5 min)

#### Notification système (macOS)

```json
{
  "hooks": {
    "Stop": {
      "command": "osascript -e 'display notification \"Claude a terminé\" with title \"Claude Code\"'",
      "timeout": 2000
    }
  }
}
```

#### Notification système (Linux)

```json
{
  "hooks": {
    "Stop": {
      "command": "notify-send 'Claude Code' 'Tâche terminée'",
      "timeout": 2000
    }
  }
}
```

#### Notification système (Windows)

```json
{
  "hooks": {
    "Stop": {
      "command": "powershell -Command \"[System.Windows.MessageBox]::Show('Claude a terminé')\"",
      "timeout": 5000
    }
  }
}
```

## Exercice pratique

### Mission

Créez une configuration MCP + Hooks complète pour votre projet.

### Cahier des charges

1. **MCP Servers**
   - searxng pour la recherche web
   - github pour l'intégration Git
   - (optionnel) Un serveur custom

2. **Hooks**
   - Lint automatique après Edit sur fichiers Python
   - Notification quand Claude termine
   - Log des actions (optionnel)

### Template de configuration

```json
// .mcp.json
{
  "mcpServers": {
    "searxng": {
      "url": "https://search.myia.io/",
      "transport": "http"
    },
    "github": {
      "command": "npx",
      "args": ["-y", "@modelcontextprotocol/server-github"],
      "env": {
        "GITHUB_TOKEN": "${GITHUB_TOKEN}"
      },
      "transport": "stdio"
    }
  }
}
```

```json
// .claude/settings.json
{
  "permissions": {
    "allow": ["Read", "Write", "Edit", "Bash", "Glob", "Grep", "WebSearch", "WebFetch"],
    "deny": []
  },
  "hooks": {
    "PostToolUse": {
      "Edit": {
        "command": "votre_commande_lint",
        "timeout": 10000
      }
    },
    "Stop": {
      "command": "votre_commande_notification",
      "timeout": 3000
    }
  }
}
```

### Livrable

Configuration fonctionnelle testée.

## Serveurs MCP populaires

| Serveur | Usage | Installation |
|---------|-------|--------------|
| searxng | Recherche web | HTTP vers instance |
| github | GitHub API | `@modelcontextprotocol/server-github` |
| filesystem | Accès fichiers | `@modelcontextprotocol/server-filesystem` |
| playwright | Browser automation | `@anthropic/mcp-server-playwright` |
| postgres | Base de données | `@modelcontextprotocol/server-postgres` |

## Bonnes pratiques

### MCP

1. **Sécurité** : Tokens dans settings.local.json (non versionné)
2. **Scope** : Utilisez des serveurs projet-spécifiques
3. **Timeout** : Configurez des timeouts raisonnables
4. **Logs** : Activez les logs pour le debug

### Hooks

1. **Rapidité** : Hooks courts (< 10s)
2. **Robustesse** : Gérez les erreurs silencieusement
3. **Ciblage** : Filtrez par type de fichier
4. **Non-bloquant** : Préférez les notifications async

## Dépannage

### MCP ne répond pas

```bash
# Vérifier la configuration
claude mcp list

# Tester manuellement (HTTP)
curl https://search.myia.io/

# Vérifier les logs
claude --debug
```

### Hook ne s'exécute pas

1. Vérifiez la syntaxe JSON
2. Vérifiez le chemin de la commande
3. Testez la commande manuellement
4. Vérifiez les permissions

## Points clés à retenir

1. **MCP = Extension** : Connectez Claude à n'importe quel service

2. **Hooks = Automatisation** : Actions sur événements

3. **Sécurité** : Secrets dans settings.local.json

4. **Modularité** : Configuration par projet

---

**Félicitations !** Vous avez terminé l'atelier 05 et la formation Claude Code.
