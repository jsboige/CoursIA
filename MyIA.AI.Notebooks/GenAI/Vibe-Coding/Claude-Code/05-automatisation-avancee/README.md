# Atelier 05 - Automatisation Avancée

## Objectifs pédagogiques

À la fin de cet atelier, vous serez capable de :

- Créer des Slash Commands personnalisés
- Développer des Skills réutilisables
- Orchestrer des Subagents pour des tâches complexes
- Configurer des serveurs MCP pour étendre les capacités
- Mettre en place des Hooks pour automatiser des actions

## Prérequis

- Ateliers 01 à 04 complétés
- Compréhension solide de Claude Code
- Connaissances en configuration YAML/JSON

## Durée estimée

**3 à 4 heures**

## Concepts clés

### Architecture d'extension de Claude Code

```
┌─────────────────────────────────────────────────────────┐
│                     Claude Code                          │
├─────────────────────────────────────────────────────────┤
│  Slash Commands    │    Skills    │    Subagents        │
│  (.claude/commands)│ (.claude/skills)│ (Task tool)       │
├─────────────────────────────────────────────────────────┤
│                    MCP Servers                           │
│  (searxng, github, playwright, custom...)               │
├─────────────────────────────────────────────────────────┤
│                      Hooks                               │
│  (PreToolUse, PostToolUse, UserPromptSubmit...)         │
└─────────────────────────────────────────────────────────┘
```

### Comparaison des mécanismes

| Mécanisme | Usage | Persistance | Complexité |
|-----------|-------|-------------|------------|
| Slash Commands | Raccourcis pour prompts | Session | Faible |
| Skills | Connaissances réutilisables | Projet | Moyenne |
| Subagents | Délégation de tâches | Session | Moyenne |
| MCP | Outils externes | Config | Élevée |
| Hooks | Automatisation | Config | Moyenne |

## Structure de l'atelier

| Demo | Titre | Durée | Description |
|------|-------|-------|-------------|
| 1 | [Slash Commands](demo-1-slash-commands/) | 45 min | Créer des commandes personnalisées |
| 2 | [Skills et Subagents](demo-2-skills-subagents/) | 60 min | Skills réutilisables et orchestration |
| 3 | [MCP et Hooks](demo-3-mcp-hooks/) | 50 min | Intégrations et automatisations |

## Démos

### Demo 1 - Slash Commands Personnalisés

**Objectif** : Créer des commandes pour automatiser des tâches répétitives.

Les Slash Commands sont des prompts sauvegardés, invoqués avec `/nom`.

```
.claude/commands/
├── lint.md          # /lint
├── test-current.md  # /test-current
└── deploy-check.md  # /deploy-check
```

**Exemple** :
```markdown
# lint.md
Analyse le code modifié et vérifie :
- Conformité PEP 8
- Type hints présents
- Docstrings complètes
Propose les corrections nécessaires.
```

### Demo 2 - Skills et Subagents

**Objectif** : Créer des connaissances réutilisables et déléguer des tâches.

**Skills** : Fichiers SKILL.md avec instructions pour Claude.

```yaml
---
name: python-reviewer
description: Expert code review pour Python
---

Tu es un expert en revue de code Python...
```

**Subagents** : Instances spécialisées pour des tâches isolées.

```
Délègue l'analyse de sécurité à un agent spécialisé.
```

### Demo 3 - MCP et Hooks

**Objectif** : Étendre Claude Code avec des outils externes et automatiser.

**MCP (Model Context Protocol)** : Connexion à des services externes.

```bash
claude mcp add searxng https://search.myia.io/
claude mcp add github https://api.githubcopilot.com/mcp/
```

**Hooks** : Actions automatiques sur des événements.

```json
{
  "hooks": {
    "PostToolUse": {
      "Edit": "npm run lint --fix"
    }
  }
}
```

## Fichiers de configuration

### Structure des fichiers

```
projet/
├── .claude/
│   ├── settings.json       # Configuration Claude Code
│   ├── settings.local.json # Secrets (non versionné)
│   ├── commands/           # Slash Commands
│   │   ├── lint.md
│   │   └── review.md
│   └── skills/             # Skills personnalisés
│       └── python-expert/
│           └── SKILL.md
├── .mcp.json               # Serveurs MCP du projet
└── CLAUDE.md               # Mémoire projet
```

### settings.json

```json
{
  "permissions": {
    "allow": ["Read", "Write", "Edit", "Bash"],
    "deny": ["mcp__dangerous__*"]
  },
  "hooks": {
    "PostToolUse": {
      "Edit": {
        "command": "npm run lint-staged",
        "timeout": 30000
      }
    }
  }
}
```

### .mcp.json

```json
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
      }
    }
  }
}
```

## Commandes essentielles

```bash
# Slash Commands
claude
> /ma-commande          # Exécute .claude/commands/ma-commande.md

# MCP
claude mcp list         # Liste les serveurs configurés
claude mcp add nom url  # Ajoute un serveur
claude mcp remove nom   # Supprime un serveur

# Skills
# Les skills sont auto-découverts dans .claude/skills/
> Utilise le skill python-reviewer pour analyser ce code

# Configuration
claude config list      # Liste la configuration
claude config set key value
```

## Bonnes pratiques

### Slash Commands

1. **Noms courts et descriptifs** : `/lint`, `/test`, `/deploy`
2. **Instructions claires** : Décrivez précisément ce que vous voulez
3. **Réutilisables** : Évitez les références à des fichiers spécifiques

### Skills

1. **Scopés** : Un skill = une expertise
2. **Documentés** : Description claire dans le frontmatter
3. **Testés** : Validez que le skill fonctionne

### MCP

1. **Sécurité** : Tokens dans settings.local.json
2. **Scope projet** : Utilisez `--scope project` pour les MCPs projet
3. **Timeout** : Configurez des timeouts raisonnables

### Hooks

1. **Rapides** : Les hooks bloquent, gardez-les courts
2. **Robustes** : Gérez les erreurs, ne cassez pas le workflow
3. **Ciblés** : Limitez les hooks aux outils pertinents

## Ressources

- [Skills Documentation](https://code.claude.com/docs/en/skills)
- [MCP Servers Registry](https://github.com/modelcontextprotocol/servers)
- [Hooks Documentation](https://code.claude.com/docs/en/hooks)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)

## Checklist de validation

- [ ] A créé au moins 3 Slash Commands fonctionnels
- [ ] A développé un Skill personnalisé
- [ ] Comprend le concept de Subagents
- [ ] A configuré un serveur MCP
- [ ] A mis en place un Hook fonctionnel
- [ ] Comprend la hiérarchie de configuration

---

**Félicitations !** Vous avez terminé la formation Claude Code.
