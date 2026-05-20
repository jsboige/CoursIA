# Concepts Avances de Claude Code

Ce document approfondit les concepts cles de Claude Code : **Slash Commands**, **Skills**, **Subagents**, **Hooks**, **Permissions**, **Sandbox** et **MCP**. Ces fonctionnalites permettent de personnaliser et d'etendre considerablement les capacites de l'assistant.

> **Documentation officielle** : [code.claude.com/docs](https://code.claude.com/docs)

## Table des Matieres

1. [Slash Commands (Commandes)](#slash-commands-commandes)
1. [Skills (Compétences)](#skills-compétences)
1. [Subagents (Sous-agents)](#subagents-sous-agents)
1. [Hooks (Déclencheurs)](#hooks-déclencheurs)
1. [Permissions et Securite](#permissions-et-securite)
1. [Sandbox](#sandbox)
1. [MCP (Model Context Protocol)](#mcp-model-context-protocol)
1. [Comparaison et Cas d'Usage](#comparaison-et-cas-dusage)

---

## Slash Commands (Commandes)

Les **slash commands** sont des prompts sauvegardés invoqués explicitement avec `/nom-commande`. Contrairement aux Skills, c'est l'utilisateur qui décide quand les exécuter.

### Commandes Intégrées

| Commande | Description |
|----------|-------------|
| `/init` | Génère un fichier CLAUDE.md adapté au projet |
| `/commit` | Crée un commit Git avec message auto-généré |
| `/review` | Analyse les changements avant commit |
| `/mcp` | Gère les serveurs MCP connectés |
| `/status` | Affiche le statut de connexion |
| `/help` | Liste toutes les commandes disponibles |
| `/agents` | Gère les subagents personnalisés |
| `/hooks` | Configure les hooks d'automatisation |

### Emplacements des Commandes Personnalisées

| Emplacement | Portée | Partage |
|-------------|--------|---------|
| `.claude/commands/` | Projet uniquement | Via le dépôt Git |
| `~/.claude/commands/` | Tous vos projets | Personnel |

**Priorité** : Les commandes projet écrasent les commandes personnelles de même nom.

### Créer une Commande Personnalisée

1. **Créer le dossier** (si inexistant) :

```bash
mkdir -p .claude/commands
```

2. **Créer un fichier Markdown** (le nom devient la commande) :

```bash
# Fichier: .claude/commands/optimize.md
```

3. **Écrire le prompt en langage naturel** :

```markdown
Analyse ce code pour détecter les problèmes de performance et suggère des optimisations.

Concentre-toi sur :
- Les boucles inefficaces
- Les requêtes N+1
- Les allocations mémoire inutiles
- Les opportunités de mise en cache

Fichiers à analyser : $ARGUMENTS
```

4. **Utiliser la commande** :

```
/optimize src/api/
```

### Variables Disponibles

| Variable | Description |
|----------|-------------|
| `$ARGUMENTS` | Arguments passés après la commande |
| `${CLAUDE_SESSION_ID}` | ID de session pour logging |

### Exemples de Commandes Utiles

#### Commande de Revue de PR

```markdown
# .claude/commands/review-pr.md

Effectue une revue de code complète des changements en cours.

1. Exécute `git diff HEAD~1` pour voir les modifications
2. Analyse chaque fichier modifié

Vérifie :
- [ ] Qualité et lisibilité du code
- [ ] Gestion des erreurs
- [ ] Tests unitaires présents
- [ ] Pas de secrets exposés
- [ ] Documentation à jour

Classe les problèmes par priorité :
- **Critique** : Doit être corrigé avant merge
- **Important** : Devrait être corrigé
- **Suggestion** : Amélioration optionnelle
```

#### Commande de Documentation

```markdown
# .claude/commands/document.md

Génère une documentation complète pour : $ARGUMENTS

Inclus :
- Description générale
- Paramètres et types
- Valeurs de retour
- Exemples d'utilisation
- Cas d'erreur possibles

Format : JSDoc/TSDoc pour TypeScript, docstrings pour Python.
```

### Autocomplétion

L'autocomplétion fonctionne n'importe où dans votre saisie. Tapez `/` à n'importe quelle position pour voir les commandes disponibles.

---

## Skills (Compétences)

Les **Skills** sont des capacités que Claude découvre et applique automatiquement quand votre demande correspond à leur description. C'est Claude qui décide quand les utiliser.

### Différence Clé : Skills vs Slash Commands

| Aspect | Slash Commands | Skills |
|--------|----------------|--------|
| **Invocation** | Explicite (`/commande`) | Automatique par Claude |
| **Décision** | Utilisateur | Claude (basé sur description) |
| **Format** | Fichier `.md` simple | Dossier avec `SKILL.md` |
| **Ressources** | Prompt uniquement | Scripts, références, assets |

### Structure d'un Skill

```
mon-skill/
├── SKILL.md          # Requis - Instructions principales
├── reference.md      # Optionnel - Documentation détaillée
├── examples.md       # Optionnel - Exemples d'utilisation
└── scripts/          # Optionnel - Scripts exécutables
    └── helper.py
```

### Format du Fichier SKILL.md

```markdown
---
name: mon-skill
description: Description claire de ce que fait ce skill et quand l'utiliser (max 1024 caractères)
allowed-tools: Read, Grep, Glob
model: claude-sonnet-4
---

# Mon Skill

## Instructions

Explications détaillées de ce que Claude doit faire...

## Étapes

1. Première étape
2. Deuxième étape

## Ressources

- Pour plus de détails, voir [reference.md](reference.md)
```

### Métadonnées Disponibles (Frontmatter)

| Champ | Requis | Description |
|-------|--------|-------------|
| `name` | Oui | Nom unique (minuscules, tirets, max 64 car.) |
| `description` | Oui | Quand utiliser ce skill (max 1024 car.) |
| `allowed-tools` | Non | Outils autorisés sans permission |
| `model` | Non | Modèle à utiliser (ex: `claude-sonnet-4`) |
| `context` | Non | `fork` pour contexte isolé |
| `agent` | Non | Type d'agent si `context: fork` |
| `user-invocable` | Non | Visible dans le menu slash (défaut: `true`) |
| `hooks` | Non | Hooks PreToolUse, PostToolUse, Stop |

### Emplacements des Skills

| Emplacement | Portée | Découverte |
|-------------|--------|------------|
| `~/.claude/skills/` | Personnel, tous projets | Auto |
| `.claude/skills/` | Projet, équipe | Auto |
| Plugin `skills/` | Avec le plugin | Auto |

**Découverte automatique** : Claude scanne aussi les `.claude/skills/` dans les sous-dossiers (support monorepo).

### Progressive Disclosure (Concept Clé)

Claude charge les informations progressivement :

1. **Au démarrage** : Seulement `name` et `description` de chaque skill
2. **Si sélectionné** : Charge le contenu de `SKILL.md`
3. **À l'exécution** : Charge les fichiers de référence si nécessaires

**Recommandation** : Garder `SKILL.md` sous 500 lignes, utiliser des fichiers séparés pour les détails.

### Exemple : Skill de Génération de Tests

```markdown
# .claude/skills/test-generator/SKILL.md
---
name: test-generator
description: Génère des tests unitaires complets. Utiliser lors de la création de nouvelles fonctions ou classes, ou quand l'utilisateur demande des tests.
allowed-tools: Read, Write, Bash
---

# Générateur de Tests

## Instructions

Quand invoqué, génère des tests unitaires pour le code spécifié.

## Étapes

1. Analyser la signature et le comportement de la fonction
2. Identifier les cas de test :
   - Cas nominal (happy path)
   - Cas limites (edge cases)
   - Cas d'erreur
3. Générer les tests avec le framework du projet

## Conventions par Langage

- **Python** : pytest avec fixtures
- **TypeScript** : Jest ou Vitest
- **Go** : testing package standard

## Structure des Tests

```python
def test_fonction_cas_nominal():
    """Test du comportement normal."""
    # Arrange
    # Act
    # Assert

def test_fonction_cas_limite():
    """Test des valeurs limites."""
    pass

def test_fonction_cas_erreur():
    """Test des erreurs attendues."""
    with pytest.raises(ExpectedError):
        pass
```
```

### Exemple : Skill de Revue de Sécurité

```markdown
# .claude/skills/security-review/SKILL.md
---
name: security-review
description: Audit de sécurité du code. Utiliser pour détecter les vulnérabilités OWASP, les injections, et les problèmes d'authentification.
allowed-tools: Read, Grep, Glob
user-invocable: false
---

# Revue de Sécurité

## Checklist OWASP Top 10

- [ ] A01 - Broken Access Control
- [ ] A02 - Cryptographic Failures
- [ ] A03 - Injection (SQL, Command, XSS)
- [ ] A04 - Insecure Design
- [ ] A05 - Security Misconfiguration
- [ ] A06 - Vulnerable Components
- [ ] A07 - Authentication Failures
- [ ] A08 - Data Integrity Failures
- [ ] A09 - Logging Failures
- [ ] A10 - SSRF

## Patterns à Détecter

Voir [patterns-vulnerabilites.md](patterns-vulnerabilites.md) pour la liste complète.
```

---

## Subagents (Sous-agents)

Les **subagents** sont des instances spécialisées de Claude qui s'exécutent dans leur propre contexte, avec leurs propres outils et permissions. Ils permettent la parallélisation et la spécialisation.

### Subagents Intégrés

| Subagent | Modèle | Outils | Usage |
|----------|--------|--------|-------|
| **Explore** | Haiku (rapide) | Lecture seule | Recherche, exploration codebase |
| **Plan** | Hérité | Lecture seule | Recherche en mode planification |
| **General-purpose** | Hérité | Tous | Tâches complexes multi-étapes |
| **Bash** | Hérité | Bash | Commandes terminal isolées |
| **Claude Code Guide** | Haiku | Lecture | Questions sur Claude Code |

### Caractéristiques Clés

- **Contexte isolé** : Chaque subagent a sa propre fenêtre de contexte
- **Parallélisme** : Jusqu'à 10 subagents simultanés (les autres sont mis en file)
- **Pas de nesting** : Un subagent ne peut pas créer d'autres subagents
- **Permissions héritées** : Hérite des permissions du parent (avec restrictions possibles)

### Créer un Subagent Personnalisé

#### Méthode 1 : Via `/agents` (Recommandé)

```
/agents
```

Puis suivre l'assistant interactif.

#### Méthode 2 : Fichier Markdown

```markdown
# .claude/agents/code-reviewer.md
---
name: code-reviewer
description: Expert en revue de code. Utiliser proactivement après des modifications.
tools: Read, Grep, Glob, Bash
model: sonnet
---

Tu es un reviewer senior. Quand invoqué :

1. Exécute `git diff` pour voir les changements
2. Analyse chaque fichier modifié

Checklist :
- Code lisible et maintenable
- Nommage approprié
- Pas de duplication
- Gestion des erreurs
- Pas de secrets exposés
- Tests présents

Formate tes retours par priorité :
- **Critique** : À corriger absolument
- **Important** : Devrait être corrigé
- **Suggestion** : Amélioration optionnelle
```

#### Méthode 3 : CLI

```bash
claude --agents '{
  "code-reviewer": {
    "description": "Expert revue de code. Utiliser après modifications.",
    "prompt": "Tu es un reviewer senior...",
    "tools": ["Read", "Grep", "Glob"],
    "model": "sonnet"
  }
}'
```

### Configuration Frontmatter

| Champ | Requis | Description |
|-------|--------|-------------|
| `name` | Oui | Identifiant unique |
| `description` | Oui | Quand Claude doit déléguer |
| `tools` | Non | Outils autorisés |
| `disallowedTools` | Non | Outils interdits |
| `model` | Non | `sonnet`, `opus`, `haiku`, `inherit` |
| `permissionMode` | Non | Mode de permission |
| `skills` | Non | Skills à injecter |
| `hooks` | Non | Hooks du subagent |

### Modes de Permission

| Mode | Comportement |
|------|--------------|
| `default` | Demande permission (standard) |
| `acceptEdits` | Auto-accepte les modifications fichiers |
| `dontAsk` | Auto-refuse les demandes de permission |
| `bypassPermissions` | Ignore toutes les permissions (prudent!) |
| `plan` | Mode lecture seule |

### Emplacements et Priorité

| Emplacement | Portée | Priorité |
|-------------|--------|----------|
| `--agents` CLI | Session | 1 (plus haute) |
| `.claude/agents/` | Projet | 2 |
| `~/.claude/agents/` | Personnel | 3 |
| Plugin `agents/` | Avec plugin | 4 (plus basse) |

### Délégation Automatique vs Explicite

**Automatique** : Claude délègue basé sur la `description` du subagent.

```
Analyse l'architecture de ce projet
→ Claude délègue automatiquement à Explore
```

**Explicite** : Vous demandez la délégation.

```
Utilise le subagent code-reviewer pour analyser mes derniers changements
```

### Foreground vs Background

| Mode | Comportement | Permissions |
|------|--------------|-------------|
| **Foreground** | Bloque la conversation principale | Prompts passés à l'utilisateur |
| **Background** | Exécution concurrente | Hérite du parent, auto-refuse inconnus |

**Désactiver background** : `CLAUDE_CODE_DISABLE_BACKGROUND_TASKS=1`

### Patterns d'Utilisation

#### Parallélisation

```
Recherche les modules auth, database et API en parallèle avec des subagents séparés
```

#### Chaînage

```
Utilise code-reviewer pour trouver les problèmes, puis optimizer pour les corriger
```

#### Isolation de tâches lourdes

```
Lance un subagent pour exécuter la suite de tests et rapporte seulement les échecs
```

### Exemple Complet : Debugger

```markdown
# .claude/agents/debugger.md
---
name: debugger
description: Spécialiste debugging pour erreurs et tests échoués. Utiliser proactivement en cas de problème.
tools: Read, Edit, Bash, Grep, Glob
model: inherit
---

Tu es un expert en debugging spécialisé dans l'analyse des causes racines.

## Quand invoqué

1. Capture le message d'erreur et la stack trace
2. Identifie les étapes de reproduction
3. Isole le point de défaillance
4. Implémente un correctif minimal
5. Vérifie que la solution fonctionne

## Pour chaque problème, fournis

- Explication de la cause racine
- Preuves supportant le diagnostic
- Correctif de code spécifique
- Approche de test
- Recommandations de prévention
```

---

## Hooks (Déclencheurs)

Les **hooks** sont des automatisations qui exécutent des commandes shell à des moments spécifiques du cycle de vie de Claude Code. Ils transforment des suggestions en actions garanties.

### Types de Hooks

| Hook | Moment | Usage |
|------|--------|-------|
| `UserPromptSubmit` | Soumission d'un prompt | Validation, enrichissement |
| `PreToolUse` | Avant exécution d'un outil | Validation, blocage, modification |
| `PostToolUse` | Après exécution d'un outil | Lint, format, notification |
| `SessionStart` | Début de session | Setup environnement |
| `SessionEnd` | Fin de session | Cleanup, logging |
| `Notification` | Notification système | Alertes |
| `Stop` | Fin de réponse | Actions finales |
| `SubagentStart/Stop` | Cycle vie subagent | Setup/cleanup subagent |
| `PreCompact` | Avant compaction | Sauvegarde contexte |

### Configuration

Les hooks se configurent dans les fichiers settings :

| Fichier | Portée |
|---------|--------|
| `~/.claude/settings.json` | Utilisateur global |
| `.claude/settings.json` | Projet (versionné) |
| `.claude/settings.local.json` | Projet local (non versionné) |

### Structure de Configuration

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Edit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "./scripts/pre-edit-check.sh"
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "Edit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "npm run lint --fix"
          }
        ]
      }
    ]
  }
}
```

### Matchers Disponibles

Les matchers filtrent quels outils déclenchent le hook :

| Matcher | Outils Correspondants |
|---------|----------------------|
| `Edit` | Modifications de fichiers |
| `Write` | Création de fichiers |
| `Bash` | Commandes terminal |
| `Task` | Subagents et tâches |
| `WebFetch` | Requêtes web |
| `*` | Tous les outils |

**Combinaison** : `Edit|Write` pour plusieurs outils.

### Contrôle de Décision (PreToolUse)

Les hooks `PreToolUse` peuvent contrôler l'exécution :

| Code Sortie | Action |
|-------------|--------|
| 0 | Continuer normalement |
| 2 | Bloquer l'opération |
| Autre | Erreur, demander à l'utilisateur |

**Champs de contrôle** dans la sortie JSON :

```json
{
  "decision": "allow|deny|ask",
  "permissionDecisionReason": "Raison affichée à l'utilisateur",
  "updatedInput": { "modifiedField": "newValue" }
}
```

### Exemple : Validation de Requêtes SQL

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "./scripts/validate-readonly-query.sh"
          }
        ]
      }
    ]
  }
}
```

**Script** `validate-readonly-query.sh` :

```bash
#!/bin/bash
INPUT=$(cat)
COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // empty')

# Bloquer les opérations d'écriture SQL
if echo "$COMMAND" | grep -iE '\b(INSERT|UPDATE|DELETE|DROP|CREATE|ALTER)\b' > /dev/null; then
  echo '{"decision": "deny", "permissionDecisionReason": "Seules les requêtes SELECT sont autorisées"}'
  exit 0
fi

echo '{"decision": "allow"}'
exit 0
```

### Exemple : Lint Automatique Après Édition

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit|Write",
        "hooks": [
          {
            "type": "command",
            "command": "npm run lint --fix"
          }
        ]
      }
    ]
  }
}
```

### Exemple : Tests Après Modification

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit",
        "hooks": [
          {
            "type": "command",
            "command": "./scripts/run-affected-tests.sh"
          }
        ]
      }
    ]
  }
}
```

### Hooks dans les Subagents

Les subagents peuvent avoir leurs propres hooks dans le frontmatter :

```yaml
---
name: db-reader
description: Exécute des requêtes read-only
tools: Bash
hooks:
  PreToolUse:
    - matcher: "Bash"
      hooks:
        - type: command
          command: "./scripts/validate-readonly-query.sh"
---
```

### Securite des Hooks

Claude Code inclut une protection : les modifications directes des fichiers de configuration de hooks necessitent une revue dans le menu `/hooks` avant prise d'effet.

---

## Permissions et Securite

Le systeme de permissions de Claude Code permet un controle granulaire sur les actions autorisees. Il repose sur des regles `allow`, `deny` et `ask` configurees dans `settings.json`.

### Niveaux de Permission

| Mode | Comportement |
| --- | --- |
| `default` | Demande permission pour chaque action |
| `acceptEdits` | Accepte lectures et ecritures de fichiers, demande pour Bash |
| `plan` | Mode lecture seule, pas d'execution |
| `auto-accept` | Accepte tout automatiquement (a utiliser avec prudence) |
| `bypassPermissions` | Ignore les permissions (deconseille en production) |

### Regles de Permission

Les regles se configurent dans `settings.json` avec trois niveaux :

```json
{
  "permissions": {
    "allow": [
      "Read",
      "Bash(npm run *)",
      "Bash(git log *)",
      "Edit(src/**)"
    ],
    "deny": [
      "Bash(rm -rf *)",
      "Read(.env)",
      "Read(.env.*)",
      "Read(./secrets/**)"
    ],
    "ask": [
      "Bash(git push *)",
      "Edit(package.json)"
    ]
  }
}
```

### Syntaxe des Regles

| Regle | Effet |
| --- | --- |
| `Bash` | Correspond a toutes les commandes Bash |
| `Bash(npm run *)` | Commandes commencant par `npm run` |
| `Read(.env)` | Lecture du fichier `.env` |
| `Read(./secrets/**)` | Lecture recursive dans `secrets/` |
| `Edit(src/**)` | Editions dans `src/` |
| `WebFetch(domain:example.com)` | Requetes vers example.com |
| `MCP(github)` | Utilisation du serveur MCP github |

### Ordre d'Evaluation

1. **Deny** : premiere regle correspondante gagne
1. **Ask** : premiere regle correspondante gagne
1. **Allow** : premiere regle correspondante gagne

Les regles `deny` sont toujours evaluees en premier, garantissant que les interdictions ne peuvent pas etre contournees.

### Options Avancees

```json
{
  "permissions": {
    "additionalDirectories": ["../docs/", "~/shared/"],
    "defaultMode": "acceptEdits",
    "disableBypassPermissionsMode": "disable"
  }
}
```

- **additionalDirectories** : Repertoires supplementaires accessibles a Claude
- **defaultMode** : Mode de permission par defaut
- **disableBypassPermissionsMode** : Empeche l'utilisation du mode bypass

---

## Sandbox

Le sandbox isole l'execution de Claude Code dans un environnement controle, limitant l'acces au systeme de fichiers et au reseau.

### Activation

```json
{
  "sandbox": {
    "enabled": true,
    "autoAllowBashIfSandboxed": true
  }
}
```

Quand `autoAllowBashIfSandboxed` est `true`, les commandes Bash sont auto-acceptees car le sandbox empeche les actions destructives.

### Configuration Reseau

```json
{
  "sandbox": {
    "enabled": true,
    "network": {
      "allowedDomains": [
        "github.com",
        "*.npmjs.org",
        "registry.yarnpkg.com"
      ],
      "allowLocalBinding": true,
      "httpProxyPort": 8080
    }
  }
}
```

### Commandes Exclues

Certaines commandes peuvent etre exclues du sandbox (executees hors isolation) :

```json
{
  "sandbox": {
    "enabled": true,
    "excludedCommands": ["git", "docker"],
    "allowUnsandboxedCommands": true
  }
}
```

### Disponibilite

Le sandbox est disponible sur macOS et Linux. Sur Windows, il n'est pas encore supporte nativement (utiliser WSL comme alternative).

---

## MCP (Model Context Protocol)

**MCP** est un standard ouvert pour connecter les agents IA à des outils et sources de données externes. Pensez-y comme "l'USB-C pour l'IA" - une interface universelle pour étendre les capacités de Claude.

### Architecture

```
┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐
│   Claude Code   │────▶│   MCP Client    │────▶│   MCP Server    │
│   (Agent IA)    │     │   (Intégré)     │     │   (Outil)       │
└─────────────────┘     └─────────────────┘     └─────────────────┘
                                                       │
                                                       ▼
                                                ┌─────────────────┐
                                                │  Service Externe │
                                                │  (DB, API, etc.) │
                                                └─────────────────┘
```

### Capacités MCP

| Type | Description | Exemple |
|------|-------------|---------|
| **Tools** | Actions exécutables | Requêtes DB, recherche web |
| **Resources** | Données consultables (@-mentions) | Documentation, fichiers |
| **Prompts** | Templates de prompts | Workflows prédéfinis |

### Types de Transport

| Transport | Usage | Configuration |
|-----------|-------|---------------|
| **HTTP** | Serveurs distants (recommandé) | URL directe |
| **Stdio** | Serveurs locaux (processus) | Commande + args |
| **SSE** | Server-Sent Events | Déprécié |

### Commandes MCP

```bash
# Ajouter un serveur HTTP
claude mcp add --transport http github https://api.githubcopilot.com/mcp/

# Ajouter un serveur local (stdio)
claude mcp add --transport stdio db -- npx -y @bytebase/dbhub --dsn "postgresql://..."

# Avec variables d'environnement
claude mcp add --transport stdio --env API_KEY=xxx myserver -- command

# Lister les serveurs
claude mcp list

# Détails d'un serveur
claude mcp get github

# Supprimer un serveur
claude mcp remove github

# Vérifier le statut (dans Claude Code)
/mcp
```

### Scopes (Portées)

| Scope | Stockage | Partage |
|-------|----------|---------|
| `local` (défaut) | `.claude.json` | Non versionné |
| `project` | `.mcp.json` | Versionné (équipe) |
| `user` | `~/.claude/...` | Personnel, tous projets |

```bash
# Serveur projet (partagé avec l'équipe)
claude mcp add --scope project --transport http myserver https://...

# Serveur utilisateur (personnel)
claude mcp add --scope user --transport http myserver https://...
```

### Fichier .mcp.json (Configuration Projet)

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
        "DB_URL": "postgresql://localhost:5432/mydb"
      }
    },
    "searxng": {
      "type": "http",
      "url": "https://search.myia.io/"
    }
  }
}
```

### Serveurs MCP Populaires

| Serveur | Usage | Installation |
|---------|-------|--------------|
| **SearXNG** | Recherche web | Instance SearXNG |
| **Playwright** | Automatisation navigateur | `npx -y @anthropic/mcp-server-playwright` |
| **GitHub** | Issues, PRs, repos | HTTP: `api.githubcopilot.com/mcp/` |
| **Context7** | Documentation à jour | `npx -y @upstash/context7-mcp` |
| **OpenMemory** | Mémoire persistante cross-session | `npx -y @mem0/openmemory-mcp` |
| **Serena** | Agent de code sémantique (30+ langages) | `uvx --from git+https://github.com/oraios/serena serena` |
| **PostgreSQL** | Requêtes DB | `npx -y @bytebase/dbhub` |

> **Note :** Claude Code intègre nativement d'excellentes capacités de gestion de fichiers. Le MCP Filesystem n'est généralement pas nécessaire.

### Tool Search (Recherche d'Outils)

Quand vous avez beaucoup d'outils MCP, Claude Code active automatiquement **Tool Search** pour éviter de surcharger le contexte :

- Activé si les descriptions d'outils > 10% de la fenêtre de contexte
- Charge les outils à la demande plutôt que tous au démarrage
- Configurable via `ENABLE_TOOL_SEARCH=auto:5`

### Gestion des Tokens

Les réponses MCP volumineuses sont limitées :

```bash
# Augmenter la limite (défaut: 25000)
export MAX_MCP_OUTPUT_TOKENS=50000
```

### Exemple : Configuration Complète pour un Projet

```json
{
  "mcpServers": {
    "search": {
      "type": "http",
      "url": "https://search.myia.io/"
    },
    "github": {
      "type": "http",
      "url": "https://api.githubcopilot.com/mcp/"
    },
    "postgres": {
      "command": "npx",
      "args": ["-y", "@bytebase/dbhub", "--dsn", "${DATABASE_URL}"],
      "env": {
        "DATABASE_URL": "postgresql://user:pass@localhost:5432/mydb"
      }
    }
  }
}
```

### Utilisation des Resources MCP

Les resources MCP sont accessibles via @-mentions :

```
Analyse @mcp-resource/docs/api-reference

Utilise les données de @mcp-resource/db/users pour générer un rapport
```

---

## Comparaison et Cas d'Usage

### Tableau Récapitulatif

| Fonctionnalité | Invocation | Stockage | Cas d'Usage |
|----------------|------------|----------|-------------|
| **Slash Commands** | Explicite (`/cmd`) | `.claude/commands/` | Prompts répétitifs |
| **Skills** | Automatique par Claude | `.claude/skills/` | Workflows complexes |
| **Subagents** | Auto ou explicite | `.claude/agents/` | Tâches spécialisées, parallélisation |
| **Hooks** | Événements | `.claude/settings.json` | Automatisations garanties |
| **MCP** | Selon besoin | `.mcp.json` | Connexion outils externes |

### Quand Utiliser Quoi ?

| Besoin | Solution |
|--------|----------|
| Prompt réutilisable simple | Slash Command |
| Workflow avec documentation/scripts | Skill |
| Tâche spécialisée ou parallèle | Subagent |
| Action garantie sur événement | Hook |
| Connexion API/DB externe | MCP Server |
| Instructions projet-wide | CLAUDE.md |

### Exemple de Combinaison

Un workflow complet de développement pourrait combiner :

1. **CLAUDE.md** : Conventions et stack du projet
2. **Slash Command `/deploy`** : Déploiement manuel
3. **Skill `test-generator`** : Génération auto de tests
4. **Subagent `code-reviewer`** : Revue spécialisée
5. **Hook PostToolUse** : Lint automatique
6. **MCP GitHub** : Gestion des PRs

---

## Ressources

### Documentation Officielle

- [Slash Commands](https://code.claude.com/docs/en/slash-commands)
- [Agent Skills](https://code.claude.com/docs/en/skills)
- [Subagents](https://code.claude.com/docs/en/sub-agents)
- [Hooks Reference](https://code.claude.com/docs/en/hooks)
- [MCP Guide](https://code.claude.com/docs/en/mcp)

### Communauté

- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)
- [Awesome Claude Skills](https://github.com/travisvn/awesome-claude-skills)
- [Claude Commands Collection](https://github.com/wshobson/commands)
- [MCP Servers Registry](https://github.com/modelcontextprotocol/servers)
- [SkillsMP Marketplace](https://skillsmp.com/)

---

*Pour l'installation et la configuration de base, consultez [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md)*

*Pour un aide-mémoire rapide, consultez [CHEAT-SHEET.md](./CHEAT-SHEET.md)*
