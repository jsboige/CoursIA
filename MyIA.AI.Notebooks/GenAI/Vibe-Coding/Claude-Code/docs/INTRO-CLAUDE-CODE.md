# Introduction à Claude Code

Ce document vous présente Claude Code, l'assistant de codage agentique développé par Anthropic, et ses deux interfaces principales : le CLI (terminal) et l'extension VS Code.

## Qu'est-ce que Claude Code ?

**Claude Code** est un outil de codage agentique qui vous aide à coder plus rapidement en exécutant des tâches routinières, en expliquant du code complexe et en gérant des workflows Git, le tout via des commandes en langage naturel.

**Caractéristiques principales :**
- Comprend votre codebase dans son contexte complet
- Exécute des tâches de manière autonome avec des agents spécialisés
- Demande la permission avant de modifier vos fichiers
- S'intègre nativement dans votre terminal et VS Code
- Extensible via MCP (Model Context Protocol)

## Deux Interfaces Complémentaires

### 1. Claude Code CLI (Terminal)

Interface en ligne de commande pour interagir avec Claude directement dans votre terminal.

**Avantages :**
- Légère et rapide
- Parfaite pour les workflows automatisés
- Scripting et intégration CI/CD
- Contrôle total via flags et options

**Cas d'usage typiques :**
- Analyser rapidement un projet
- Exécuter des tâches ponctuelles
- Automatisation et scripts
- Debugging en ligne de commande

### 2. Claude Code Extension VS Code

Interface graphique native intégrée à Visual Studio Code.

**Avantages :**
- Interface visuelle intuitive
- Système de diff interactif
- Références de fichiers avec @-mentions
- Multiples conversations en parallèle
- Historique des conversations

**Cas d'usage typiques :**
- Développement interactif
- Revue de code visuelle
- Sessions de développement longues
- Collaboration en équipe

## Concepts Clés

### Agents et Sous-agents

Claude Code utilise une architecture multi-agents :

**Agent principal :** Gère la conversation et coordonne les tâches

**Sous-agents spécialisés :**
- **Explore** : Agent rapide en lecture seule pour explorer et analyser le code
- **Plan** : Recherche dans la codebase pour la planification
- **General-purpose** : Agent polyvalent pour tâches complexes multi-étapes

**Exécution parallèle :** Jusqu'à 10 sous-agents peuvent s'exécuter simultanément pour des tâches indépendantes.

**Cas d'usage :**
```
"Génère la documentation pour tous les modules"
→ Agent principal liste les modules
→ 10 sous-agents documentent 10 modules en parallèle
→ Agent principal assemble le tout
```

### Commandes Slash (Slash Commands)

Les commandes slash sont des prompts sauvegardés invoqués avec `/commande`.

**Commandes intégrées utiles :**
- `/init` : Générer un fichier CLAUDE.md pour votre projet
- `/commit` : Créer un commit Git avec message généré
- `/review` : Analyser les changements avant commit
- `/mcp` : Gérer les serveurs MCP
- `/status` : Afficher le statut de connexion

**Commandes personnalisables :** Créez vos propres commandes pour des workflows répétitifs.

### Skills (Compétences)

Les **skills** sont des capacités structurées avec fichiers de support que Claude découvre automatiquement.

**Différences avec les slash commands :**
- **Slash command** : Invoqué explicitement par l'utilisateur (`/test`)
- **Skill** : Invoqué automatiquement par Claude quand pertinent

**Format standard :** Fichier `SKILL.md` définissant la compétence

**Exemples de skills :**
- Correction automatique de tests échoués
- Revue de code selon standards du projet
- Génération de documentation

### Hooks (Déclencheurs)

Les **hooks** sont des automatisations basées sur des événements qui se déclenchent à des moments spécifiques.

**Types de hooks :**
- **Pre-tool hooks** : Avant l'exécution d'un outil
- **Post-tool hooks** : Après l'exécution d'un outil
- **User prompt hooks** : À la soumission d'un prompt utilisateur

**Exemples pratiques :**
- Exécuter les tests après chaque modification de code
- Formater le code avant commit
- Valider les standards de sécurité

### MCP (Model Context Protocol)

MCP est un standard ouvert pour connecter les agents IA à des outils et sources de données externes.

**Serveurs MCP populaires :**
- **Filesystem** : Accès au système de fichiers
- **GitHub** : Intégration GitHub (issues, PRs, etc.)
- **PostgreSQL** : Requêtes de bases de données
- **Web Search** : Recherche web (searxng, brave, etc.)
- **Browser** : Automatisation de navigateur

**Trois types de transport :**
1. **HTTP** : Serveurs distants (recommandé)
2. **Stdio** : Serveurs locaux via ligne de commande
3. **SSE** : Server-Sent Events (déprécié)

**Configuration :**
```bash
# Serveur HTTP distant
claude mcp add --transport http github https://api.githubcopilot.com/mcp/

# Serveur local (stdio)
claude mcp add --transport stdio db -- npx -y @bytebase/dbhub --dsn "postgresql://..."
```

### CLAUDE.md - Mémoire de Projet

Le fichier **CLAUDE.md** est lu automatiquement au début de chaque session.

**Contenu recommandé :**
1. **Stack technique** : Frameworks, langages, versions
2. **Structure du projet** : Organisation des dossiers
3. **Commandes essentielles** : Build, test, déploiement
4. **Conventions de code** : Standards de nommage, formatage
5. **Bonnes pratiques Git** : Branches, commits, PR

**Bonnes pratiques :**
- ✅ Rester concis et universel
- ✅ Se concentrer sur ce qui est vraiment utile
- ✅ Utiliser `/init` comme point de départ
- ❌ Ne pas dupliquer les règles de linters
- ❌ Éviter les informations obsolètes

**Hiérarchie :**
1. `~/.claude/CLAUDE.md` (utilisateur global)
2. `/projet/CLAUDE.md` (racine du projet)
3. `/projet/sous-dossier/CLAUDE.md` (dossiers spécifiques)

### Modes de Permission

Claude Code offre plusieurs niveaux d'autonomie :

**Modes disponibles :**
- **Default** : Demande avant chaque action (recommandé)
- **Auto-accept** : Applique automatiquement les modifications
- **Plan** : Mode planification sans exécution
- **Manual** : Contrôle complet utilisateur

**Configuration par outil :**
```json
{
  "allowedTools": [
    "Read",
    "Bash(git log:*)",
    "Bash(git diff:*)"
  ],
  "disallowedTools": ["Write(/etc/*:*)"]
}
```

## Workflow Typique

### CLI (Terminal)

```bash
# 1. Démarrer une session interactive
claude

# 2. Poser une question
> Explique-moi l'architecture de ce projet

# 3. Demander une modification
> Ajoute des tests pour le module auth

# 4. Continuer la conversation précédente
claude -c

# 5. Query rapide sans interactivité
claude -p "Liste les dépendances obsolètes"
```

### VS Code Extension

1. **Ouvrir Claude** : Cliquer sur l'icône ✱ (spark) ou `Cmd+Shift+P` → "Claude Code"
2. **Référencer du code** : Sélectionner du code puis `Alt+K` pour créer une @-mention
3. **Poser une question** : "Débugge cette fonction"
4. **Revoir les changements** : Examiner les diffs proposés
5. **Accepter/Rejeter** : Valider ou refuser les modifications

## Cas d'Usage Éducatifs

### Apprendre un Nouveau Framework

```
> Je découvre React. Explique-moi ce composant et suggère des améliorations
```

### Débugger du Code

```
> J'ai une erreur dans @app.py:42-58. Aide-moi à comprendre et corriger
```

### Refactoring

```
> Refactorise @legacy.js pour utiliser des fonctions async/await modernes
```

### Documentation

```
> Génère une documentation complète pour tous les modules de src/
```

### Tests Automatisés

```
> Crée des tests unitaires pour @calculator.py avec pytest
```

## Différences avec Roo Code

| Aspect | Claude Code | Roo Code |
|--------|-------------|----------|
| **Développeur** | Anthropic (officiel) | Communauté |
| **Modèles** | Famille Claude (Sonnet, Opus, Haiku) | Multi-modèles (via OpenRouter) |
| **Interface** | CLI + Extension VS Code | Extension VS Code uniquement |
| **MCP** | Support natif complet | Support partiel |
| **Agents** | Sous-agents spécialisés intégrés | Agents personnalisables |
| **Tarification** | Abonnement Claude ou API pay-per-use | Basé sur les modèles utilisés |
| **Ecosystem** | Marketplace officiel | Configuration manuelle |

## Ressources et Documentation

### Documentation Officielle
- [Quickstart](https://code.claude.com/docs/en/quickstart)
- [CLI Reference](https://code.claude.com/docs/en/cli-reference)
- [VS Code Guide](https://code.claude.com/docs/en/vs-code)
- [MCP Documentation](https://code.claude.com/docs/en/mcp)
- [Slash Commands](https://code.claude.com/docs/en/slash-commands)

### GitHub et Communauté
- [Dépôt officiel](https://github.com/anthropics/claude-code)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)
- [MCP Servers Registry](https://github.com/modelcontextprotocol/servers)

### Guides et Tutoriels
- [Complete Guide to CLAUDE.md](https://www.builder.io/blog/claude-md-guide)
- [Best Practices for Agentic Coding](https://www.anthropic.com/engineering/claude-code-best-practices)
- [Cooking with Claude Code](https://www.siddharthbharath.com/claude-code-the-complete-guide/)

### Marketplaces
- [SkillsMP](https://skillsmp.com/) - Marketplace communautaire de skills
- [Claude Marketplaces](https://claudemarketplaces.com/) - Plugins et extensions

---

*Pour l'installation et la configuration, consultez le guide [INSTALLATION-CLAUDE-CODE.md](./INSTALLATION-CLAUDE-CODE.md)*

*Pour approfondir les concepts (Skills, Subagents, Hooks, MCP), consultez [CONCEPTS-AVANCES.md](./CONCEPTS-AVANCES.md)*
