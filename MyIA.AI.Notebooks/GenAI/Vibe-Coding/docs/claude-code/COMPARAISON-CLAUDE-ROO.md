# Comparaison : Claude Code vs Roo Code

Guide comparatif détaillé pour comprendre les différences entre Claude Code et Roo Code, et choisir le bon outil selon vos besoins.

## 📊 Vue d'Ensemble

| Critère | Claude Code | Roo Code |
|---------|-------------|----------|
| **Développeur** | Anthropic (officiel) | Communauté open-source |
| **Type** | Outil agentique natif | Extension VS Code |
| **Interfaces** | CLI + Extension VS Code | Extension VS Code uniquement |
| **Première sortie** | 2024 | 2024 |
| **Open Source** | Non (propriétaire) | Oui (fork de Cline) |
| **Documentation** | Officielle complète | Communautaire |

## 🎯 Philosophie et Approche

### Claude Code
**"Agentic coding with AI that understands your codebase"**

- Focus sur l'**autonomie** et l'**exécution**
- Architecture **multi-agents** sophistiquée
- Intégration **native** terminal et IDE
- Optimisé pour les **workflows professionnels**
- Support **officiel** Anthropic

### Roo Code
**"AI coding assistant for VS Code"**

- Focus sur la **collaboration** humain-AI
- Interface **graphique** intuitive
- **Multi-modèles** flexible (OpenRouter)
- Communauté **active** et contributions
- Personnalisation **extensive**

## 🔧 Installation et Configuration

### Installation

| Aspect | Claude Code | Roo Code |
|--------|-------------|----------|
| **Méthode** | Installateur natif ou npm | Extension VS Code uniquement |
| **Prérequis** | Aucun (natif) ou Node.js 18+ | VS Code 1.60+ |
| **Taille** | ~100 MB (natif) | ~5 MB (extension) |
| **Plateformes** | Windows, macOS, Linux, WSL | Windows, macOS, Linux |
| **Temps install** | 2-5 minutes | 1-2 minutes |

### Configuration Modèles

**Claude Code avec OpenRouter :**
```bash
# Variables d'environnement
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="VOTRE_CLE"
export ANTHROPIC_API_KEY=""
```

**Roo Code avec OpenRouter :**
```json
// Via interface graphique des paramètres
{
  "provider": "OpenRouter",
  "apiKey": "VOTRE_CLE",
  "model": "anthropic/claude-sonnet-4"
}
```

**Verdict :** Roo Code est plus simple à configurer via l'interface graphique.

## 🤖 Modèles et Providers

### Claude Code

| Aspect | Détails |
|--------|---------|
| **Modèles natifs** | Claude Sonnet, Opus, Haiku (via Anthropic) |
| **Aliases** | `sonnet`, `opus`, `haiku` |
| **Avec OpenRouter** | Tous modèles OpenRouter disponibles |
| **Fallback** | Support fallback automatique |
| **Streaming** | Oui |

### Roo Code

| Aspect | Détails |
|--------|---------|
| **Modèles** | Tous via OpenRouter (100+ modèles) |
| **Providers** | OpenRouter, Anthropic, OpenAI, Google, etc. |
| **Profils** | Système de profils pour changer rapidement |
| **Multi-modèles** | Utilisation simultanée possible |
| **Streaming** | Oui |

**Verdict :** Roo Code offre plus de flexibilité pour tester différents modèles.

## 🎨 Interface Utilisateur

### Claude Code CLI

**Points forts :**
- ✅ Léger et rapide
- ✅ Scriptable et automatisable
- ✅ Parfait pour CI/CD
- ✅ Contrôle total via flags

**Points faibles :**
- ❌ Courbe d'apprentissage pour les flags
- ❌ Pas de visualisation graphique
- ❌ Moins intuitif pour débutants

### Claude Code Extension VS Code

**Points forts :**
- ✅ Interface native VS Code
- ✅ Diffs interactifs visuels
- ✅ @-mentions avec sélection
- ✅ Multiples conversations (tabs/windows)
- ✅ Historique persistant

**Points faibles :**
- ❌ Moins de contrôle que CLI
- ❌ Nécessite VS Code ouvert

### Roo Code Extension

**Points forts :**
- ✅ Interface graphique très intuitive
- ✅ Panneau de configuration visuel
- ✅ Gestion profils modèles facile
- ✅ Marketplace intégré
- ✅ Meilleure pour débutants

**Points faibles :**
- ❌ Pas de CLI
- ❌ Moins scriptable
- ❌ Dépendant de VS Code

**Verdict :** Roo Code est plus accessible pour débutants, Claude Code CLI plus puissant pour experts.

## 🔌 Extensibilité (MCP)

### Claude Code

| Aspect | Support |
|--------|---------|
| **MCP natif** | ✅ Complet |
| **Transports** | HTTP, Stdio, SSE |
| **Configuration** | CLI (`claude mcp`) ou fichiers JSON |
| **Scopes** | User, Project, Local |
| **Tool Search** | ✅ Automatique si >10% contexte |
| **Resources** | ✅ Via @-mentions |
| **Prompts** | ✅ Deviennent slash commands |
| **OAuth** | ✅ Support intégré |

### Roo Code

| Aspect | Support |
|--------|---------|
| **MCP** | ✅ Support partiel |
| **Transports** | Principalement Stdio |
| **Configuration** | Interface graphique + JSON |
| **Scopes** | Project principalement |
| **Tool Search** | ❌ Non |
| **Resources** | ⚠️ Support limité |
| **Prompts** | ⚠️ Support limité |
| **OAuth** | ❌ Configuration manuelle |

**Verdict :** Claude Code a un support MCP nettement plus complet et mature.

## 🚀 Agents et Parallélisation

### Claude Code - Sous-agents Intégrés

**Agents spécialisés :**
- **Explore** : Lecture seule, recherche rapide
- **Plan** : Recherche pour planification
- **General-purpose** : Tâches complexes multi-étapes

**Capacités :**
- ✅ Jusqu'à **10 agents parallèles** simultanément
- ✅ Agents **personnalisables** via JSON
- ✅ Délégation **automatique** des tâches
- ✅ Gestion **contexte** indépendant par agent

**Exemple :**
```bash
claude --agents '{
  "reviewer": {
    "description": "Code reviewer",
    "prompt": "Expert en qualité code",
    "tools": ["Read", "Grep"]
  }
}'
```

### Roo Code - Agents Configurables

**Capacités :**
- ⚠️ Pas de système de sous-agents natif
- ✅ Workflow **séquentiel** optimisé
- ✅ Configuration **skills** personnalisés
- ❌ Pas de parallélisation native

**Verdict :** Claude Code est **largement supérieur** pour tâches complexes nécessitant parallélisation.

## 📝 Mémoire et Contexte

### Claude Code - CLAUDE.md

**Format :**
```markdown
# Stack Technique
- TypeScript 5.3
- React 18

# Commandes
- `npm test` : Tests
```

**Caractéristiques :**
- ✅ Hiérarchie (user / project / directory)
- ✅ Importation avec `@path/to/file`
- ✅ Lecture automatique au démarrage
- ✅ Génération via `/init`

### Roo Code - Configuration Projet

**Format :**
```json
{
  "projectContext": "...",
  "customInstructions": "...",
  "skills": [...]
}
```

**Caractéristiques :**
- ✅ Configuration via interface graphique
- ✅ Instructions personnalisées
- ❌ Pas de système hiérarchique
- ❌ Pas d'importation de fichiers

**Verdict :** Claude Code offre un système plus flexible et structuré.

## 🎭 Skills et Commands

### Claude Code

**Skills :**
- Format standard `SKILL.md`
- Auto-découverte
- Invocation automatique par l'AI
- Compatible avec ecosystem

**Slash Commands :**
- Intégrés : `/init`, `/commit`, `/review`, `/mcp`
- Personnalisables
- Deviennent skills automatiquement

**Marketplace :**
- [SkillsMP](https://skillsmp.com/)
- Installation one-click
- Communauté active

### Roo Code

**Skills :**
- Configuration manuelle
- Format propriétaire
- Marketplace intégré dans l'extension

**Slash Commands :**
- Configuration via settings
- Interface graphique
- Moins de commandes intégrées

**Verdict :** Claude Code a un ecosystem plus mature et standardisé.

## 🪝 Hooks et Automatisation

### Claude Code

**Types de hooks :**
```json
{
  "hooks": {
    "user-prompt-submit": "run_tests.sh",
    "pre-tool": {
      "Write": "format_code.sh"
    },
    "post-tool": {
      "Bash": "check_syntax.sh"
    }
  }
}
```

**Capacités :**
- ✅ Pre-tool, Post-tool, User-prompt
- ✅ Configuration par outil
- ✅ Interface `/hooks` dédiée
- ✅ Scripts shell support

### Roo Code

**Hooks :**
- ⚠️ Support limité
- Configuration manuelle
- Moins de types de hooks

**Verdict :** Claude Code offre un système de hooks plus complet.

## 💰 Coût et Tarification

### Claude Code

**Options :**
1. **Abonnement Claude** (Pro/Max/Teams/Enterprise)
   - Modèles Anthropic inclus
   - Modèles tiers via OpenRouter facturés séparément

2. **API Anthropic** (pay-per-use)
   - Facturation à l'utilisation

3. **Via OpenRouter uniquement**
   - Tous modèles facturés par OpenRouter

**Coûts typiques (avec OpenRouter) :**
- Claude Sonnet 4 : ~$3 / 1M tokens input
- Claude Opus 4 : ~$15 / 1M tokens input

### Roo Code

**Options :**
- **OpenRouter** (principal)
- **API directes** (Anthropic, OpenAI, etc.)
- **Providers gratuits** possibles

**Coûts :** Identiques à Claude Code si même modèle via OpenRouter

**Verdict :** Coûts similaires, flexibilité équivalente avec OpenRouter.

## 🔒 Sécurité et Permissions

### Claude Code

**Niveaux de permission :**
- `default` : Demande avant chaque action
- `auto-accept` : Accepte automatiquement
- `plan` : Planification sans exécution

**Configuration fine :**
```json
{
  "allowedTools": ["Read", "Bash(git:*)"],
  "disallowedTools": ["Write(/etc/*:*)"]
}
```

**Sécurité :**
- ✅ Sandboxing natif
- ✅ Granularité par outil
- ✅ Patterns d'exclusion
- ✅ Audit trail

### Roo Code

**Permissions :**
- Système d'approbation manuel
- Moins de granularité

**Verdict :** Claude Code offre un contrôle plus fin et professionnel.

## 📚 Documentation et Support

### Claude Code

**Documentation :**
- ✅ [Officielle complète](https://code.claude.com/docs)
- ✅ Guides étape par étape
- ✅ Exemples pratiques
- ✅ Changelog détaillé

**Support :**
- ✅ Support officiel Anthropic
- ✅ GitHub Issues actif
- ✅ Communauté Discord
- ✅ Guides tiers nombreux

### Roo Code

**Documentation :**
- ⚠️ Communautaire principalement
- ⚠️ Moins structurée
- ✅ Tutoriels vidéo
- ✅ README GitHub

**Support :**
- ✅ Communauté active
- ✅ GitHub Issues
- ❌ Pas de support officiel

**Verdict :** Claude Code bénéficie d'un support professionnel.

## 🎓 Cas d'Usage Recommandés

### Choisir Claude Code si...

✅ Vous voulez un outil **professionnel** et **supporté**
✅ Vous avez besoin de **parallélisation** de tâches
✅ Vous utilisez principalement la **famille Claude**
✅ Vous voulez une **intégration MCP complète**
✅ Vous travaillez en **équipe** avec standards
✅ Vous avez besoin de **CLI** pour automatisation
✅ Vous cherchez **stabilité** et **fiabilité**

**Idéal pour :**
- Développement professionnel
- Projets d'équipe
- CI/CD et automatisation
- Tâches complexes multi-fichiers
- Génération de documentation
- Refactoring à grande échelle

### Choisir Roo Code si...

✅ Vous êtes **débutant** avec les AI coding tools
✅ Vous voulez tester **différents modèles** facilement
✅ Vous préférez une **interface graphique** simple
✅ Vous avez un **budget limité** (modèles moins chers)
✅ Vous voulez **personnaliser** extensivement
✅ Vous travaillez **solo** sur petits projets
✅ Vous aimez l'**open source** et contribuer

**Idéal pour :**
- Apprentissage et expérimentation
- Projets personnels
- Développement rapide (prototypage)
- Tests de différents modèles LLM
- Petites modifications ponctuelles
- Utilisateurs débutants en AI

## 🔄 Migration entre Outils

### De Roo Code vers Claude Code

**Avantages :**
- ✅ Gain en **performance** et **parallélisation**
- ✅ Support **MCP** plus complet
- ✅ **CLI** pour automatisation
- ✅ Documentation **professionnelle**

**Étapes :**
1. Installer Claude Code (CLI + Extension)
2. Configurer OpenRouter (mêmes clés)
3. Créer `CLAUDE.md` (équivalent config Roo)
4. Migrer MCP servers vers `.mcp.json`
5. Recréer skills si nécessaire

### De Claude Code vers Roo Code

**Avantages :**
- ✅ Interface plus **intuitive**
- ✅ **Multi-modèles** plus facile
- ✅ **Open source** et personnalisable

**Étapes :**
1. Installer extension Roo Code
2. Configurer profils modèles
3. Transférer instructions de CLAUDE.md
4. Adapter configuration MCP si supporté

## 🏆 Récapitulatif et Recommandations

### Tableau Synthèse

| Critère | Claude Code | Roo Code | Gagnant |
|---------|-------------|----------|---------|
| **Facilité installation** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Roo |
| **Interface utilisateur** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Roo |
| **Puissance (agents)** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Claude |
| **MCP Support** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Claude |
| **Flexibilité modèles** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Roo |
| **Documentation** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Claude |
| **Automatisation** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | Claude |
| **Communauté** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Égalité |
| **Prix** | ⭐⭐⭐ | ⭐⭐⭐⭐ | Roo |
| **Courbe apprentissage** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Roo |

### Recommandation Générale

**Pour la formation EPF 2026 :**

1. **Débutants** : Commencer avec **Roo Code**
   - Plus accessible
   - Interface intuitive
   - Moins intimidant

2. **Intermédiaires** : Essayer les **deux**
   - Comparer workflows
   - Identifier préférences
   - Comprendre forces/faiblesses

3. **Avancés** : Préférer **Claude Code**
   - Exploiter parallélisation
   - Utiliser CLI pour automation
   - Workflows professionnels

**Dans la pratique :**
- **Roo Code** pour petites tâches rapides et expérimentation
- **Claude Code** pour projets sérieux et développement d'équipe
- **Les deux** peuvent coexister sans problème !

## 📖 Ressources Complémentaires

### Claude Code
- [Documentation officielle](https://code.claude.com/docs)
- [Best practices](https://www.anthropic.com/engineering/claude-code-best-practices)
- [GitHub](https://github.com/anthropics/claude-code)

### Roo Code
- Basé sur [Cline](https://github.com/cline/cline)
- [Documentation Roo](https://docs.roo.dev)
- Communauté Discord

### Comparaisons Tiers
- [Builder.io Guide](https://www.builder.io/blog/claude-code)
- [WhyTryAI Comparison](https://www.whytryai.com/p/claude-code-beginner-guide)

---

**Conclusion :** Les deux outils ont leur place. Claude Code excelle en puissance et professionnalisme, Roo Code en accessibilité et flexibilité. Choisissez selon vos besoins et votre niveau ! 🚀
