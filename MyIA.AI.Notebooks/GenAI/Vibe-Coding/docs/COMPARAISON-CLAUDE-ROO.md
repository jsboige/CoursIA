# Comparaison : Claude Code vs Roo Code

Guide comparatif détaillé pour comprendre les différences entre Claude Code et Roo Code, et choisir le bon outil selon vos besoins.

> Sources : [code.claude.com/docs](https://code.claude.com/docs) | [docs.roocode.com](https://docs.roocode.com)

## Vue d'Ensemble

| Critère | Claude Code | Roo Code |
| --- | --- | --- |
| **Développeur** | Anthropic (officiel) | Communauté open-source |
| **Type** | Outil agentique natif | Extension VS Code |
| **Interfaces** | CLI + Extension VS Code | Extension VS Code uniquement |
| **Open Source** | Non (propriétaire) | Oui (fork de Cline) |
| **Documentation** | Officielle complète | Communautaire + docs.roocode.com |

## Philosophie et Approche

### Claude Code - "Agentic coding"

- Focus sur l'**autonomie** et l'**exécution**
- Architecture **multi-agents** sophistiquée (sous-agents parallèles)
- Intégration **native** terminal et IDE
- Optimise pour les **workflows professionnels**
- Support **officiel** Anthropic

### Roo Code - "AI coding assistant"

- Focus sur la **collaboration** humain-AI
- Interface **graphique** intuitive
- **Multi-modèles** flexible (OpenRouter natif)
- Système de **modes** personnalisables (Architect, Code, Ask, Debug)
- Communauté **active** et contributions open-source

## Installation et Configuration

| Aspect | Claude Code | Roo Code |
| --- | --- | --- |
| **Méthode** | npm ou installateur natif | Extension VS Code |
| **Prérequis** | Node.js 18+ (npm) ou aucun (natif) | VS Code 1.60+ |
| **Plateformes** | Windows, macOS, Linux, WSL | Windows, macOS, Linux |
| **Temps install** | 2-5 minutes | 1-2 minutes |

### Configuration des modèles

**Claude Code avec OpenRouter :**

```bash
# Via variables d'environnement
export ANTHROPIC_BASE_URL="https://openrouter.ai/api"
export ANTHROPIC_AUTH_TOKEN="sk-or-v1-VOTRE_CLE"
export ANTHROPIC_API_KEY=""
```

Ou via `~/.claude/settings.json` :

```json
{
  "env": {
    "ANTHROPIC_BASE_URL": "https://openrouter.ai/api",
    "ANTHROPIC_AUTH_TOKEN": "sk-or-v1-VOTRE_CLE",
    "ANTHROPIC_API_KEY": ""
  }
}
```

**Roo Code avec OpenRouter :**

Configuration via l'interface graphique des paramètres (Prompts Tab), choix du provider OpenRouter et saisie de la clé API.

**Verdict :** Roo Code est plus simple a configurer grâce a son interface graphique. Claude Code offre plus de flexibilité via fichiers et variables d'environnement.

## Modèles et Providers

### Modèles Claude Code

| Aspect | Détails |
| --- | --- |
| **Modèles natifs** | Claude Sonnet 4.5, Opus 4.6, Haiku 4.5 |
| **Aliases** | `sonnet`, `opus`, `haiku` |
| **Avec OpenRouter** | Tous modèles OpenRouter disponibles |
| **Aliases alternatifs** | `ANTHROPIC_DEFAULT_OPUS_MODEL`, etc. |

### Modèles Roo Code

| Aspect | Détails |
| --- | --- |
| **Modèles** | Tous via OpenRouter (100+ modèles) |
| **Providers** | OpenRouter, Anthropic, OpenAI, Google, etc. |
| **Profils** | Système de profils pour changer rapidement |
| **Par mode** | Modèle différent par mode (Code, Architect, etc.) |

**Verdict :** Roo Code offre plus de flexibilité native pour tester différents modèles. Claude Code rattrape avec les aliases OpenRouter.

## Interface Utilisateur

### Claude Code CLI

**Points forts :** léger et rapide, scriptable et automatisable, parfait pour CI/CD, contrôle total via flags.

**Points faibles :** courbe d'apprentissage pour les flags, pas de visualisation graphique native.

### Claude Code Extension VS Code

**Points forts :** interface native VS Code, diffs interactifs visuels, @-mentions avec sélection, multiples conversations (tabs/windows), historique persistant.

### Roo Code Extension

**Points forts :** interface graphique très intuitive, panneau de configuration visuel, gestion profils modèles facile, modes spécialisés (Architect, Code, Ask, Debug).

**Points faibles :** pas de CLI, moins scriptable, dépendant de VS Code.

**Verdict :** Roo Code est plus accessible pour débutants. Claude Code CLI est plus puissant pour experts et automatisation.

## Extensibilité (MCP)

### Support MCP Claude Code

| Aspect | Support |
| --- | --- |
| **MCP natif** | Complet |
| **Transports** | HTTP, Stdio, SSE |
| **Configuration** | CLI (`claude mcp`) ou fichiers JSON |
| **Scopes** | User, Project, Local |
| **Tool Search** | Automatique si >10% contexte |
| **Resources** | Via @-mentions |
| **Prompts** | Deviennent slash commands |
| **OAuth** | Support intégré |

### Support MCP Roo Code

| Aspect | Support |
| --- | --- |
| **MCP** | Support complet (Stdio) |
| **Transports** | Principalement Stdio, SSE |
| **Configuration** | Interface graphique + JSON |
| **Scopes** | Project principalement |
| **Tool Search** | Non |
| **Resources** | Support partiel |

**Verdict :** Claude Code a un support MCP nettement plus complet et mature, notamment pour les serveurs HTTP et le tool search.

## Agents et Parallélisation

### Claude Code - Sous-agents Intégrés

Agents spécialisés :

- **Explore** : Lecture seule, recherche rapide (modèle Haiku)
- **Plan** : Recherche pour planification
- **Général-purpose** : Tâches complexes multi-étapes

Capacites :

- Jusqu'a **10 agents parallèles** simultanement
- Agents **personnalisables** via fichiers `.claude/agents/*.md`
- Delegation **automatique** basee sur la description
- Gestion **contexte** independant par agent

### Roo Code - Modes et Boomerang

Modes intégrés :

- **Code** : Écriture et modification de code
- **Architect** : Planification et architecture
- **Ask** : Questions et recherche
- **Debug** : Debugging et correction

Capacites :

- **Custom modes** personnalisables (`.roomodes`)
- Workflow **séquentiel** optimise
- Pattern **Boomerang** pour orchestration multi-mode
- Pas de parallélisation native

**Verdict :** Claude Code est supérieur pour les tâches complexes nécessitant parallélisation. Roo Code compense avec ses modes spécialisés et le pattern Boomerang.

## Mémoire et Contexte

### Claude Code - Système CLAUDE.md

**Hiérarchie (priorité croissante) :**

1. `~/.claude/CLAUDE.md` : Instructions globales personnelles
1. `CLAUDE.md` ou `.claude/CLAUDE.md` : Instructions projet (equipe)
1. `.claude/CLAUDE.local.md` : Instructions projet personnelles
1. Sous-dossiers : `CLAUDE.md` par repertoire

**Complément :** `.claude/rules/*.md` pour règles modulaires avec scoping par fichier (frontmatter `globs`).

### Roo Code - Système de Rules

**Hiérarchie :**

1. Instructions globales via UI (Prompts Tab)
1. `~/.roo/rules/` : Règles globales
1. `~/.roo/rules-{mode}/` : Règles globales par mode
1. `.roo/rules/` : Règles projet
1. `.roo/rules-{mode}/` : Règles projet par mode
1. `.roorules` / `.roorules-{mode}` : Fichiers alternatifs
1. `AGENTS.md` : Instructions agent d'equipe

**Verdict :** Les deux systèmes sont riches. Claude Code favorise CLAUDE.md + rules, Roo Code offre un scoping par mode plus fin.

## Skills et Commands

### Claude Code - Skills et Slash Commands

**Skills** (`.claude/skills/*/SKILL.md`) :

- Format standardise avec frontmatter YAML
- Auto-decouverte et application automatique par Claude
- Support des fichiers de référence et scripts
- Marketplace communautaire ([SkillsMP](https://skillsmp.com/))

**Slash Commands intégrés :** `/init`, `/commit`, `/review`, `/mcp`, `/status`, `/hooks`, `/memory`

### Roo Code - Modes personnalisés

**Custom Modes** (`.roomodes`) :

- Définition de modes avec outils autorises
- Restrictions de fichiers par mode
- Configuration via interface graphique
- Partage possible via le depot

**Verdict :** Claude Code a un ecosysteme skills plus mature et standardise. Roo Code compense avec ses custom modes flexibles.

## Hooks et Automatisation

### Claude Code - Hooks complets

Types de hooks :

- `PreToolUse` / `PostToolUse` : Avant/après chaque outil
- `UserPromptSubmit` : A la soumission d'un prompt
- `SessionStart` / `SessionEnd` : Debut/fin de session
- `Notification`, `Stop`, `SubagentStart/Stop`, `PreCompact`

Configuration dans `settings.json` :

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Write",
        "hooks": [
          {
            "type": "command",
            "command": "python check_file.py"
          }
        ]
      }
    ]
  }
}
```

### Roo Code - Automatisation limitee

- Support des hooks basique via configuration
- Moins de points d'accroche que Claude Code
- Automatisation principalement via les modes

**Verdict :** Claude Code offre un système de hooks nettement plus complet et granulaire.

## Sécurité et Permissions

### Claude Code - Système granulaire

**Modes de permission :** `default`, `acceptEdits`, `plan`, `auto-accept`

**Règles fines :**

```json
{
  "permissions": {
    "allow": ["Read", "Bash(npm run *)"],
    "deny": ["Read(.env)", "Bash(rm -rf *)"],
    "ask": ["Bash(git push *)"]
  }
}
```

**Sandbox :** Isolation des commandes avec contrôle réseau (macOS/Linux).

### Roo Code - Approbation manuelle

- Système d'approbation par action
- Auto-approve configurable par mode
- Moins de granularite que Claude Code

**Verdict :** Claude Code offre un contrôle plus fin et professionnel, avec le sandbox en plus.

## Coût et Tarification

Les coûts sont identiques si le même modèle est utilise via OpenRouter.

**Coûts typiques OpenRouter :**

- Claude Sonnet 4.5 : ~$3 / 1M tokens input
- Claude Opus 4.6 : ~$15 / 1M tokens input
- Modèles alternatifs (GLM, Qwen) : souvent moins cher

**Verdict :** Coûts similaires, flexibilité équivalente avec OpenRouter.

## Documentation et Support

### Claude Code

- Documentation officielle complète : [code.claude.com/docs](https://code.claude.com/docs)
- Best practices officielles : [code.claude.com/docs/en/best-practices](https://code.claude.com/docs/en/best-practices)
- Support officiel Anthropic
- Communauté Discord et GitHub active
- Guides tiers nombreux ([Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code))

### Roo Code

- Documentation officielle : [docs.roocode.com](https://docs.roocode.com)
- Communauté active Discord et GitHub
- Tutoriels vidéo et guides communautaires
- Open source : contributions bienvenues

## Cas d'Usage Recommandes

### Préférer Claude Code pour

- Développement **professionnel** et **supporté**
- **Parallélisation** de tâches (sous-agents)
- Intégration **CLI** pour automatisation et CI/CD
- Support **MCP** complet
- Travail en **equipe** avec standards partages
- Projets nécessitant **sécurité granulaire** (sandbox, permissions)

### Préférer Roo Code pour

- **Débutants** avec les AI coding tools
- Tester **différents modèles** facilement
- Interface **graphique** intuitive
- **Custom modes** spécialisés (Architect, Debug)
- Projets **open source** et personnalisation poussee
- **Budget limite** (modèles alternatifs moins chers)

### Recommandation pour la formation EPF 2026

1. **Débutants** : Commencer avec **Roo Code** (plus accessible, interface intuitive)
1. **Intermédiaires** : Essayer les **deux** (comparer workflows, identifier préférences)
1. **Avancés** : Préférer **Claude Code** (parallélisation, CLI, workflows professionnels)

Les deux outils peuvent coexister sans problème dans VS Code.

## Tableau Synthese

| Critère | Claude Code | Roo Code |
| --- | --- | --- |
| Facilite installation | 3/5 | 5/5 |
| Interface utilisateur | 4/5 | 5/5 |
| Puissance (agents) | 5/5 | 3/5 |
| MCP Support | 5/5 | 3/5 |
| Flexibilité modèles | 4/5 | 5/5 |
| Documentation | 5/5 | 4/5 |
| Automatisation | 5/5 | 3/5 |
| Sécurité | 5/5 | 3/5 |
| Courbe apprentissage | 3/5 | 5/5 |

## Ressources

### Claude Code

- [Documentation officielle](https://code.claude.com/docs)
- [Best practices](https://code.claude.com/docs/en/best-practices)
- [GitHub](https://github.com/anthropics/claude-code)
- [Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code)

### Roo Code

- [Documentation officielle](https://docs.roocode.com)
- [GitHub](https://github.com/RooVetGit/Roo-Code)
- [VS Code Marketplace](https://marketplace.visualstudio.com/items?itemName=RooVet.roo-cline)

---

**Conclusion :** Les deux outils ont leur place. Claude Code excelle en puissance et professionnalisme, Roo Code en accessibilité et flexibilité. Choisissez selon vos besoins et votre niveau.
