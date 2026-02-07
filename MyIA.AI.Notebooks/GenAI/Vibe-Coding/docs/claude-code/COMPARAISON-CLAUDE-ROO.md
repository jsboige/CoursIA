# Comparaison : Claude Code vs Roo Code

Guide comparatif detaille pour comprendre les differences entre Claude Code et Roo Code, et choisir le bon outil selon vos besoins.

> Sources : [code.claude.com/docs](https://code.claude.com/docs) | [docs.roocode.com](https://docs.roocode.com)

## Vue d'Ensemble

| Critere | Claude Code | Roo Code |
| --- | --- | --- |
| **Developpeur** | Anthropic (officiel) | Communaute open-source |
| **Type** | Outil agentique natif | Extension VS Code |
| **Interfaces** | CLI + Extension VS Code | Extension VS Code uniquement |
| **Open Source** | Non (proprietaire) | Oui (fork de Cline) |
| **Documentation** | Officielle complete | Communautaire + docs.roocode.com |

## Philosophie et Approche

### Claude Code - "Agentic coding"

- Focus sur l'**autonomie** et l'**execution**
- Architecture **multi-agents** sophistiquee (sous-agents paralleles)
- Integration **native** terminal et IDE
- Optimise pour les **workflows professionnels**
- Support **officiel** Anthropic

### Roo Code - "AI coding assistant"

- Focus sur la **collaboration** humain-AI
- Interface **graphique** intuitive
- **Multi-modeles** flexible (OpenRouter natif)
- Systeme de **modes** personnalisables (Architect, Code, Ask, Debug)
- Communaute **active** et contributions open-source

## Installation et Configuration

| Aspect | Claude Code | Roo Code |
| --- | --- | --- |
| **Methode** | npm ou installateur natif | Extension VS Code |
| **Prerequis** | Node.js 18+ (npm) ou aucun (natif) | VS Code 1.60+ |
| **Plateformes** | Windows, macOS, Linux, WSL | Windows, macOS, Linux |
| **Temps install** | 2-5 minutes | 1-2 minutes |

### Configuration des modeles

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

Configuration via l'interface graphique des parametres (Prompts Tab), choix du provider OpenRouter et saisie de la cle API.

**Verdict :** Roo Code est plus simple a configurer grace a son interface graphique. Claude Code offre plus de flexibilite via fichiers et variables d'environnement.

## Modeles et Providers

### Modeles Claude Code

| Aspect | Details |
| --- | --- |
| **Modeles natifs** | Claude Sonnet 4.5, Opus 4.6, Haiku 4.5 |
| **Aliases** | `sonnet`, `opus`, `haiku` |
| **Avec OpenRouter** | Tous modeles OpenRouter disponibles |
| **Aliases alternatifs** | `ANTHROPIC_DEFAULT_OPUS_MODEL`, etc. |

### Modeles Roo Code

| Aspect | Details |
| --- | --- |
| **Modeles** | Tous via OpenRouter (100+ modeles) |
| **Providers** | OpenRouter, Anthropic, OpenAI, Google, etc. |
| **Profils** | Systeme de profils pour changer rapidement |
| **Par mode** | Modele different par mode (Code, Architect, etc.) |

**Verdict :** Roo Code offre plus de flexibilite native pour tester differents modeles. Claude Code rattrape avec les aliases OpenRouter.

## Interface Utilisateur

### Claude Code CLI

**Points forts :** leger et rapide, scriptable et automatisable, parfait pour CI/CD, controle total via flags.

**Points faibles :** courbe d'apprentissage pour les flags, pas de visualisation graphique native.

### Claude Code Extension VS Code

**Points forts :** interface native VS Code, diffs interactifs visuels, @-mentions avec selection, multiples conversations (tabs/windows), historique persistant.

### Roo Code Extension

**Points forts :** interface graphique tres intuitive, panneau de configuration visuel, gestion profils modeles facile, modes specialises (Architect, Code, Ask, Debug).

**Points faibles :** pas de CLI, moins scriptable, dependant de VS Code.

**Verdict :** Roo Code est plus accessible pour debutants. Claude Code CLI est plus puissant pour experts et automatisation.

## Extensibilite (MCP)

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
| **OAuth** | Support integre |

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

## Agents et Parallelisation

### Claude Code - Sous-agents Integres

Agents specialises :

- **Explore** : Lecture seule, recherche rapide (modele Haiku)
- **Plan** : Recherche pour planification
- **General-purpose** : Taches complexes multi-etapes

Capacites :

- Jusqu'a **10 agents paralleles** simultanement
- Agents **personnalisables** via fichiers `.claude/agents/*.md`
- Delegation **automatique** basee sur la description
- Gestion **contexte** independant par agent

### Roo Code - Modes et Boomerang

Modes integres :

- **Code** : Ecriture et modification de code
- **Architect** : Planification et architecture
- **Ask** : Questions et recherche
- **Debug** : Debugging et correction

Capacites :

- **Custom modes** personnalisables (`.roomodes`)
- Workflow **sequentiel** optimise
- Pattern **Boomerang** pour orchestration multi-mode
- Pas de parallelisation native

**Verdict :** Claude Code est superieur pour les taches complexes necessitant parallelisation. Roo Code compense avec ses modes specialises et le pattern Boomerang.

## Memoire et Contexte

### Claude Code - Systeme CLAUDE.md

**Hierarchie (priorite croissante) :**

1. `~/.claude/CLAUDE.md` : Instructions globales personnelles
1. `CLAUDE.md` ou `.claude/CLAUDE.md` : Instructions projet (equipe)
1. `.claude/CLAUDE.local.md` : Instructions projet personnelles
1. Sous-dossiers : `CLAUDE.md` par repertoire

**Complement :** `.claude/rules/*.md` pour regles modulaires avec scoping par fichier (frontmatter `globs`).

### Roo Code - Systeme de Rules

**Hierarchie :**

1. Instructions globales via UI (Prompts Tab)
1. `~/.roo/rules/` : Regles globales
1. `~/.roo/rules-{mode}/` : Regles globales par mode
1. `.roo/rules/` : Regles projet
1. `.roo/rules-{mode}/` : Regles projet par mode
1. `.roorules` / `.roorules-{mode}` : Fichiers alternatifs
1. `AGENTS.md` : Instructions agent d'equipe

**Verdict :** Les deux systemes sont riches. Claude Code favorise CLAUDE.md + rules, Roo Code offre un scoping par mode plus fin.

## Skills et Commands

### Claude Code - Skills et Slash Commands

**Skills** (`.claude/skills/*/SKILL.md`) :

- Format standardise avec frontmatter YAML
- Auto-decouverte et application automatique par Claude
- Support des fichiers de reference et scripts
- Marketplace communautaire ([SkillsMP](https://skillsmp.com/))

**Slash Commands integres :** `/init`, `/commit`, `/review`, `/mcp`, `/status`, `/hooks`, `/memory`

### Roo Code - Modes personnalises

**Custom Modes** (`.roomodes`) :

- Definition de modes avec outils autorises
- Restrictions de fichiers par mode
- Configuration via interface graphique
- Partage possible via le depot

**Verdict :** Claude Code a un ecosysteme skills plus mature et standardise. Roo Code compense avec ses custom modes flexibles.

## Hooks et Automatisation

### Claude Code - Hooks complets

Types de hooks :

- `PreToolUse` / `PostToolUse` : Avant/apres chaque outil
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

**Verdict :** Claude Code offre un systeme de hooks nettement plus complet et granulaire.

## Securite et Permissions

### Claude Code - Systeme granulaire

**Modes de permission :** `default`, `acceptEdits`, `plan`, `auto-accept`

**Regles fines :**

```json
{
  "permissions": {
    "allow": ["Read", "Bash(npm run *)"],
    "deny": ["Read(.env)", "Bash(rm -rf *)"],
    "ask": ["Bash(git push *)"]
  }
}
```

**Sandbox :** Isolation des commandes avec controle reseau (macOS/Linux).

### Roo Code - Approbation manuelle

- Systeme d'approbation par action
- Auto-approve configurable par mode
- Moins de granularite que Claude Code

**Verdict :** Claude Code offre un controle plus fin et professionnel, avec le sandbox en plus.

## Cout et Tarification

Les couts sont identiques si le meme modele est utilise via OpenRouter.

**Couts typiques OpenRouter :**

- Claude Sonnet 4.5 : ~$3 / 1M tokens input
- Claude Opus 4.6 : ~$15 / 1M tokens input
- Modeles alternatifs (GLM, Qwen) : souvent moins cher

**Verdict :** Couts similaires, flexibilite equivalente avec OpenRouter.

## Documentation et Support

### Claude Code

- Documentation officielle complete : [code.claude.com/docs](https://code.claude.com/docs)
- Best practices officielles : [code.claude.com/docs/en/best-practices](https://code.claude.com/docs/en/best-practices)
- Support officiel Anthropic
- Communaute Discord et GitHub active
- Guides tiers nombreux ([Awesome Claude Code](https://github.com/hesreallyhim/awesome-claude-code))

### Roo Code

- Documentation officielle : [docs.roocode.com](https://docs.roocode.com)
- Communaute active Discord et GitHub
- Tutoriels video et guides communautaires
- Open source : contributions bienvenues

## Cas d'Usage Recommandes

### Preferer Claude Code pour

- Developpement **professionnel** et **supporte**
- **Parallelisation** de taches (sous-agents)
- Integration **CLI** pour automatisation et CI/CD
- Support **MCP** complet
- Travail en **equipe** avec standards partages
- Projets necessitant **securite granulaire** (sandbox, permissions)

### Preferer Roo Code pour

- **Debutants** avec les AI coding tools
- Tester **differents modeles** facilement
- Interface **graphique** intuitive
- **Custom modes** specialises (Architect, Debug)
- Projets **open source** et personnalisation poussee
- **Budget limite** (modeles alternatifs moins chers)

### Recommandation pour la formation EPF 2026

1. **Debutants** : Commencer avec **Roo Code** (plus accessible, interface intuitive)
1. **Intermediaires** : Essayer les **deux** (comparer workflows, identifier preferences)
1. **Avances** : Preferer **Claude Code** (parallelisation, CLI, workflows professionnels)

Les deux outils peuvent coexister sans probleme dans VS Code.

## Tableau Synthese

| Critere | Claude Code | Roo Code |
| --- | --- | --- |
| Facilite installation | 3/5 | 5/5 |
| Interface utilisateur | 4/5 | 5/5 |
| Puissance (agents) | 5/5 | 3/5 |
| MCP Support | 5/5 | 3/5 |
| Flexibilite modeles | 4/5 | 5/5 |
| Documentation | 5/5 | 4/5 |
| Automatisation | 5/5 | 3/5 |
| Securite | 5/5 | 3/5 |
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

**Conclusion :** Les deux outils ont leur place. Claude Code excelle en puissance et professionnalisme, Roo Code en accessibilite et flexibilite. Choisissez selon vos besoins et votre niveau.
