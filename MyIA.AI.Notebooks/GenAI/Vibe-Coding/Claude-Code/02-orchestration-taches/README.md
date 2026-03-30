# Atelier 02 - Orchestration de Tâches

## Objectifs pédagogiques

À la fin de cet atelier, vous serez capable de :

- Utiliser l'agent Explore pour naviguer et comprendre un codebase
- Utiliser l'agent Plan pour concevoir des solutions structurées
- Effectuer des recherches web avec WebSearch et WebFetch
- Synthétiser des informations de sources multiples
- Comprendre comment Claude Code délègue aux sous-agents

## Prérequis

- Atelier 01 complété
- Claude Code fonctionnel
- Connexion internet (pour la recherche web)

## Durée estimée

**2 à 3 heures**

## Concepts clés

### Agents intégrés de Claude Code

Claude Code dispose d'agents spécialisés qui peuvent être invoqués automatiquement ou explicitement :

| Agent | Fonction | Invocation |
|-------|----------|------------|
| **Explore** | Explorer et comprendre un codebase | Automatique ou "explore le projet" |
| **Plan** | Planifier des implémentations | Automatique ou "planifie comment..." |
| **General-purpose** | Tâches variées | Délégation automatique |

### Outils de recherche

| Outil | Description | Usage |
|-------|-------------|-------|
| **Glob** | Recherche de fichiers par pattern | `*.py`, `src/**/*.ts` |
| **Grep** | Recherche de contenu | Texte, regex |
| **WebSearch** | Recherche web | Documentation, actualités |
| **WebFetch** | Récupérer une page web | Contenu spécifique |

## Structure de l'atelier

| Demo | Titre | Durée | Description |
|------|-------|-------|-------------|
| 1 | [Agent Explore](demo-1-agent-explore/) | 40 min | Explorer et cartographier un codebase |
| 2 | [Agent Plan](demo-2-agent-plan/) | 40 min | Planifier une implémentation |
| 3 | [Recherche Web](demo-3-recherche-web/) | 30 min | Rechercher et synthétiser des informations |

## Démos

### Demo 1 - Agent Explore

**Objectif** : Apprendre à explorer efficacement un codebase inconnu.

L'agent Explore utilise les outils Glob, Grep et Read pour :
- Cartographier la structure d'un projet
- Identifier les composants principaux
- Comprendre les dépendances entre modules
- Trouver des patterns et conventions

**Commande exemple** :
```
Explore ce projet et explique-moi son architecture
```

### Demo 2 - Agent Plan

**Objectif** : Utiliser le mode Plan pour concevoir avant d'implémenter.

Le mode Plan permet de :
- Analyser les besoins d'une tâche
- Proposer une approche structurée
- Identifier les fichiers à modifier
- Estimer la complexité

**Commande exemple** :
```
Planifie comment ajouter une fonctionnalité de cache à ce projet
```

### Demo 3 - Recherche Web

**Objectif** : Intégrer des informations externes dans votre workflow.

Les outils WebSearch et WebFetch permettent de :
- Rechercher de la documentation
- Trouver des solutions à des problèmes
- Se tenir à jour sur les technologies
- Comparer des approches

**Commande exemple** :
```
Recherche les meilleures pratiques pour l'authentification JWT en 2026
```

## Commandes essentielles

```bash
# Lancer Claude Code en mode Plan
claude --permission-mode plan

# Demander une exploration
> Explore ce projet et crée une documentation d'architecture

# Demander une planification
> Planifie l'ajout d'une API REST à ce projet

# Recherche web
> Recherche les différences entre FastAPI et Flask en 2026

# Récupérer une page spécifique
> Récupère et résume la documentation de pytest sur les fixtures
```

## Points clés

### Agent Explore vs Grep/Glob manuels

| Approche | Avantages | Quand utiliser |
|----------|-----------|----------------|
| Agent Explore | Automatique, exhaustif, intelligent | Découverte, compréhension globale |
| Grep/Glob direct | Rapide, ciblé | Recherche précise connue |

### Mode Plan vs Implémentation directe

| Mode | Avantages | Quand utiliser |
|------|-----------|----------------|
| Plan | Réflexion, validation, vision globale | Tâches complexes, architecture |
| Direct | Rapide, itératif | Tâches simples, corrections |

## Bonnes pratiques

1. **Explorez avant de coder** : Comprenez le contexte existant
2. **Planifiez les tâches complexes** : Évitez les impasses
3. **Vérifiez les sources web** : Les informations peuvent être datées
4. **Combinez les approches** : Explore → Plan → Implémente

## Ressources

- [Documentation agents Claude Code](https://code.claude.com/docs/en/agents)
- [Guide Explore](../../docs/claude-code/CONCEPTS-AVANCES.md#agents)
- [Best Practices](https://www.anthropic.com/engineering/claude-code-best-practices)

## Checklist de validation

- [ ] Sait invoquer l'agent Explore
- [ ] Comprend la différence entre exploration et recherche ciblée
- [ ] Sait utiliser le mode Plan
- [ ] Maîtrise WebSearch et WebFetch
- [ ] Capable de synthétiser des informations multiples

---

**Prochaine étape** : [Atelier 03 - Assistant Développeur](../03-assistant-developpeur/)
