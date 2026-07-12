# Demo 1 - Agent Explore

## Objectif

Apprendre à utiliser l'agent Explore pour naviguer, comprendre et cartographier un codebase inconnu.

## Durée estimée

**40 minutes**

## Concepts

### Qu'est-ce que l'agent Explore ?

L'agent Explore est un sous-agent spécialisé de Claude Code qui :

- Parcourt automatiquement la structure d'un projet
- Utilise Glob pour trouver des fichiers par pattern
- Utilise Grep pour rechercher du contenu
- Lit les fichiers pertinents avec Read
- Synthétise les informations en une vue cohérente

### Quand utiliser Explore ?

| Situation | Utiliser Explore |
|-----------|------------------|
| Nouveau projet à comprendre | ✅ Oui |
| Recherche d'un fichier précis | ❌ Non (utiliser `@` ou Glob) |
| Comprendre une architecture | ✅ Oui |
| Trouver un bug spécifique | ❌ Non (recherche ciblée) |
| Documentation de projet | ✅ Oui |

## Étapes

### Étape 1 : Préparer un projet à explorer (5 min)

Vous pouvez utiliser :
- Le projet exemple de l'atelier 01
- Un de vos projets personnels
- Un projet open-source (voir suggestions ci-dessous)

**Suggestions de projets open-source** :
```bash
# Projet Python simple
git clone https://github.com/pallets/flask --depth 1
cd flask

# Projet Node.js
git clone https://github.com/expressjs/express --depth 1
cd express
```

### Étape 2 : Exploration basique (10 min)

Lancez Claude Code dans le dossier du projet :

```bash
claude
```

#### Exploration générale

```
Explore ce projet et donne-moi une vue d'ensemble :
- Quel est le but de ce projet ?
- Quelle est la structure des dossiers ?
- Quels sont les fichiers principaux ?
```

#### Observer le comportement

Notez que Claude :
1. Lit d'abord les fichiers de configuration (package.json, setup.py, etc.)
2. Liste la structure des dossiers
3. Identifie les points d'entrée
4. Lit les fichiers clés

### Étape 3 : Exploration ciblée (15 min)

#### Comprendre un module spécifique

```
Explore le dossier @src/models/ et explique :
- Quelles classes sont définies ?
- Comment elles sont liées entre elles ?
- Quels patterns sont utilisés ?
```

#### Tracer un flux

```
Trace le flux d'une requête HTTP dans ce projet, de l'entrée jusqu'à la réponse.
Identifie chaque fichier impliqué.
```

#### Trouver des patterns

```
Explore le code et identifie les design patterns utilisés.
Pour chaque pattern, donne un exemple concret du projet.
```

### Étape 4 : Créer une documentation (10 min)

#### Générer un rapport d'architecture

```
Génère un fichier ARCHITECTURE.md qui documente :
1. Vue d'ensemble du projet
2. Structure des dossiers (avec descriptions)
3. Composants principaux et leurs responsabilités
4. Diagramme des dépendances (format Mermaid)
5. Points d'entrée et flux principaux
```

## Exercice pratique

### Mission

Explorez un projet open-source et créez sa documentation d'architecture.

### Étapes

1. Choisissez un projet (ou utilisez Flask suggéré ci-dessus)
2. Demandez une exploration complète
3. Posez des questions de suivi sur les parties floues
4. Générez un fichier `ARCHITECTURE.md`

### Critères d'évaluation

- [ ] Vue d'ensemble claire
- [ ] Structure de dossiers documentée
- [ ] Composants principaux identifiés
- [ ] Diagramme Mermaid inclus
- [ ] Flux principaux décrits

## Exemples de prompts efficaces

### Pour démarrer

```
Explore ce projet comme si tu étais un nouveau développeur qui rejoint l'équipe.
Que dois-je savoir en priorité ?
```

### Pour approfondir

```
Explore comment la gestion des erreurs est implémentée dans ce projet.
Quels patterns sont utilisés ? Est-ce cohérent ?
```

### Pour documenter

```
Explore le projet et génère une documentation technique pour les nouveaux
développeurs. Inclus les conventions de code observées.
```

### Pour analyser

```
Explore ce projet et identifie :
- Les points forts de l'architecture
- Les améliorations possibles
- Les dettes techniques potentielles
```

## Points clés à retenir

1. **Explore est intelligent** : Il choisit automatiquement quels fichiers lire

2. **Guidez l'exploration** : Plus votre question est précise, meilleure est l'exploration

3. **Itérez** : Commencez large, puis zoomez sur les parties intéressantes

4. **Demandez des livrables** : Diagrammes, documentation, rapports

## Limitations

- L'exploration de très grands projets peut prendre du temps
- Les fichiers binaires ne sont pas analysés
- Le contexte a une limite : très grands projets = exploration partielle

## Ressources

- [Projet exemple Flask](https://github.com/pallets/flask)
- [Documentation agents](https://code.claude.com/docs/en/agents)

---

**Prochaine étape** : [Demo 2 - Agent Plan](../demo-2-agent-plan/)
