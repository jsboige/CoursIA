# Conseils pour des Prompts Efficaces

## Principes de base

### 1. Soyez spécifique

**Moins efficace :**
```
Explique Python
```

**Plus efficace :**
```
Explique les list comprehensions en Python avec 3 exemples de complexité croissante.
```

### 2. Donnez du contexte

**Moins efficace :**
```
Comment faire une API ?
```

**Plus efficace :**
```
Je développe une API REST en Python avec FastAPI pour gérer une bibliothèque de livres.
Comment structurer les endpoints pour les opérations CRUD ?
```

### 3. Précisez le format attendu

**Moins efficace :**
```
Donne-moi des commandes Git
```

**Plus efficace :**
```
Liste les 10 commandes Git les plus utiles sous forme de tableau avec :
- La commande
- Sa description
- Un exemple d'utilisation
```

### 4. Découpez les tâches complexes

**Moins efficace :**
```
Crée une application complète de gestion de tâches
```

**Plus efficace :**
```
Je veux créer une application de gestion de tâches. Commençons par :
1. Définir la structure des données (quels champs pour une tâche ?)
2. Je te demanderai ensuite de créer les fonctions CRUD
```

## Techniques avancées

### Chain of Thought (Réflexion étape par étape)

```
Résous ce problème étape par étape :
Comment optimiser une requête SQL qui prend 30 secondes sur une table de 10 millions de lignes ?
```

### Few-Shot (Exemples)

```
Convertis ces phrases en slug URL :
- "Mon Premier Article" → "mon-premier-article"
- "L'été 2024 !" → "lete-2024"

Maintenant convertis : "Les 10 meilleures pratiques DevOps"
```

### Role-Playing

```
Agis comme un expert en sécurité informatique et analyse ce code PHP
pour identifier les vulnérabilités potentielles.
```

## Structures de prompts efficaces

### Pour de l'aide au code

```
Contexte : [description du projet]
Problème : [ce qui ne fonctionne pas]
Code actuel : [snippet de code]
Comportement attendu : [ce que ça devrait faire]
Comportement actuel : [ce qui se passe]
```

### Pour de la génération

```
Génère [quoi] pour [contexte/usage]
Contraintes :
- [contrainte 1]
- [contrainte 2]
Format : [format souhaité]
```

### Pour de l'explication

```
Explique [concept] comme si j'étais [niveau]
Inclus :
- Une définition simple
- Un exemple concret
- Les cas d'usage typiques
```

## Exemples par type de tâche

### Debug

```
Ce code Python lève une erreur. Aide-moi à comprendre et corriger :

```python
def process_data(items):
    return [item.upper() for item in items]

result = process_data([1, 2, 3])
```

Erreur : AttributeError: 'int' object has no attribute 'upper'
```

### Refactoring

```
Ce code fonctionne mais n'est pas maintenable. Propose une version refactorisée
en appliquant les principes SOLID :

[code à refactorer]

Explique chaque changement.
```

### Documentation

```
Génère une docstring complète (format Google) pour cette fonction Python.
Inclus les types, la description des paramètres, les exceptions possibles
et un exemple d'utilisation.

[fonction à documenter]
```

### Architecture

```
Je dois concevoir [système/fonctionnalité].
Contraintes :
- [contrainte technique]
- [contrainte métier]

Propose une architecture avec :
1. Les composants principaux
2. Les interactions entre eux
3. Les technologies recommandées
4. Les points d'attention
```

## Anti-patterns à éviter

### Trop vague

❌ "Aide-moi avec mon code"
✅ "Mon code Python lève TypeError à la ligne 42. Voici le code et l'erreur..."

### Trop long en une fois

❌ Un prompt de 500 lignes avec tout le contexte
✅ Découper en plusieurs échanges, commencer par le contexte minimal

### Pas de contexte

❌ "Comment faire un login ?"
✅ "Comment implémenter l'authentification JWT dans une API FastAPI ?"

### Attentes floues

❌ "Améliore ce code"
✅ "Améliore ce code en termes de performance, en particulier la boucle ligne 15"

## Checklist du bon prompt

- [ ] J'ai précisé le contexte (langage, framework, projet)
- [ ] J'ai décrit clairement ce que je veux obtenir
- [ ] J'ai indiqué le format de réponse souhaité
- [ ] J'ai inclus les contraintes importantes
- [ ] Mon prompt est découpé si la tâche est complexe
- [ ] J'ai évité les ambiguïtés

## Ressources

- [Prompt Engineering Guide](https://www.promptingguide.ai/)
- [Anthropic Prompt Library](https://docs.anthropic.com/en/prompt-library)
- [Best Practices Anthropic](https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering/overview)
