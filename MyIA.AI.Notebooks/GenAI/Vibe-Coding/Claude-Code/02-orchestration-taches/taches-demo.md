# Tâches de démonstration - Atelier 02

Ce document liste des tâches concrètes pour découvrir les capacités d'orchestration de Claude Code.

## Tâche 1 : Explorer un projet open-source

### Contexte
Vous rejoignez une équipe qui travaille sur un projet existant. Vous devez comprendre rapidement son architecture.

### Instructions

1. Clonez un projet open-source simple (exemple : une API Flask/FastAPI)
   ```bash
   git clone https://github.com/tiangolo/fastapi
   cd fastapi
   ```

2. Lancez Claude Code et demandez une exploration :
   ```
   Explore ce projet et explique-moi :
   - La structure des dossiers
   - Les composants principaux
   - Comment les fichiers interagissent
   - Les dépendances externes
   ```

3. Demandez des précisions :
   ```
   Comment fonctionne le système de routing ?
   ```

### Résultat attendu
- Vue d'ensemble claire de l'architecture
- Identification des fichiers clés
- Compréhension des patterns utilisés

---

## Tâche 2 : Cartographier les dépendances

### Contexte
Vous devez comprendre les dépendances d'un module avant de le modifier.

### Instructions

1. Utilisez le projet de l'atelier 01 ou un autre projet
2. Demandez à Claude d'analyser les dépendances :
   ```
   Analyse les imports dans @src/ et crée un graphe des dépendances
   entre les modules. Identifie les dépendances circulaires s'il y en a.
   ```

3. Demandez une visualisation :
   ```
   Crée un diagramme Mermaid montrant les relations entre modules
   ```

### Livrable
Fichier `architecture.md` avec :
- Liste des modules
- Graphe des dépendances (Mermaid)
- Analyse des couplages

---

## Tâche 3 : Planifier une nouvelle fonctionnalité

### Contexte
On vous demande d'ajouter une fonctionnalité de cache à une application.

### Instructions

1. Décrivez le besoin à Claude :
   ```
   Je veux ajouter un système de cache pour les requêtes API.
   Planifie cette implémentation en détaillant :
   - Les options de cache possibles (Redis, mémoire, fichier)
   - Les fichiers à créer ou modifier
   - L'ordre des étapes
   - Les tests nécessaires
   ```

2. Demandez des détails sur chaque option :
   ```
   Compare Redis vs cache en mémoire pour mon cas d'usage :
   - Application Python/FastAPI
   - ~1000 requêtes/minute
   - Données qui changent toutes les 5 minutes
   ```

3. Validez le plan :
   ```
   Génère un plan détaillé avec les fichiers à créer et leur contenu prévu
   ```

### Livrable
Plan d'implémentation structuré en Markdown.

---

## Tâche 4 : Recherche de documentation

### Contexte
Vous devez choisir une bibliothèque pour une fonctionnalité.

### Instructions

1. Demandez une recherche comparative :
   ```
   Recherche et compare les bibliothèques Python pour la validation de données :
   - Pydantic
   - Marshmallow
   - Cerberus

   Critères : performance, facilité d'utilisation, intégration FastAPI
   ```

2. Demandez les sources :
   ```
   Donne-moi les liens vers la documentation officielle de chaque bibliothèque
   ```

3. Récupérez un exemple spécifique :
   ```
   Récupère un exemple de validation imbriquée avec Pydantic depuis la doc officielle
   ```

### Livrable
Tableau comparatif avec recommandation argumentée.

---

## Tâche 5 : Veille technologique

### Contexte
Vous voulez vous tenir à jour sur les évolutions d'une technologie.

### Instructions

1. Demandez une veille :
   ```
   Recherche les nouveautés de Python 3.12 et 3.13. Quelles sont les
   fonctionnalités les plus importantes pour le développement web ?
   ```

2. Approfondissez un point :
   ```
   Explique le nouveau système de typing de Python 3.12 avec des exemples
   ```

3. Évaluez l'impact :
   ```
   Comment ces nouveautés affectent-elles un projet FastAPI existant ?
   Quelles migrations sont recommandées ?
   ```

### Livrable
Document `veille-python-2026.md` avec résumé des nouveautés.

---

## Tâche 6 : Audit de sécurité préliminaire

### Contexte
Vous devez évaluer rapidement la sécurité d'un projet.

### Instructions

1. Demandez un audit de sécurité :
   ```
   Explore ce projet et identifie les problèmes de sécurité potentiels :
   - Injection SQL
   - XSS
   - Gestion des secrets
   - Dépendances vulnérables
   ```

2. Recherchez les bonnes pratiques :
   ```
   Recherche les recommandations OWASP 2025 pour les API REST Python
   ```

3. Demandez un plan de correction :
   ```
   Planifie les corrections par ordre de priorité avec estimation d'effort
   ```

### Livrable
Rapport d'audit avec plan de remédiation.

---

## Tâche 7 : Planifier une migration

### Contexte
Vous devez migrer une application vers une nouvelle version de framework.

### Instructions

1. Décrivez la situation :
   ```
   J'ai une application Flask 2.x que je veux migrer vers Flask 3.x.
   Explore le code et identifie :
   - Les breaking changes qui nous affectent
   - Les fonctionnalités dépréciées utilisées
   - L'ordre de migration recommandé
   ```

2. Recherchez les changements :
   ```
   Recherche le changelog de Flask 3.0 et les guides de migration
   ```

3. Générez un plan :
   ```
   Crée un plan de migration détaillé avec des étapes de test intermédiaires
   ```

### Livrable
Plan de migration avec checklist de validation.

---

## Tâche 8 : Synthèse multi-sources

### Contexte
Vous devez rédiger une recommandation technique basée sur plusieurs sources.

### Instructions

1. Définissez le sujet :
   ```
   Je dois recommander une solution de déploiement pour une application Python.
   Options : AWS Lambda, Google Cloud Run, Heroku, Railway
   ```

2. Demandez une recherche structurée :
   ```
   Pour chaque option, recherche :
   - Tarification (avec exemples concrets)
   - Facilité de déploiement
   - Limitations
   - Retours d'expérience
   ```

3. Demandez une synthèse :
   ```
   Synthétise ces informations en une recommandation pour :
   - Application FastAPI
   - ~10k requêtes/jour
   - Budget limité
   - Équipe de 2 développeurs
   ```

### Livrable
Document de recommandation avec tableau comparatif et justification.

---

## Récapitulatif des livrables

| Tâche | Livrable |
|-------|----------|
| 1 | Documentation d'exploration |
| 2 | `architecture.md` avec diagrammes |
| 3 | Plan d'implémentation cache |
| 4 | Comparatif bibliothèques |
| 5 | `veille-python-2026.md` |
| 6 | Rapport d'audit sécurité |
| 7 | Plan de migration Flask |
| 8 | Recommandation déploiement |

---

## Pour aller plus loin

- Combinez exploration et planification pour des tâches complexes
- Utilisez la recherche web pour valider vos choix techniques
- Créez des templates de plan pour vos tâches récurrentes
