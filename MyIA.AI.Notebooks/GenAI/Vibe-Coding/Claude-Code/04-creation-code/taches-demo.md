# Tâches de démonstration - Atelier 04

Ce document liste des tâches concrètes pour maîtriser la génération de code avec Claude Code.

## Tâche 1 : Générer une CLI simple

### Contexte
Vous devez créer un outil en ligne de commande pour convertir des fichiers.

### Instructions

1. Décrivez le besoin à Claude :
   ```
   Crée une CLI Python pour convertir des fichiers Markdown en HTML.

   Fonctionnalités :
   - Convertir un fichier unique
   - Convertir tous les fichiers d'un dossier
   - Option pour inclure un CSS personnalisé
   - Prévisualisation dans le terminal

   Technique :
   - Python 3.11+
   - Click pour la CLI
   - markdown2 pour la conversion
   - rich pour l'affichage

   Structure attendue :
   md2html/
   ├── src/
   │   ├── __init__.py
   │   ├── cli.py
   │   ├── converter.py
   │   └── preview.py
   ├── tests/
   ├── pyproject.toml
   └── README.md
   ```

2. Demandez la génération étape par étape :
   - Structure et configuration
   - Module de conversion
   - Interface CLI
   - Tests

### Livrable
CLI fonctionnelle avec tests.

---

## Tâche 2 : Générer une API REST

### Contexte
Vous devez créer une API pour gérer une collection de recettes.

### Instructions

1. Spécification complète :
   ```
   Crée une API REST pour une application de recettes.

   Modèles :
   - Recipe : id, title, description, ingredients (list), steps (list), prep_time, cook_time, servings, tags
   - Ingredient : id, name, quantity, unit

   Endpoints :
   - GET /recipes : Liste avec pagination et filtres (tag, search)
   - GET /recipes/{id} : Détail d'une recette
   - POST /recipes : Créer une recette
   - PUT /recipes/{id} : Modifier une recette
   - DELETE /recipes/{id} : Supprimer une recette
   - GET /recipes/{id}/scale?servings=X : Recette avec ingrédients recalculés

   Technique :
   - FastAPI
   - Pydantic pour la validation
   - SQLite avec SQLAlchemy
   - Alembic pour les migrations

   Qualité :
   - Documentation Swagger automatique
   - Gestion d'erreurs standardisée
   - Logs structurés
   - Tests > 80% couverture
   ```

2. Générez progressivement :
   - Modèles Pydantic et SQLAlchemy
   - Routes CRUD
   - Fonctionnalités avancées (scale, search)
   - Tests

### Livrable
API complète avec documentation Swagger.

---

## Tâche 3 : Générer un package réutilisable

### Contexte
Vous voulez créer une bibliothèque Python réutilisable.

### Instructions

1. Spécification :
   ```
   Crée un package Python pour la validation de données.

   Fonctionnalités :
   - Validation d'email (format + domaine)
   - Validation de numéro de téléphone (formats internationaux)
   - Validation de mot de passe (critères configurables)
   - Validation d'URL
   - Messages d'erreur en français et anglais

   API :
   ```python
   from pyvalidator import EmailValidator, PasswordValidator

   validator = EmailValidator()
   result = validator.validate("test@example.com")
   # result.is_valid, result.errors, result.warnings
   ```

   Qualité :
   - Type hints complets
   - Docstrings Google-style
   - Tests > 90% couverture
   - Compatible Python 3.9+
   - Publication PyPI ready
   ```

2. Générez avec structure package :
   ```
   pyvalidator/
   ├── src/pyvalidator/
   │   ├── __init__.py
   │   ├── validators/
   │   │   ├── email.py
   │   │   ├── phone.py
   │   │   ├── password.py
   │   │   └── url.py
   │   ├── result.py
   │   └── i18n/
   │       ├── fr.py
   │       └── en.py
   ├── tests/
   ├── docs/
   ├── pyproject.toml
   └── README.md
   ```

### Livrable
Package installable via pip.

---

## Tâche 4 : Tests pour code existant

### Contexte
Vous avez du code sans tests et devez atteindre 80% de couverture.

### Instructions

1. Utilisez le module `projet-a-tester` fourni dans les ressources

2. Demandez une analyse :
   ```
   @projet-a-tester/ Analyse ce code et identifie :
   - Les fonctions à tester en priorité
   - Les cas limites à couvrir
   - Les dépendances à mocker
   ```

3. Générez les tests :
   ```
   Génère des tests complets pour @projet-a-tester/services.py
   Objectif : 80% de couverture minimum
   Inclus : tests unitaires, tests de cas limites, mocks
   ```

4. Vérifiez la couverture :
   ```bash
   pytest --cov=projet-a-tester --cov-report=html
   ```

### Livrable
Suite de tests avec rapport de couverture.

---

## Tâche 5 : Tests d'intégration

### Contexte
Vous avez une API et devez créer des tests d'intégration.

### Instructions

1. Demandez des tests d'intégration :
   ```
   @src/api/ Génère des tests d'intégration pour cette API.

   Couvrir :
   - Workflow complet CRUD
   - Authentification (si présente)
   - Cas d'erreur (404, 400, 500)
   - Pagination et filtres
   - Validation des données

   Technique :
   - pytest avec fixtures
   - TestClient de FastAPI
   - Base de données de test isolée
   - Factories pour les données de test
   ```

2. Structure attendue :
   ```
   tests/
   ├── conftest.py      # Fixtures globales
   ├── factories.py     # Factories de données
   ├── integration/
   │   ├── test_recipes_crud.py
   │   ├── test_recipes_search.py
   │   └── test_error_handling.py
   └── unit/
       └── ...
   ```

### Livrable
Tests d'intégration complets.

---

## Tâche 6 : Documentation README

### Contexte
Votre projet manque de documentation d'entrée.

### Instructions

1. Demandez un README complet :
   ```
   Génère un README.md professionnel pour ce projet incluant :

   1. Badges (build, coverage, version, license)
   2. Description courte et longue
   3. Fonctionnalités principales (liste)
   4. Installation (pip, from source)
   5. Quick Start avec exemples
   6. Configuration (variables d'env, fichier config)
   7. Utilisation détaillée
   8. API Reference (si applicable)
   9. Contribution guidelines
   10. License
   11. Changelog link

   Style : Professionnel, concis, avec émojis appropriés
   ```

### Livrable
README.md complet.

---

## Tâche 7 : Documentation API

### Contexte
Votre API a besoin d'une documentation utilisateur.

### Instructions

1. Demandez une documentation API :
   ```
   @src/api/ Génère une documentation API complète incluant :

   1. Vue d'ensemble
   2. Authentification (si applicable)
   3. Erreurs standards
   4. Endpoints avec exemples curl
   5. Schémas des modèles
   6. Exemples de réponses
   7. Rate limiting
   8. Versioning

   Format : Markdown structuré, prêt pour MkDocs
   ```

2. Structure :
   ```
   docs/
   ├── index.md
   ├── getting-started.md
   ├── authentication.md
   ├── api/
   │   ├── recipes.md
   │   └── users.md
   ├── errors.md
   └── examples.md
   ```

### Livrable
Documentation API complète.

---

## Tâche 8 : Docstrings automatiques

### Contexte
Votre code manque de docstrings.

### Instructions

1. Demandez l'ajout de docstrings :
   ```
   @src/ Ajoute des docstrings Google-style complètes à tout le code.

   Inclure pour chaque fonction/méthode :
   - Description courte
   - Description longue si nécessaire
   - Args avec types et descriptions
   - Returns avec type et description
   - Raises avec les exceptions possibles
   - Examples si pertinent

   Ne pas modifier la logique, uniquement ajouter documentation.
   ```

2. Vérifiez avec pydocstyle :
   ```bash
   pip install pydocstyle
   pydocstyle src/
   ```

### Livrable
Code entièrement documenté.

---

## Récapitulatif des livrables

| Tâche | Livrable |
|-------|----------|
| 1 | CLI md2html fonctionnelle |
| 2 | API REST recettes |
| 3 | Package pyvalidator |
| 4 | Tests avec 80% couverture |
| 5 | Tests d'intégration |
| 6 | README.md professionnel |
| 7 | Documentation API |
| 8 | Code avec docstrings |

---

## Pour aller plus loin

- Générez un projet avec CI/CD (GitHub Actions)
- Créez un projet multi-package (monorepo)
- Ajoutez une couche de déploiement (Docker, Kubernetes)
