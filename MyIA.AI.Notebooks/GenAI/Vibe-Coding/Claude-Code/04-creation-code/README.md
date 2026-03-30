# Atelier 04 - Création de Code

## Objectifs pédagogiques

À la fin de cet atelier, vous serez capable de :

- Générer un projet complet depuis une spécification
- Créer des tests unitaires et d'intégration
- Documenter du code de manière professionnelle
- Structurer un projet selon les bonnes pratiques

## Prérequis

- Ateliers 01, 02 et 03 complétés
- Connaissance de base en Python
- Compréhension des tests unitaires

## Durée estimée

**3 heures**

## Concepts clés

### Génération de code avec Claude Code

Claude Code excelle dans la création de :
- Structures de projet complètes
- Fonctions et classes avec documentation
- Tests couvrant les cas normaux et limites
- Documentation technique (README, API docs)

### Workflow de création

```
Spécification → Plan → Génération → Tests → Documentation → Review
```

## Structure de l'atelier

| Demo | Titre | Durée | Description |
|------|-------|-------|-------------|
| 1 | [Génération de Projet](demo-1-generation-projet/) | 50 min | Créer un projet complet |
| 2 | [Tests Automatisés](demo-2-tests-automatises/) | 45 min | Générer des tests |
| 3 | [Documentation](demo-3-documentation/) | 40 min | Documenter le code |

## Démos

### Demo 1 - Génération de Projet

**Objectif** : Créer un projet fonctionnel depuis une spécification.

Vous apprendrez à :
- Décrire une spécification claire
- Générer une structure de projet
- Implémenter les fonctionnalités progressivement
- Valider le résultat

**Exemple** :
```
Crée une API REST pour gérer une bibliothèque de livres.
Fonctionnalités : CRUD livres, recherche, pagination.
Stack : Python, FastAPI, SQLite.
```

### Demo 2 - Tests Automatisés

**Objectif** : Générer des tests complets pour du code existant.

Vous apprendrez à :
- Créer des tests unitaires avec pytest
- Couvrir les cas normaux et les edge cases
- Mocker les dépendances externes
- Atteindre une couverture de code élevée

**Exemple** :
```
@src/services/ Génère des tests unitaires avec couverture > 80%
```

### Demo 3 - Documentation

**Objectif** : Documenter un projet de manière professionnelle.

Vous apprendrez à :
- Générer des docstrings automatiquement
- Créer un README complet
- Documenter une API (OpenAPI/Swagger)
- Créer des guides d'utilisation

**Exemple** :
```
Génère la documentation complète de ce projet :
README, API docs, guide de contribution.
```

## Types de projets à générer

### CLI (Command Line Interface)

```
Crée une CLI Python pour [fonctionnalité].
Utilise argparse ou click.
Inclus : aide, validation des arguments, couleurs.
```

### API REST

```
Crée une API REST avec FastAPI pour [domaine].
Inclus : validation Pydantic, documentation Swagger, pagination.
```

### Script utilitaire

```
Crée un script qui [action].
Gère les erreurs, le logging, et la configuration externe.
```

### Package/Bibliothèque

```
Crée un package Python réutilisable pour [fonctionnalité].
Structure avec setup.py/pyproject.toml, tests, documentation.
```

## Bonnes pratiques de génération

### Spécification claire

**Mauvais** :
```
Fais-moi une app de todo
```

**Bon** :
```
Crée une application de gestion de tâches avec :

Fonctionnalités :
- CRUD des tâches (titre, description, date limite, statut)
- Filtrage par statut (todo, in_progress, done)
- Recherche par titre
- Export JSON/CSV

Technique :
- Python 3.11+
- CLI avec Click
- Stockage SQLite
- Tests pytest avec couverture > 80%

Structure :
- src/ pour le code source
- tests/ pour les tests
- docs/ pour la documentation
```

### Génération progressive

1. **Structure d'abord** : Créez la structure vide
2. **Modèles ensuite** : Définissez les données
3. **Logique métier** : Implémentez les services
4. **Interface** : CLI ou API
5. **Tests** : À chaque étape
6. **Documentation** : En dernier

## Commandes essentielles

```bash
# Générer une structure de projet
claude
> Crée la structure d'un projet Python avec src/, tests/, docs/

# Générer une fonctionnalité
> Ajoute une fonction de recherche à @src/services/book.py

# Générer des tests
> Génère des tests pour @src/services/book.py

# Générer la documentation
> Ajoute des docstrings Google-style à @src/

# Review et finalisation
> /review
> /commit
```

## Checklist de validation

- [ ] Sait décrire une spécification claire
- [ ] Capable de générer un projet structuré
- [ ] Sait créer des tests complets
- [ ] Maîtrise la génération de documentation
- [ ] Comprend le workflow de création progressif

## Ressources

- [Python Project Structure](https://docs.python-guide.org/writing/structure/)
- [pytest Documentation](https://docs.pytest.org/)
- [Google Docstring Style](https://google.github.io/styleguide/pyguide.html#38-comments-and-docstrings)
- [FastAPI Tutorial](https://fastapi.tiangolo.com/tutorial/)

---

**Prochaine étape** : [Atelier 05 - Automatisation Avancée](../05-automatisation-avancee/)
