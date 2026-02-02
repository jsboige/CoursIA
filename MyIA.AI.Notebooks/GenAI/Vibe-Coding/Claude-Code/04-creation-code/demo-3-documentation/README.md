# Demo 3 - Documentation

## Objectif

Apprendre à générer une documentation professionnelle et complète pour vos projets.

## Durée estimée

**40 minutes**

## Concepts

### Types de documentation

| Type | Audience | Contenu |
|------|----------|---------|
| README | Tous | Vue d'ensemble, installation, quickstart |
| API Docs | Développeurs | Endpoints, paramètres, exemples |
| Docstrings | Développeurs | Documentation inline du code |
| Guides | Utilisateurs | Tutoriels, how-to |
| Architecture | Équipe | Décisions techniques, diagrammes |

### Formats courants

- **Markdown** : README, guides
- **reStructuredText** : Sphinx
- **OpenAPI/Swagger** : API REST
- **Docstrings** : Google, NumPy, Sphinx style

## Étapes

### Étape 1 : Générer des docstrings (10 min)

#### Format Google Style

```
@src/ Ajoute des docstrings Google-style à toutes les fonctions et classes.

Format attendu :
```python
def fonction(param1: str, param2: int = 0) -> dict:
    """Description courte sur une ligne.

    Description plus longue si nécessaire, expliquant
    le comportement et le contexte.

    Args:
        param1: Description du premier paramètre.
        param2: Description avec valeur par défaut. Defaults to 0.

    Returns:
        Description de ce qui est retourné.

    Raises:
        ValueError: Si param1 est vide.
        TypeError: Si param2 n'est pas un entier.

    Examples:
        >>> fonction("test", 5)
        {'result': 'test', 'count': 5}
    """
```

Ne modifie pas la logique, uniquement ajouter documentation.
```

### Étape 2 : Générer le README (15 min)

#### Template complet

```
Génère un README.md professionnel avec cette structure :

# [Nom du Projet]

## Badges
- Build status
- Coverage
- Version
- License

## Description
- Courte (1 phrase)
- Longue (1 paragraphe)
- Captures d'écran si applicable

## Features
- Liste des fonctionnalités principales
- Avec émojis appropriés

## Installation

### Prérequis
- Liste des dépendances système

### Via pip
```bash
pip install mon-projet
```

### Depuis les sources
```bash
git clone ...
pip install -e .
```

## Quick Start
Exemple minimal fonctionnel en 5 lignes max.

## Usage
Exemples plus détaillés pour chaque fonctionnalité.

## Configuration
Variables d'environnement et fichiers de config.

## API Reference
Lien vers documentation détaillée ou résumé.

## Contributing
Guidelines pour contribuer.

## License
Type de licence.

## Changelog
Lien vers CHANGELOG.md

Style : Professionnel, concis, avec émojis appropriés
```

#### Exemple de résultat

```markdown
# BookTracker

![Build Status](https://img.shields.io/github/workflow/status/user/booktracker/ci)
![Coverage](https://img.shields.io/codecov/c/github/user/booktracker)
![PyPI](https://img.shields.io/pypi/v/booktracker)
![License](https://img.shields.io/github/license/user/booktracker)

Track your reading habits and discover insights about your book collection.

BookTracker is a command-line application that helps you manage your personal library,
track reading progress, and generate statistics about your reading habits.

## Features

- Add books with metadata (title, author, pages, genre)
- Mark books as read with ratings and notes
- Filter and search your collection
- Generate reading statistics
- Export to CSV for backup

## Installation

```bash
pip install booktracker
```

## Quick Start

```bash
# Add a book
booktracker add "1984" "George Orwell" 328 --genre "Dystopia"

# Mark as read
booktracker read 1 --rating 5 --notes "Masterpiece!"

# View statistics
booktracker stats
```

[... suite du README ...]
```

### Étape 3 : Documenter une API (10 min)

#### Documentation OpenAPI

```
@src/api/ Génère la documentation API au format OpenAPI 3.0.

Inclure pour chaque endpoint :
- Summary et description
- Paramètres (path, query, body)
- Schémas de request/response
- Codes de réponse possibles
- Exemples de requêtes curl
- Exemples de réponses

Format : YAML ou JSON selon préférence du projet
```

#### Documentation Markdown

```
Génère une documentation API en Markdown incluant :

## Endpoints

### GET /books
Liste tous les livres.

**Paramètres Query:**
| Param | Type | Default | Description |
|-------|------|---------|-------------|
| page | int | 1 | Numéro de page |
| limit | int | 20 | Résultats par page |
| genre | string | null | Filtrer par genre |

**Réponse:**
```json
{
  "data": [...],
  "pagination": {...}
}
```

**Exemple:**
```bash
curl -X GET "http://api.example.com/books?genre=fiction&limit=10"
```

[Pour chaque endpoint du projet]
```

### Étape 4 : Créer un guide utilisateur (5 min)

```
Crée un guide utilisateur pour ce projet couvrant :

1. Introduction
   - Qu'est-ce que c'est
   - À qui ça s'adresse
   - Prérequis

2. Premiers pas
   - Installation
   - Configuration initiale
   - Premier exemple

3. Fonctionnalités
   - Tutoriel pour chaque fonctionnalité
   - Avec captures d'écran/exemples

4. Configuration avancée
   - Toutes les options
   - Personnalisation

5. FAQ
   - Questions fréquentes
   - Problèmes courants

6. Ressources
   - Liens utiles
   - Support
```

## Exercice pratique

### Mission

Documentez complètement un projet existant.

### Checklist

- [ ] Docstrings sur toutes les fonctions publiques
- [ ] README complet avec badges
- [ ] Documentation API (si applicable)
- [ ] CONTRIBUTING.md
- [ ] CHANGELOG.md
- [ ] Guide utilisateur

### Processus

1. **Audit documentation**
   ```
   @src/ Liste les fonctions sans docstring.
   ```

2. **Ajout docstrings**
   ```
   Ajoute des docstrings Google-style aux fonctions identifiées.
   ```

3. **Génération README**
   ```
   Génère un README professionnel basé sur le code.
   ```

4. **Documentation supplémentaire**
   ```
   Génère CONTRIBUTING.md et CHANGELOG.md
   ```

### Livrable

Documentation complète du projet.

## Outils recommandés

### Génération de documentation

| Outil | Usage |
|-------|-------|
| Sphinx | Documentation Python complète |
| MkDocs | Documentation Markdown simple |
| pdoc | Auto-doc depuis docstrings |
| Swagger UI | Documentation API interactive |

### Vérification

```bash
# Vérifier les docstrings
pip install pydocstyle
pydocstyle src/

# Vérifier le README
pip install readme-renderer
python -m readme_renderer README.md

# Linter Markdown
npm install -g markdownlint-cli
markdownlint README.md
```

## Points clés à retenir

1. **Documentation = Premier contact** : Soignez-la

2. **Exemples concrets** : Montrez, ne décrivez pas seulement

3. **Maintenez à jour** : Documentation obsolète est pire que pas de doc

4. **Ciblez l'audience** : Adaptez le niveau de détail

---

**Prochaine étape** : [Atelier 05 - Automatisation Avancée](../../05-automatisation-avancee/)
