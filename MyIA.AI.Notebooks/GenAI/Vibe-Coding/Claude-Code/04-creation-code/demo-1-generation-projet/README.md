# Demo 1 - Génération de Projet

## Objectif

Apprendre à générer un projet complet et fonctionnel depuis une spécification textuelle.

## Durée estimée

**50 minutes**

## Concepts

### Principes de génération

1. **Spécification claire** : Plus vous êtes précis, meilleur est le résultat
2. **Génération incrémentale** : Structure → Modèles → Logique → Interface
3. **Validation continue** : Testez à chaque étape
4. **Itération** : Affinez progressivement

### Ce que Claude Code peut générer

- Structures de projet complètes
- Fichiers de configuration (pyproject.toml, setup.py)
- Code fonctionnel avec gestion d'erreurs
- Tests associés
- Documentation

## Étapes

### Étape 1 : Définir la spécification (10 min)

Une bonne spécification inclut :

```markdown
## Projet : [Nom]

### Description
[2-3 phrases décrivant le but]

### Fonctionnalités
- Fonctionnalité 1
- Fonctionnalité 2
- ...

### Stack technique
- Langage : [Python 3.11+]
- Framework : [FastAPI / Click / etc.]
- Base de données : [SQLite / PostgreSQL / etc.]
- Tests : [pytest]

### Structure attendue
```
projet/
├── src/
├── tests/
└── ...
```

### Contraintes
- [Contrainte 1]
- [Contrainte 2]
```

### Étape 2 : Générer la structure (10 min)

#### Demande initiale

```
Crée la structure du projet suivant :

Projet : BookTracker - Suivi de lecture

Description : Application CLI pour suivre ses lectures, noter les livres et générer des statistiques.

Fonctionnalités :
- Ajouter un livre (titre, auteur, pages, genre)
- Marquer comme lu avec date et note (1-5)
- Lister les livres (filtres : lu/non lu, genre, note)
- Statistiques (livres lus par mois, pages totales, moyenne notes)
- Export CSV

Stack :
- Python 3.11+
- Click pour la CLI
- SQLite avec SQLAlchemy
- pytest

Génère d'abord uniquement la structure et les fichiers de configuration.
```

#### Résultat attendu

```
booktracker/
├── src/
│   └── booktracker/
│       ├── __init__.py
│       ├── cli.py
│       ├── models.py
│       ├── database.py
│       ├── services.py
│       └── utils.py
├── tests/
│   ├── __init__.py
│   ├── conftest.py
│   └── test_services.py
├── pyproject.toml
├── README.md
└── .gitignore
```

### Étape 3 : Générer les modèles (10 min)

```
Maintenant, implémente les modèles SQLAlchemy dans models.py :

Modèle Book :
- id : Integer, primary key
- title : String, required
- author : String, required
- pages : Integer, required
- genre : String, optional
- is_read : Boolean, default False
- read_date : Date, optional
- rating : Integer (1-5), optional
- notes : Text, optional
- created_at : DateTime, auto
- updated_at : DateTime, auto

Ajoute aussi la configuration de la base de données dans database.py.
```

### Étape 4 : Générer la logique métier (10 min)

```
Implémente les services dans services.py :

BookService avec :
- add_book(title, author, pages, genre=None) -> Book
- mark_as_read(book_id, rating, notes=None) -> Book
- list_books(is_read=None, genre=None, min_rating=None) -> List[Book]
- get_statistics() -> dict avec :
  - total_books
  - books_read
  - total_pages_read
  - average_rating
  - books_per_month (dict)
- export_to_csv(filepath) -> None

Gère les exceptions appropriées (BookNotFound, InvalidRating, etc.)
```

### Étape 5 : Générer l'interface CLI (10 min)

```
Implémente la CLI dans cli.py avec Click :

Commandes :
- booktracker add <title> <author> <pages> [--genre]
- booktracker read <book_id> <rating> [--notes]
- booktracker list [--read/--unread] [--genre] [--min-rating]
- booktracker stats
- booktracker export <filepath>

Ajoute :
- Aide pour chaque commande
- Couleurs pour l'affichage (rich)
- Confirmation pour les actions destructives
- Gestion d'erreurs user-friendly
```

## Exercice pratique

### Mission

Créez un projet complet de votre choix.

### Options suggérées

1. **Note Keeper** : Gestionnaire de notes en CLI
2. **Expense Tracker** : Suivi de dépenses
3. **Todo API** : API REST de gestion de tâches
4. **URL Shortener** : Raccourcisseur d'URL

### Template de spécification

```markdown
## Projet : [Votre nom de projet]

### Description
[Description en 2-3 phrases]

### Fonctionnalités
1. [Fonctionnalité principale 1]
2. [Fonctionnalité principale 2]
3. [Fonctionnalité principale 3]
4. [Fonctionnalité bonus optionnelle]

### Stack technique
- Langage : Python 3.11+
- [Framework CLI/Web]
- Base de données : SQLite
- Tests : pytest

### Modèles de données
[Décrivez vos entités principales]

### Interface
[CLI avec commandes X, Y, Z]
ou
[API REST avec endpoints X, Y, Z]

### Contraintes
- Tests avec couverture > 70%
- Documentation complète
- Gestion d'erreurs robuste
```

### Processus

1. Rédigez votre spécification
2. Demandez la structure
3. Générez composant par composant
4. Testez à chaque étape
5. Documentez

### Livrable

Projet fonctionnel avec :
- Code complet
- Tests
- README
- Historique Git propre

## Bonnes pratiques

### DO

- Soyez spécifique dans vos demandes
- Générez par petites étapes
- Testez le code généré
- Demandez des corrections si nécessaire
- Utilisez `/review` avant de continuer

### DON'T

- Ne demandez pas tout d'un coup
- Ne supposez pas que le code fonctionne sans tester
- N'ignorez pas les erreurs
- Ne sautez pas la phase de planification

## Points clés à retenir

1. **Spécification = Qualité** : Investissez du temps dans la spec

2. **Incrémental** : Structure → Modèles → Services → Interface

3. **Validation** : Testez chaque composant avant de continuer

4. **Itération** : Affinez et améliorez progressivement

---

**Prochaine étape** : [Demo 2 - Tests Automatisés](../demo-2-tests-automatises/)
