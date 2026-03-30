# CLAUDE.md - Exemple de Configuration Projet

Ce fichier est un exemple de configuration CLAUDE.md pour les exercices des notebooks CLI.

## Description du Projet

Ce projet est une application de demonstration pour les notebooks Claude CLI.
Il contient des fonctions de calcul statistique et de formatage de rapports.

## Structure

```
sample_project/
├── main.py              # Point d'entree principal
├── utils.py             # Fonctions utilitaires
└── tests/
    └── test_utils.py    # Tests unitaires
```

## Commandes Utiles

### Executer l'application

```bash
python main.py
```

### Lancer les tests

```bash
pytest tests/ -v
```

## Conventions de Code

- **Langage** : Python 3.9+
- **Style** : PEP 8
- **Docstrings** : Format Google-style
- **Type hints** : Obligatoires pour les fonctions publiques
- **Tests** : pytest avec couverture > 80%

## Architecture

### Module utils.py

Contient les fonctions de calcul :
- `calculate_statistics()` : Statistiques descriptives
- `format_report()` : Formatage du rapport
- `validate_data()` : Validation des donnees
- `normalize_data()` : Normalisation 0-1

### Module main.py

Point d'entree avec :
- `main()` : Execution principale
- `process_batch()` : Traitement par lots

## Notes pour Claude

Lors de l'analyse ou modification de ce code :

1. **Privilegier la lisibilite** sur la concision
2. **Conserver les docstrings** existantes
3. **Ajouter des tests** pour toute nouvelle fonction
4. **Utiliser les type hints** systematiquement
5. **Repondre en francais** pour les commentaires

## Dependances

- Python 3.9+
- pytest (pour les tests)
- Pas de dependances externes pour le code principal
