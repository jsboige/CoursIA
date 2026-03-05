# papermill-coursia - Archivé

**Date d'archivage:** 2026-03-05

## Raison de l'archivage

Ce package a été archivé car sa fonctionnalité est désormais couverte par `scripts/notebook_tools/notebook_tools.py` qui fournit une CLI unifiée pour la gestion des notebooks :

- Validation de notebooks
- Extraction de squelettes
- Exécution Papermill
- Analyse de structure

## Remplacement

Utiliser `scripts/notebook_tools/notebook_tools.py` à la place.

```bash
python scripts/notebook_tools/notebook_tools.py --help
```

## Contenu original

- `cli/papermill_coursia.py` - CLI Papermill
- `core/executor.py` - Logique d'exécution
- `requirements.txt` - Dépendances

Archivé lors de la consolidation de `notebook-infrastructure/` dans `scripts/`.
