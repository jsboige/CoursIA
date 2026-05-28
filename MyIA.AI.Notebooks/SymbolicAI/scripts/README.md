# Scripts Utilitaires - SymbolicAI

Ce répertoire contient les scripts Python utilitaires de la série SymbolicAI : installation de dépendances externes (solveurs) et utilitaires de génération/maintenance de documentation des notebooks.

## Scripts Disponibles

### install_clingo.py

Script d'installation automatique de Clingo (solveur ASP - Answer Set Programming, suite Potassco) pour Windows et Linux. Utilisé par les notebooks Tweety qui font appel à ASP via `ClingoSolver`.

**Usage:**
```bash
python install_clingo.py [--target-dir ext_tools/clingo] [--force]
```

**Fonctionnalités:**

- Téléchargement automatique de Clingo 5.7.1 depuis GitHub
- Extraction et installation dans `ext_tools/clingo/`
- Support Windows (ZIP) et Linux (tar.gz)
- Vérification de l'installation existante (skip si déjà présent, sauf `--force`)

**Note technique:** Dans Clingo 5.0+, `gringo` a été fusionné dans `clingo`. `GringoGrounder` de TweetyProject ne fonctionne donc pas directement, mais `ClingoSolver` reste pleinement opérationnel.

### extract_notebook_content.py

Utilitaire d'analyse de notebooks pour générer/maintenir la documentation. Parcourt tous les notebooks `.ipynb` du répertoire SymbolicAI et extrait pour chacun : le kernel, le nombre de cellules par type, et un aperçu des premières lignes de chaque cellule.

**Usage:**
```bash
python extract_notebook_content.py
```

**Fonctionnalités:**

- Scan récursif des notebooks SymbolicAI
- Extraction du kernel et statistiques de cellules
- Génération de previews (3 lignes / 200 caractères max par cellule)
- Sortie utilisable pour rédaction/mise à jour de README

## Maintenance

Ces scripts sont des outils d'appui à la série SymbolicAI :

- `install_clingo.py` : à exécuter une fois par environnement pour activer les notebooks ASP de Tweety
- `extract_notebook_content.py` : utilitaire de génération de documentation, utile lors de la mise à jour des README de séries
