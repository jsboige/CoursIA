# Scripts Utilitaires - Série Tweety

Ce répertoire contient les scripts Python utilitaires pour la gestion de la série de notebooks Tweety.

## Scripts Disponibles

### verify_all_tweety.py
Script de vérification complète de tous les notebooks Tweety. Exécute chaque notebook avec Papermill et analyse les sorties pour identifier les problèmes.

**Usage:**
```bash
python verify_all_tweety.py
```

**Fonctionnalités:**
- Exécution de tous les notebooks (Tweety-1 à Tweety-7)
- Analyse des outputs pour détecter erreurs, warnings, outputs longs
- Génération d'un résumé de vérification
- Rapport de succès/échec par notebook

### reorganize_tweety.py
Script de réorganisation des notebooks Tweety. A été utilisé pour diviser le notebook monolithique original en 7 notebooks thématiques.

**Usage:**
```bash
python reorganize_tweety.py
```

**Historique:**
- Création de Tweety-5 (Argumentation Abstraite - Dung uniquement)
- Création de Tweety-6 (Argumentation Structurée - ASPIC+, DeLP, ABA, ASP)
- Renommage de l'ancien Tweety-6 en Tweety-7
- Mise à jour des liens de navigation

### install_clingo.py
Script d'installation automatique de Clingo (solveur ASP) pour Windows/Linux.

**Usage:**
```bash
python install_clingo.py
```

**Fonctionnalités:**
- Téléchargement automatique de Clingo 5.7.1 depuis GitHub
- Extraction et installation dans ext_tools/clingo/
- Support Windows (ZIP) et Linux (tar.gz)
- Vérification de l'installation existante

## Maintenance

Ces scripts ont été utilisés pour la mise en place et la vérification de la série Tweety. Ils peuvent être réutilisés pour:
- Vérifier l'intégrité après modifications
- Réorganiser/refactoriser les notebooks
- Installer les dépendances externes
