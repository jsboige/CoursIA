# 📁 Gestion de Fichiers avec Quickfiles

## Introduction

La gestion efficace des fichiers est essentielle dans tout projet de développement. Roo dispose d'un MCP (Model Context Protocol) spécialisé appelé **Quickfiles** qui permet de manipuler les fichiers de manière plus efficace et plus puissante que les outils de base.

> **Note d'intégration**: Quickfiles est désormais disponible dans le dépôt principal sous `mcps/internal/quickfiles-server/`.

Ce guide vous présente les fonctionnalités de Quickfiles et comment l'utiliser dans le cadre du mode Orchestrator pour optimiser vos workflows de gestion de fichiers.

## Qu'est-ce que Quickfiles ?

Quickfiles est un MCP interne qui étend les capacités de Roo en matière de gestion de fichiers, offrant des fonctionnalités avancées comme :

- Lecture multiple de fichiers en une seule opération
- Listage optimisé de répertoires avec options de filtrage et de tri
- Recherche avancée dans les fichiers avec contexte
- Édition multiple de fichiers en une seule opération
- Extraction de structure de documents Markdown
- Opérations de recherche et remplacement avancées

## Avantages par rapport aux outils standard

| Fonctionnalité | Outils standard | Quickfiles |
|----------------|-----------------|------------|
| Lecture de fichiers | Un fichier à la fois | Plusieurs fichiers en parallèle |
| Listage de répertoires | Simple liste de fichiers | Options de tri, filtrage, et informations détaillées |
| Recherche | Recherche basique | Recherche avec contexte et expressions régulières |
| Édition | Modification d'un fichier à la fois | Modifications multiples en une opération |
| Performance | Limitée pour les gros fichiers | Optimisée avec troncature automatique |

## Outils disponibles dans Quickfiles

Quickfiles propose plusieurs outils spécialisés :

1. **read_multiple_files** : Lecture parallèle de plusieurs fichiers
2. **list_directory_contents** : Listage avancé de répertoires
3. **search_in_files** : Recherche de motifs dans les fichiers
4. **edit_multiple_files** : Édition de plusieurs fichiers en une opération
5. **search_and_replace** : Recherche et remplacement avancés
6. **extract_markdown_structure** : Analyse de la structure des fichiers Markdown
7. **delete_files** : Suppression de fichiers

## Intégration avec le mode Orchestrator

Le mode Orchestrator peut tirer parti de Quickfiles pour :

1. **Analyse de codebase** :
   - Lister la structure du projet
   - Rechercher des motifs spécifiques dans le code
   - Extraire la structure de la documentation

2. **Refactorisation à grande échelle** :
   - Identifier les fichiers à modifier
   - Appliquer des modifications cohérentes sur plusieurs fichiers
   - Vérifier les résultats des modifications

3. **Migration de projets** :
   - Analyser la structure existante
   - Rechercher des dépendances
   - Appliquer des transformations systématiques

4. **Gestion de documentation** :
   - Extraire la structure des documents Markdown
   - Mettre à jour des références dans plusieurs fichiers
   - Réorganiser la documentation

## Bonnes pratiques

- **Commencez par l'exploration** : Utilisez `list_directory_contents` pour comprendre la structure du projet
- **Recherchez avant de modifier** : Utilisez `search_in_files` pour identifier les fichiers à modifier
- **Vérifiez avant d'appliquer** : Utilisez l'option `preview` dans `search_and_replace` pour voir les changements avant de les appliquer
- **Combinez les outils** : Utilisez Quickfiles en combinaison avec d'autres MCP pour des workflows complets

## Pour aller plus loin

Pour des exemples concrets d'utilisation de Quickfiles dans différents scénarios, consultez le guide [exemples-quickfiles.md](./exemples-quickfiles.md).

## Limitations

- Quickfiles est optimisé pour les opérations sur des fichiers texte
- Les fichiers binaires peuvent ne pas être correctement traités
- Des limites de taille sont appliquées pour éviter les problèmes de performance
- Certaines opérations complexes peuvent nécessiter plusieurs étapes

## Conclusion

Quickfiles est un outil puissant qui, lorsqu'il est utilisé dans le cadre du mode Orchestrator, permet de gérer efficacement les fichiers dans des projets de toute taille. En combinant ses fonctionnalités avec d'autres outils de Roo, vous pouvez créer des workflows automatisés pour diverses tâches de gestion de fichiers.

## Installation et configuration

Pour utiliser Quickfiles, vous devez l'installer et le configurer comme suit :

```bash
# Depuis la racine du dépôt principal
cd mcps/internal/quickfiles-server
npm install
node ./build/index.js
```

Pour plus de détails sur l'installation et la configuration, consultez la documentation dans le dépôt principal sous `mcps/internal/quickfiles-server/README.md`.