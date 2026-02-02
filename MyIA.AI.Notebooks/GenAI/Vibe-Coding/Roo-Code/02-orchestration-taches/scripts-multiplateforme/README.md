# 🔄 Scripts Multiplateforme avec Roo

## Introduction

Dans un environnement de développement moderne, il est courant de travailler avec des équipes utilisant différents systèmes d'exploitation. Créer des scripts qui fonctionnent de manière cohérente sur Windows et macOS/Linux peut représenter un défi. Ce guide vous présente comment utiliser Roo en mode Orchestrator pour créer et gérer des scripts multiplateforme.

## Défis de la compatibilité multiplateforme

Les principaux défis lors de la création de scripts multiplateforme incluent :

1. **Différences de syntaxe** : PowerShell vs Bash/Shell
2. **Chemins de fichiers** : Barres obliques inversées (Windows) vs barres obliques (Unix)
3. **Commandes système** : Différentes commandes pour les mêmes opérations
4. **Encodage de fichiers** : Différences dans les retours à la ligne (CRLF vs LF)
5. **Permissions d'exécution** : Gestion différente selon les systèmes

## Approches pour la compatibilité multiplateforme

### 1. Scripts parallèles

Maintenir des versions séparées mais équivalentes pour chaque plateforme :
- `script.ps1` pour Windows (PowerShell)
- `script.sh` pour macOS/Linux (Bash)

Cette approche est simple mais nécessite de maintenir plusieurs fichiers.

### 2. Scripts universels

Utiliser des langages qui fonctionnent de manière identique sur toutes les plateformes :
- Python
- Node.js
- Ruby

Cette approche nécessite l'installation de l'environnement d'exécution sur toutes les machines.

### 3. Scripts conditionnels

Créer des scripts qui détectent le système d'exploitation et exécutent le code approprié :
- Scripts Bash avec détection de plateforme
- PowerShell Core (disponible sur toutes les plateformes)

## Rôle du mode Orchestrator

Le mode Orchestrator de Roo peut vous aider à :

1. **Analyser les besoins** : Comprendre les exigences multiplateforme
2. **Concevoir la stratégie** : Choisir l'approche la plus adaptée
3. **Implémenter les scripts** : Créer des versions compatibles
4. **Tester la compatibilité** : Vérifier le fonctionnement sur différentes plateformes
5. **Documenter l'utilisation** : Créer des instructions claires pour tous les utilisateurs

## Exemples de scripts multiplateforme

Dans ce répertoire, vous trouverez des exemples de scripts équivalents pour Windows et macOS/Linux :

- [`exemple-script.ps1`](./exemple-script.ps1) : Version PowerShell pour Windows
- [`exemple-script.sh`](./exemple-script.sh) : Version Bash pour macOS/Linux

Ces scripts démontrent comment effectuer les mêmes opérations sur différentes plateformes.

## Bonnes pratiques

### Conception de scripts

1. **Privilégier la simplicité** : Plus un script est simple, plus il est facile de le rendre compatible
2. **Modulariser le code** : Séparer les fonctionnalités pour faciliter la maintenance
3. **Utiliser des variables d'environnement** : Pour les chemins et configurations spécifiques à la plateforme
4. **Documenter les différences** : Commenter les sections spécifiques à chaque plateforme

### Gestion des chemins de fichiers

1. **Utiliser des chemins relatifs** quand c'est possible
2. **Construire les chemins dynamiquement** en utilisant les séparateurs appropriés
3. **Utiliser des variables d'environnement** pour les répertoires système

### Tests

1. **Tester sur toutes les plateformes cibles**
2. **Créer des scénarios de test** couvrant les cas particuliers
3. **Automatiser les tests** si possible

## Outils utiles

### Pour Windows (PowerShell)

- **PowerShell Core** : Version multiplateforme de PowerShell
- **Windows Subsystem for Linux (WSL)** : Pour tester les scripts Linux sur Windows

### Pour macOS/Linux (Bash)

- **shellcheck** : Outil d'analyse statique pour les scripts shell
- **bash** : Disponible sur la plupart des systèmes Unix

### Outils multiplateforme

- **Git Bash** : Environnement Bash pour Windows
- **Visual Studio Code** : Éditeur avec support pour PowerShell et Bash

## Installation et prérequis

Pour plus d'informations sur l'installation des prérequis nécessaires pour exécuter les scripts multiplateforme, consultez le guide [installation.md](./installation.md).

## Conclusion

La création de scripts multiplateforme peut sembler complexe, mais avec les bonnes pratiques et outils, il est possible de maintenir des workflows cohérents sur différents systèmes d'exploitation. Le mode Orchestrator de Roo peut vous aider à naviguer dans cette complexité en coordonnant les différentes étapes du processus.