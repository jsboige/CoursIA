# 📘 CoursIA

Bienvenue dans le dépôt **CoursIA**, qui contient les ressources et TPs pour le cours d'intelligence artificielle en C# et Python.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## 📋 Table des matières

- [Introduction](#introduction)
- [Structure du dépôt](#structure-du-dépôt)
- [Mise en route](#mise-en-route)
- [Parcours d'apprentissage](#parcours-dapprentissage)
- [Contenu des modules](#contenu-des-modules)
- [Suivis Projets](#suivis-projets)
- [Contribution](#contribution)
- [Licence](#licence)

## 🚀 Introduction

Ce dépôt contient un ensemble de notebooks Jupyter interactifs et de ressources pour l'apprentissage de l'intelligence artificielle, couvrant un large éventail de sujets allant du machine learning classique aux techniques d'IA générative modernes, en passant par l'IA symbolique et les algorithmes de recherche.

Les notebooks sont principalement en C# (utilisant .NET Interactive) et Python, offrant une approche pratique et hands-on pour comprendre les concepts d'IA.

## 🗂️ Structure du dépôt

Le dépôt est organisé en plusieurs sections thématiques :

```
MyIA.AI.Notebooks/
├── GenAI/               # IA Générative (OpenAI, LLMs, RAG, etc.)
├── ML/                  # Machine Learning avec ML.NET
├── IIT/                 # Integrated Information Theory
├── Probas/              # Probabilités et inférence bayésienne
├── Search/              # Algorithmes de recherche et optimisation
├── Sudoku/              # Résolution de Sudoku avec différentes approches
├── SymbolicAI/          # IA Symbolique (RDF, Z3, OR-Tools)
└── Config/              # Configuration pour les notebooks
```

## 🛠️ Mise en route

### Prérequis

Avant de commencer, assurez-vous d'avoir installé :

- [Python 3.9+](https://www.python.org/downloads/)
- [Visual Studio Code](https://code.visualstudio.com/)
- L'extension **Python** et **Jupyter** dans VSCode
- [Extension **.Net extension pack**](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.vscode-dotnet-pack)
- [.NET 9.0 SDK](https://dotnet.microsoft.com/download) (pour les notebooks C#)
- [OpenAI API key](https://platform.openai.com/signup/) (pour les notebooks GenAI)

### Installation des dépendances

1. **Créer et activer un environnement virtuel Python :**

   ```sh
   python -m venv venv
   source venv/bin/activate  # macOS/Linux
   venv\Scripts\activate      # Windows
   ```

2. **Installer Jupyter et les bibliothèques nécessaires :**

   ```sh
   pip install --upgrade pip
   pip install jupyter openai
   ```

3. **Ajouter l'environnement à Jupyter :**

   ```sh
   python -m ipykernel install --user --name=coursia --display-name "Python (CoursIA)"
   ```

4. **Configurer les clés API (pour GenAI) :**
   
   Créez un fichier `.env` dans le dossier `MyIA.AI.Notebooks/GenAI/` en vous basant sur le fichier `.env.example`.

### Configuration pour les notebooks C#

Pour les notebooks C#, vous devez également :

1. **Restaurer les packages NuGet :**

   ```sh
   dotnet restore MyIA.CoursIA.sln
   ```

2. **Configurer les paramètres API :**
   
   Copiez `MyIA.AI.Notebooks/Config/settings.json.openai-example` vers `MyIA.AI.Notebooks/Config/settings.json` et ajoutez votre clé API.

## 🎓 Parcours d'apprentissage

Voici un parcours d'apprentissage suggéré pour explorer ce dépôt :

1. **Introduction au Machine Learning** - Commencez par les notebooks dans `ML/`
2. **Algorithmes de recherche** - Explorez les notebooks dans `Search/` et `Sudoku/`
3. **IA Symbolique** - Découvrez les notebooks dans `SymbolicAI/`
4. **Probabilités et inférence** - Étudiez les notebooks dans `Probas/`
5. **IA Générative** - Terminez avec les notebooks dans `GenAI/`

## 📚 Contenu des modules

### 🤖 GenAI (IA Générative)

Notebooks sur l'IA générative, les grands modèles de langage (LLMs), et les techniques associées :

- `OpenAI_Intro.ipynb` - Introduction à l'API OpenAI
- `PromptEngineering.ipynb` - Techniques d'ingénierie de prompts
- `RAG.ipynb` - Retrieval Augmented Generation
- `LocalLlama.ipynb` - Utilisation de modèles locaux comme Llama
- `SemanticKernel/` - Notebooks sur Microsoft Semantic Kernel

### 📊 ML (Machine Learning)

Série de notebooks sur le machine learning avec ML.NET :

- `ML-1-Introduction.ipynb` - Introduction au ML avec ML.NET
- `ML-2-Data&Features.ipynb` - Préparation des données et ingénierie des caractéristiques
- `ML-3-Entrainement&AutoML.ipynb` - Entraînement de modèles et AutoML
- `ML-4-Evaluation.ipynb` - Évaluation des modèles
- `TP-prevision-ventes.ipynb` - TP sur la prévision des ventes

### 🧩 Sudoku

Notebooks illustrant différentes approches pour résoudre des Sudokus :

- `Sudoku-0-Environment.ipynb` - Mise en place de l'environnement
- `Sudoku-1-Backtracking.ipynb` - Résolution par backtracking
- `Sudoku-2-Genetic.ipynb` - Algorithmes génétiques
- `Sudoku-3-ORTools.ipynb` - Utilisation d'OR-Tools
- `Sudoku-4-Z3.ipynb` - Résolution avec le solveur Z3
- `Sudoku-5-DancingLinks.ipynb` - Algorithme de Dancing Links
- `Sudoku-6-Infer.ipynb` - Inférence probabiliste

### 🔍 Search (Recherche)

Notebooks sur les algorithmes de recherche et d'optimisation :

- `GeneticSharp-EdgeDetection.ipynb` - Détection de contours avec algorithmes génétiques
- `Portfolio_Optimization_GeneticSharp.ipynb` - Optimisation de portefeuille
- `PyGad-EdgeDetection.ipynb` - Détection de contours avec PyGad

### 🧠 SymbolicAI (IA Symbolique)

Notebooks sur l'IA symbolique et les approches formelles :

- `Linq2Z3.ipynb` - Utilisation du solveur Z3 avec LINQ
- `OR-tools-Stiegler.ipynb` - Résolution de problèmes avec OR-Tools
- `RDF.Net/` - Utilisation de RDF avec .NET

### 🔢 Probas (Probabilités)

Notebooks sur les probabilités et l'inférence bayésienne :

- `Infer-101.ipynb` - Introduction à l'inférence probabiliste

### 🧪 IIT (Integrated Information Theory)

Notebooks sur la théorie de l'information intégrée :

- `Intro_to_PyPhi.ipynb` - Introduction à PyPhi pour IIT

## 🧪 Scripts GenAI Auth - Écosystème ComfyUI-Qwen Sécurisé

Cette section contient les scripts pour l'installation, la validation et la gestion de l'écosystème ComfyUI-Qwen avec authentification sécurisée.

### 🚀 Installation Complète
Pour installer l'écosystème complet de manière automatisée :

```bash
# Installation complète automatisée
python scripts/genai-auth/core/setup_complete_qwen.py
```

### 🔍 Validation et Diagnostic
Pour valider et diagnostiquer l'écosystème :

```bash
# Validation complète de l'écosystème
python scripts/genai-auth/core/validate_genai_ecosystem.py --verbose

# Diagnostic de l'authentification
python scripts/genai-auth/core/diagnose_comfyui_auth.py

# Synchronisation des tokens
python scripts/genai-auth/utils/token_synchronizer.py --unify
```

### 📚 Documentation Complète
La documentation complète de l'écosystème est disponible dans :

- **[Index de l'écosystème](docs/suivis/genai-image/README-ECOSYSTEME-COMFYUI-QWEN-20251125.md)** : Vue d'ensemble et navigation
- **[Guide d'utilisation](docs/suivis/genai-image/GUIDE-UTILISATION-COMFYUI-QWEN-20251125.md)** : Instructions complètes (567 lignes)
- **[Architecture technique](docs/suivis/genai-image/ARCHITECTURE-FINALE-COMFYUI-QWEN-20251125.md)** : Architecture détaillée (456 lignes)
- **[Rapport de mission](docs/suivis/genai-image/RAPPORT-FINAL-MISSION-COMFYUI-LOGIN-20251125.md)** : Mission accomplie (334 lignes)

### Structure des Scripts
L'écosystème est organisé de manière modulaire et maintenable :

```
scripts/genai-auth/
├── README.md                          (376 lignes - Documentation complète)
├── core/                              Scripts principaux
│   ├── setup_complete_qwen.py         (527 lignes - Installation complète)
│   ├── validate_genai_ecosystem.py    (Validation écosystème)
│   ├── diagnose_comfyui_auth.py       (Diagnostic authentification)
│   └── install_comfyui_login.py       (Installation ComfyUI-Login)
├── utils/                             Utilitaires spécialisés
│   ├── token_synchronizer.py          (608 lignes - Synchroniseur unifié)
│   ├── comfyui_client_helper.py       (1305 lignes - Client HTTP)
│   ├── workflow_utils.py              (489 lignes - Manipulation workflows)
│   └── diagnostic_utils.py            (426 lignes - Utilitaires diagnostic)
└── tests/                             Scripts de test
    └── genai-improvements/           Tests et débogage
```

### 🐳 Configuration Docker
La configuration Docker est organisée dans `docker-configurations/` :

```
docker-configurations/
├── README.md                    (170 lignes - Documentation infrastructure)
├── comfyui-qwen/              (Configuration principale)
│   ├── docker-compose.yml
│   ├── .env
│   └── workspace/
├── models/                      (Modèles partagés)
├── cache/                       (Cache partagé)
└── orchestrator/                (Service d'orchestration)
```
```

## 📂 Suivis Projets

Cette section regroupe les suivis détaillés des projets en cours et terminés.

### 🖼️ Projet GenAI Image

- **Description** : Déploiement d'une infrastructure locale ComfyUI + Qwen pour la génération et l'édition d'images par IA. Inclut la mise en production SSL/IIS, le monitoring et le design de workflows pédagogiques.
- **Statut** : Phase 13A complétée, Phase 13B en planification
- **Accès** : [`docs/suivis/genai-image/README.md`](docs/suivis/genai-image/README.md)

## 👥 Contribution

Les contributions à ce dépôt sont les bienvenues ! Si vous souhaitez contribuer :

1. Forkez le dépôt
2. Créez une branche pour votre fonctionnalité (`git checkout -b feature/nouvelle-fonctionnalite`)
3. Committez vos changements (`git commit -m 'Ajout d'une nouvelle fonctionnalité'`)
4. Poussez vers la branche (`git push origin feature/nouvelle-fonctionnalite`)
5. Ouvrez une Pull Request

## 📄 Licence

Ce projet est sous licence MIT - voir le fichier [LICENSE](LICENSE) pour plus de détails.

---

🚀 Bon apprentissage et bonnes expérimentations avec l'IA !
