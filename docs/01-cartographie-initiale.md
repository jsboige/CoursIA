# Cartographie Initiale du Dépôt CoursIA

Ce document dresse un état des lieux du contenu pédagogique du dépôt à la date du 2025-08-04.

## 1. Vue d'ensemble de l'organisation

Le dépôt s'articule autour d'un répertoire principal `MyIA.AI.Notebooks` qui centralise l'ensemble des contenus pédagogiques. La structure est thématique, reflétant les grandes familles de l'IA. Un fichier [`index.md`](../../index.md) à la racine sert de table des matières, ce qui est un excellent point d'entrée.

- **Hétérogénéité des langages :** Le projet est bilingue, utilisant à la fois **Python** (pour les notebooks d'introduction à l'IA Générative, PyTorch, etc.) et **C#/.NET** (pour `ML.NET`, `Semantic Kernel`, l'IA Symbolique avec `Z3`, `OR-Tools`, etc.). Cette dualité est une caractéristique forte du projet.

## 2. Thèmes de formation identifiés

Voici une liste des principaux thèmes couverts, avec des liens vers les contenus pertinents.

### 🤖 IA Générative (`GenAI/`)
- **Concepts de base :** Introduction aux LLMs via [OpenAI_Intro.ipynb](../../MyIA.AI.Notebooks/GenAI/1_OpenAI_Intro.ipynb) et au [PromptEngineering.ipynb](../../MyIA.AI.Notebooks/GenAI/2_PromptEngineering.ipynb).
- **Techniques avancées :** Approche du [RAG.ipynb](../../MyIA.AI.Notebooks/GenAI/3_RAG.ipynb) et de l'utilisation de modèles locaux comme [LocalLlama.ipynb](../../MyIA.AI.Notebooks/GenAI/4_LocalLlama.ipynb).
- **Agentique et Orchestration :** Un large éventail de contenus sur **Microsoft Semantic Kernel** ([Intro](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb), [Avancé](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb), [Agents](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/03-SemanticKernel-Agents.ipynb)) montre une forte orientation vers la construction d'agents intelligents en C#.

### 📊 Machine Learning (`ML/`)
- **Fondamentaux :** Le parcours est bien structuré avec `ML.NET` ([Introduction](../../MyIA.AI.Notebooks/ML/ML-1-Introduction.ipynb), [Données](../../MyIA.AI.Notebooks/ML/ML-2-Data&Features.ipynb), [Entraînement](../../MyIA.AI.Notebooks/ML/ML-3-Entrainement&AutoML.ipynb), [Évaluation](../../MyIA.AI.Notebooks/ML/ML-4-Evaluation.ipynb)).
- **Cas pratique :** Un TP sur la [prévision des ventes](../../MyIA.AI.Notebooks/ML/TP-prevision-ventes.ipynb) ancre les concepts dans un contexte réel.

### 🧠 IA Symbolique (`SymbolicAI/`)
- **Résolution de contraintes :** Utilisation de solveurs comme [Z3 avec LINQ](../../MyIA.AI.Notebooks/SymbolicAI/Linq2Z3.ipynb) et [OR-Tools](../../MyIA.AI.Notebooks/SymbolicAI/OR-tools-Stiegler.ipynb).
- **Web Sémantique :** Introduction à [RDF.Net](../../MyIA.AI.Notebooks/SymbolicAI/RDF.Net/RDF.Net.ipynb).

### 🔍 Autres thèmes
- **Algorithmes de recherche :** Résolution de problèmes (Sudoku) et optimisation ([génétique](../../MyIA.AI.Notebooks/Search/GeneticSharp-EdgeDetection.ipynb)).
- **Probabilités :** Introduction à l'inférence probabiliste ([Infer-101.ipynb](../../MyIA.AI.Notebooks/Probas/Infer-101.ipynb)).

## 3. Évaluation et analyse

### Points forts
- **Richesse thématique :** Le dépôt couvre un large spectre de l'IA, du symbolique au génératif.
- **Double compétence C#/Python :** Une force rare et différenciante, permettant de cibler différents écosystèmes.
- **Focus sur l'agentique :** L'investissement sur `Semantic Kernel` est un atout majeur pour notre objectif de formation à la datascience agentique.
- **Documentation d'accueil :** Le fichier `index.md` est un excellent guide pour les nouveaux arrivants.

### Faiblesses et "trous" dans le parcours
- **Silo entre les langages :** Les parcours semblent très orientés soit Python, soit C#. Il y a peu de ponts entre les deux mondes (par exemple, utiliser un modèle entraîné en Python depuis une application C#).
- **Manque sur le cycle de vie de la donnée (Data Science) :** Bien que le ML soit abordé, les étapes amont (collecte, nettoyage avancé, data-viz) et aval (déploiement, monitoring de modèles) sont peu couvertes.
- **Agentique Python :** L'agentique est presque exclusivement C#. Des équivalents en Python (e.g., LangChain, LlamaIndex) sont absents.
- **Projet intégrateur :** Il manque un projet fil rouge qui combinerait plusieurs briques (par exemple, un agent en C# utilisant un modèle de ML custom entraîné en Python pour une tâche de datascience).
