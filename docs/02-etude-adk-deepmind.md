# Étude sur le framework agentique ADK et l'exemple MLE-STAR

**Date:** 2025-08-04
**Auteur:** Roo, Architecte IA

## 1. Objectif de l'étude

Cette étude vise à analyser le **Agent Development Kit (ADK)** de Google et son exemple d'application **Machine Learning Engineering (MLE-STAR)**. L'objectif est de fournir une synthèse claire des concepts, de l'architecture et des prérequis, destinée à un public de "product owners" et de "managers d'ingénieurs", afin d'évaluer la pertinence de cette technologie pour notre écosystème.

## 2. Agent Development Kit (ADK) - Le Framework

L'ADK est un framework conçu pour standardiser et simplifier le développement et le déploiement d'agents basés sur l'IA. Il vise à appliquer les bonnes pratiques du génie logiciel au monde de l'agentique.

### Philosophie et Concepts Clés

- **Agnosticisme et Compatibilité :** Bien qu'optimisé pour l'écosystème Google (Gemini, Vertex AI), l'ADK est fondamentalement agnostique :
    - **Modèle :** Il peut fonctionner avec différents LLMs.
    - **Déploiement :** Les agents peuvent être déployés localement, sur des conteneurs (Docker), ou des services cloud comme Google Cloud Run et GKE.
    - **Framework :** Il est compatible et peut intégrer des outils provenant d'autres frameworks comme LangChain ou CrewAI.
- **Langages Supportés :** Python et Java. Son existence vient combler un manque en agentique Python identifié dans notre cartographie initiale.
- **Architecture Multi-Agents :** C'est un principe fondamental. L'ADK facilite la création de systèmes complexes où plusieurs agents spécialisés collaborent, potentiellement de manière hiérarchique.
- **Orchestration Flexible :** Deux modes de fonctionnement sont possibles :
    - **Agents de Workflow (`Workflow agents`) :** Pour des pipelines déterministes et prévisibles (séquentiels, parallèles, boucles).
    - **Agents LLM (`LlmAgent`) :** Pour un routage dynamique et un comportement adaptatif où le LLM décide de la prochaine étape.
- **Écosystème d'Outils (`Tools`) :** Les agents peuvent être dotés de capacités via des outils. L'ADK supporte des outils pré-construits (Recherche Google, exécution de code), la création de fonctions Python comme outils, et l'intégration d'outils tiers (via OpenAPI, etc.).

## 3. L'exemple "Machine Learning Engineering" (MLE-STAR)

Cet exemple, basé sur le papier de recherche de DeepMind, est une implémentation de référence qui montre comment utiliser l'ADK pour une tâche de datascience complexe : **l'ingénierie de modèles de machine learning pour des compétitions**.

### But et Fonctionnement

Le but de l'agent MLE-STAR est d'automatiser le processus de création d'un modèle de ML performant. Pour cela, il suit un workflow sophistiqué :

1.  **Génération de Solution Initiale :** L'agent utilise un outil de recherche web pour trouver des notebooks et du code existants pour des problèmes similaires. Il analyse et fusionne les meilleures approches pour créer un premier pipeline de code fonctionnel.
2.  **Raffinement Ciblé par Blocs :** L'agent analyse le pipeline de code et identifie les blocs (ex: pré-traitement, sélection de modèle, hyperparamètres) qui ont le plus de potentiel d'amélioration. Il se concentre itérativement sur ces blocs pour les optimiser.
3.  **Stratégies d'Ensembling :** Il est capable de proposer et de tester différentes manières de combiner les prédictions de plusieurs modèles pour obtenir un résultat final plus robuste.
4.  **Robustesse et Fiabilité :** Le système inclut des sous-agents dédiés à des tâches critiques du cycle de vie ML :
    - Un **agent de débogage** pour corriger les erreurs de code.
    - Des **vérificateurs** pour éviter la fuite de données (`data leakage`) et s'assurer que toutes les données pertinentes sont utilisées.

### Apport pour la "Data Science"

L'exemple MLE-STAR illustre comment une approche agentique peut adresser des points faibles souvent négligés dans les parcours de formation ML : le déploiement, le monitoring, et l'optimisation itérative d'un pipeline complet.

## 4. Prérequis Techniques

Pour mettre en œuvre un projet basé sur l'ADK et l'exemple MLE-STAR, les compétences et outils suivants sont nécessaires :

- **Langage :** Python (3.12+).
- **Gestion de dépendances :** Poetry.
- **Écosystème Cloud :** Une bonne connaissance de Google Cloud Platform est indispensable. Le framework est fortement intégré avec :
    - **Vertex AI:** Pour les modèles (Gemini) et le déploiement (`Agent Engine`).
    - **Google Cloud Storage (GCS):** Pour le stockage des artefacts.
    - **Google Cloud CLI:** Pour l'authentification et la gestion des ressources.

## 5. Premières Étapes pour un Projet Simple

1.  **Installation :** Cloner le dépôt, installer les dépendances via `poetry install`.
2.  **Configuration :** Mettre en place les authentifications GCP et configurer les variables d'environnement (projet GCP, location, modèle à utiliser).
3.  **Définition de la Tâche :** Créer un répertoire pour la tâche contenant un descriptif et les fichiers de données.
4.  **Lancement :** Exécuter l'agent via la ligne de commande `adk run` ou l'interface web `adk web`.
5.  **Interaction :** Dialoguer avec l'agent pour lancer et suivre l'exécution de la tâche de ML.
