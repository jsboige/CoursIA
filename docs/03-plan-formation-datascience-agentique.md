# Plan de Formation : Data Science Agentique

Ce parcours pédagogique vise à former des techniciens et développeurs à la conception et à l'implémentation de solutions de data science modernes, basées sur des agents intelligents. Il comble le fossé entre la data science traditionnelle en Python et l'ingénierie d'agents complexes, avec un focus sur l'écosystème C#/.NET pour l'orchestration et le framework ADK de DeepMind pour l'agent de data science.

---

## Module 1 : Les Fondamentaux de la Data Science en Python

**Objectif :** Acquérir les compétences essentielles pour la manipulation, l'analyse et la visualisation de données en Python. Ce module comble les lacunes identifiées dans le parcours existant.

*   **Notebook 1.1 : Introduction à l'écosystème Python pour la Data Science**
    *   **Description :** Prise en main de l'environnement de travail (Jupyter, VS Code), et introduction aux bibliothèques fondamentales.
*   **Notebook 1.2 : Manipulation de Données avec NumPy**
    *   **Description :** Apprendre à créer et manipuler des tableaux multi-dimensionnels, effectuer des opérations mathématiques vectorisées et comprendre le broadcasting.
*   **Notebook 1.3 : Analyse de Données avec Pandas**
    *   **Description :** Maîtriser les DataFrames pour le nettoyage, la transformation, le filtrage, le groupage et l'agrégation de données structurées.
*   **Notebook 1.4 : Visualisation de Données avec Matplotlib et Seaborn**
    *   **Description :** Créer des graphiques et des visualisations informatives pour explorer les données et communiquer les résultats d'une analyse.
*   **Notebook 1.5 : Introduction au Machine Learning avec Scikit-Learn**
    *   **Description :** Découvrir le cycle de vie d'un projet de ML : préparation des données, entraînement d'un modèle simple (régression/classification), et évaluation de sa performance.

---

## Module 2 : Introduction à l'Agentique en Python

**Objectif :** Faire la transition en douceur de la programmation Python classique vers la conception d'agents. Nous utilisons LangChain comme une première étape accessible avant d'aborder un framework plus complexe comme l'ADK.

*   **Notebook 2.1 : Les concepts de l'IA Agentique**
    *   **Description :** Comprendre ce qu'est un agent, le cycle "Perception-Réflexion-Action", et les concepts de LLMs, d'outils (`tools`) et de `prompt engineering` avancé.
*   **Notebook 2.2 : Construire son premier Agent avec LangChain**
    *   **Description :** Créer un agent simple capable d'utiliser des outils (ex: une recherche web, une calculatrice) pour répondre à une question.
*   **Notebook 2.3 : Agentique et Manipulation de Données**
    *   **Description :** Développer un agent LangChain capable d'interagir avec un DataFrame Pandas pour répondre à des questions en langage naturel sur un jeu de données.

---

## Module 3 : Plongée dans le Framework ADK de DeepMind

**Objectif :** Se familiariser avec le framework ADK (`Agent Development Kit`) et son application de référence `MLE-STAR` pour l'ingénierie de Machine Learning.

*   **Notebook 3.1 : Découverte de l'écosystème ADK**
    *   **Description :** Installation et configuration de l'environnement (Python 3.12+, Poetry, GCP CLI), et compréhension de l'architecture (Agents de Workflow, Agents LLM, Outils).
*   **Notebook 3.2 : Lancer son premier agent ADK**
    *   **Description :** Exécuter un agent pré-configuré simple pour comprendre le cycle de vie : définition de la tâche, lancement, et interaction via la ligne de commande ou l'interface web.
*   **Notebook 3.3 : Analyse du workflow de l'agent MLE-STAR**
    *   **Description :** Étudier en détail le fonctionnement de l'agent MLE-STAR : génération de solution, raffinement par blocs, ensembling et mécanismes de robustesse (débogage, `data leakage`).

---

## Module 4 : Projet Intégrateur - Orchestrateur C# et Agent Data Scientist Python

**Objectif :** Mettre en pratique toutes les compétences acquises dans un projet qui combine l'écosystème C#/.NET pour l'orchestration de haut niveau et l'écosystème Python/ADK pour la tâche spécialisée de data science.

*   **Projet Final : Un Système Automatisé de Reporting Financier**
    *   **Description :** L'objectif est de construire un système où un utilisateur peut demander, en langage naturel, un rapport d'analyse sur des données de ventes.
    *   **Composant 1 : L'Orchestrateur (C# / Semantic Kernel)**
        *   **Rôle :** Interface principale avec l'utilisateur. Il analyse la requête, identifie les données nécessaires, et délègue la tâche d'analyse à l'agent spécialisé. Il est responsable de la mise en forme du rapport final.
        *   **Notebook 4.1.C# :** Créer le plugin Semantic Kernel qui pilote l'agent Python.
    *   **Composant 2 : L'Agent de Data Science (Python / ADK)**
        *   **Rôle :** C'est un agent spécialisé basé sur l'ADK. Il reçoit une instruction de l'orchestrateur (ex: "Analyse les ventes du produit X pour le trimestre Y et identifie les tendances"). Il exécute un pipeline de data science (nettoyage, analyse, visualisation), génère les résultats (texte, graphiques), et les retourne à l'orchestrateur.
        *   **Notebook 4.2.Py :** Développer l'agent ADK et ses outils personnalisés pour l'analyse de données.
    *   **Notebook 4.3.Intégration :** Faire communiquer l'orchestrateur C# et l'agent Python via une API simple.