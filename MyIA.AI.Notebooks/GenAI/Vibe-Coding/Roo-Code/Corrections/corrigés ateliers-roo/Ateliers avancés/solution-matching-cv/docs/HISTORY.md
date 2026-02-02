# Historique du Projet

Ce document retrace les grandes étapes du développement de l'application `solution-matching-cv`, des premières expérimentations jusqu'à la version stabilisée actuelle. Il consolide les informations de plusieurs journaux de développement et rapports de mission.

## Phase 1 : L'Ère Streamlit - Initialisation et Débogage Complexe

La mission a débuté avec un objectif simple : lancer et tester une application **Streamlit** existante. Cependant, cette phase a été marquée par une cascade de défis techniques.

*   **Problèmes d'Environnement :** Les premières tentatives ont révélé un environnement de développement non configuré, nécessitant l'installation manuelle de toutes les dépendances.

*   **Instabilité des Tests E2E :** L'enjeu principal fut la mise en place de tests de bout en bout (E2E) avec **Playwright**. La nature dynamique de Streamlit a rendu ces tests extrêmement instables. L'équipe a consacré un temps considérable à lutter contre des problèmes de synchronisation ("race conditions"), des sélecteurs imprécis et même des "heisenbugs" où l'acte d'observer le test modifiait son comportement.

*   **Bugs Applicatifs :** Parallèlement, l'application elle-même présentait des bugs critiques, notamment un problème de "page blanche" causé par un conflit de boucles d'événements (`asyncio`) entre Streamlit et la bibliothèque `semantic_kernel`. Une refactorisation en "chargement paresseux" (lazy loading) a permis de résoudre ce conflit.

*   **Conclusion de la Phase 1 :** À la fin de cette phase, l'application était fonctionnelle, mais au prix de l'abandon de la suite de tests E2E, jugée trop fragile pour être fiable. Cette situation a directement conduit à la décision radicale de la phase suivante.

## Phase 2 : Le Pivot Stratégique vers Flask

Face à l'impossibilité de garantir la fiabilité des tests avec Streamlit, un ultimatum a été posé : la solution doit être testable.

*   **La Décision :** L'équipe a pris la décision d'abandonner Streamlit pour reconstruire l'application avec **Flask**, un micro-framework web standard reconnu pour générer un DOM stable, rendant les tests Playwright simples et fiables.

*   **Simplification et Reconstruction :**
    *   **Dépendances Assainies :** La migration a été l'occasion de retirer la bibliothèque `semantic-kernel`, qui était une source de lourdeur et d'instabilité, au profit d'une logique plus simple au départ.
    *   **Nouvelle Interface :** L'application a été reconstruite autour d'un serveur Flask simple et d'une page HTML unique avec un formulaire d'upload.
    *   **Résolution de Problèmes Profonds :** Cette reconstruction a permis de découvrir et de résoudre des problèmes d'environnement sous-jacents (ex: installation `numpy` corrompue), menant à la création d'un environnement virtuel propre et stable.

*   **Succès de la Validation :** La nouvelle suite de tests E2E a été réécrite pour Flask et s'est exécutée avec succès, validant de bout en bout la robustesse de la nouvelle architecture.

## Phase 3 : Enrichissement Fonctionnel et Finalisation

Une fois la plateforme stabilisée sur Flask, le focus a été mis sur l'enrichissement de la logique métier et la consolidation du projet.

*   **Réintroduction des Algorithmes :** Le travail initial sur les différents algorithmes a été réintégré, transformant l'application en un outil de comparaison. Trois logiques sont maintenant disponibles :
    1.  **Simple :** Comptage de mots-clés (la baseline initiale).
    2.  **Sémantique (Meilleur Score) :** Utilise les embeddings pour trouver le meilleur score.
    3.  **Sémantique (Stable) :** Utilise l'algorithme de Gale-Shapley pour un appariement optimal.

*   **Correction et Amélioration des Algorithmes :**
    *   L'algorithme "stable" a été corrigé pour gérer les cas où le nombre de consultants et de postes est inégal, en utilisant une version plus générale de l'algorithme (Hospital-Resident).
    *   Les algorithmes "simple" et "meilleur score" ont été modifiés pour garantir des assignations uniques (un consultant par poste), afin de pouvoir les comparer équitablement à l'algorithme stable.

*   **Mise en Place d'une Suite de Tests Unitaires :** Une suite de tests unitaires robuste a été développée (`tests/unit/`) pour valider chaque algorithme de manière isolée.

*   **Conclusion de la Phase 3 :** Le projet a atteint une première forme stable : une application Flask fonctionnelle, validée par des tests.

## Phase 4 : Optimisation et Amélioration de l'Expérience

Cette phase s'est concentrée sur la résolution des problèmes de performance et l'amélioration de l'ergonomie de l'application.

*   **Optimisation des Performances Sémantiques :**
    *   **Migration vers ChromaDB :** La base de données vectorielle en mémoire a été remplacée par **ChromaDB** pour assurer la persistance des embeddings des CVs, éliminant le besoin de les recalculer à chaque fois.
    *   **Batch Processing :** Le calcul des embeddings pour les fiches de poste a été optimisé en utilisant un traitement par lots (batching), réduisant drastiquement le nombre d'appels à l'API OpenAI.

*   **Mise à Jour Technique :** Une mise à niveau de la bibliothèque `semantic-kernel` vers une nouvelle version majeure (impliquant des changements d'API importants) a été nécessaire, entraînant un refactoring significatif de la logique de matching sémantique.

*   **Amélioration de l'Expérience Utilisateur (UX) :**
    *   **Pré-chargement des Données :** L'application charge désormais les fichiers CSV par défaut au démarrage, rendant les tests et les démonstrations plus fluides.
    *   **Harmonisation des Résultats :** Les trois algorithmes ont été refactorisés pour garantir que leurs tableaux de résultats aient une structure de colonnes identique.
    *   **Amélioration Visuelle :** Une feuille de style CSS a été ajoutée pour améliorer la lisibilité et l'apparence de l'interface.

## Phase 5 : Fiabilisation du Cache et Validation des Performances

La dernière étape a consisté à solidifier le mécanisme de cache pour garantir son bon fonctionnement et à prouver son efficacité.

*   **Débogage du Cache d'Idempotence :**
    *   **Problème :** Malgré l'utilisation d'IDs déterministes (basés sur le hash du contenu), les tests de performance révélaient que les données étaient systématiquement ré-indexées, entraînant des appels inutiles et coûteux à l'API OpenAI.
    *   **Investigation :** Une analyse approfondie a montré que la méthode `get` du connecteur `ChromaStore` de Semantic Kernel ne permettait pas de récupérer efficacement tous les IDs existants pour la comparaison.
    *   **Solution :** Après une analyse du code source de la bibliothèque `semantic-kernel`, la solution a été d'accéder à la collection ChromaDB native via la méthode privée `_get_collection()`. Cette approche, bien que non idéale, était la seule permettant d'implémenter une vérification d'idempotence fiable.

*   **Validation Quantitative des Performances :**
    *   Pour valider l'efficacité du cache, un nouveau test (`test_cache_performance.py`) a été créé.
    *   Ce test compare deux scénarios : une indexation "à froid" avec une base de données volatile (en mémoire) et une indexation "à chaud" avec la base de données persistante.
    *   Les résultats ont démontré un gain de performance spectaculaire, avec une seconde passe d'indexation (utilisant le cache) **plus de 100 fois plus rapide** que la première, validant ainsi l'approche.

## Phase 6 : Harmonisation des Scripts et Support Multi-Plateforme

Cette phase a été dédiée à l'amélioration de l'expérience développeur en professionnalisant les scripts d'exécution et en assurant la compatibilité avec différents systèmes d'exploitation.

*   **Centralisation et Nettoyage :**
    *   Tous les scripts d'exécution (`.ps1`, `.py`) ont été déplacés de la racine vers un dossier dédié `/scripts`.
    *   Les scripts redondants ou obsolètes ont été supprimés.

*   **Fiabilisation des Scripts :**
    *   Les chemins codés en dur ont été éliminés de tous les scripts.
    *   Une logique a été mise en place pour lire la configuration (notamment le chemin vers l'environnement virtuel) depuis un fichier `.env`, rendant les scripts portables et robustes.

*   **Support Multi-Plateforme :**
    *   Des versions Bash (`.sh`) de tous les scripts PowerShell ont été créées pour garantir une expérience équivalente sur macOS et Linux.

*   **Mise à Jour de la Documentation :**
    *   L'ensemble de la documentation (`README.md`, `GETTING_STARTED.md`, `TESTING.md`) a été mis à jour pour refléter la nouvelle structure de scripts et fournir des instructions claires pour les utilisateurs de Windows, macOS et Linux.
    *   Le guide de démarrage inclut désormais des recommandations importantes, comme la création de l'environnement virtuel en dehors des dossiers synchronisés par le cloud.