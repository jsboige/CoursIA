# Solution de Matching CV - Fiches de Poste

Ce projet est une application web conçue pour comparer et évaluer différents algorithmes de matching entre des CV de consultants et des fiches de poste. Il sert de plateforme d'expérimentation pour des approches allant de la simple recherche par mots-clés à des techniques sémantiques avancées basées sur des modèles de langage.

L'objectif principal est de fournir un outil robuste, testable et performant pour identifier les meilleurs profils pour un poste donné.

## Structure du Projet

-   `/app` : Contient le cœur de l'application Flask et la logique métier.
-   `/scripts` : Scripts d'automatisation pour lancer l'application, les tests, etc.
-   `/data` : Données brutes (CV, fiches de poste).
-   `/tests` : Tests unitaires et end-to-end.
-   `/docs` : Documentation complète du projet.

## Navigation

-   **Pour une vue d'ensemble complète, commencez par le [document d'introduction](docs/INTRODUCTION.md).**
-   Pour comprendre le fonctionnement interne, consultez l'[**architecture technique**](docs/ARCHITECTURE.md).
-   Pour lancer l'application, suivez le [**guide de démarrage**](docs/GETTING_STARTED.md).

## Lancement Rapide

Tous les scripts principaux sont situés dans le dossier `/scripts`. Ils sont fournis en version PowerShell (`.ps1`) pour Windows et Bash (`.sh`) pour macOS/Linux.

-   **Installer les dépendances :**
    -   *Windows :*
        ```powershell
        ./scripts/install_deps.ps1
        ```
    -   *macOS/Linux :*
        ```bash
        ./scripts/install_deps.sh
        ```

-   **Lancer l'application web :**
    -   *Windows :*
        ```powershell
        ./scripts/run_app.ps1
        ```
    -   *macOS/Linux :*
        ```bash
        ./scripts/run_app.sh
        ```

-   **Lancer les tests unitaires :**
    -   *Windows :*
        ```powershell
        ./scripts/run_unit_tests.ps1
        ```
    -   *macOS/Linux :*
        ```bash
        ./scripts/run_unit_tests.sh
        ```

-   **Lancer les tests End-to-End :**
    -   *Windows :*
        ```powershell
        ./scripts/run_e2e_tests.ps1
        ```
    -   *macOS/Linux :*
        ```bash
        ./scripts/run_e2e_tests.sh
        ```

## Fonctionnalités

-   **Interface Web Simple :** Une application Flask légère pour lancer les comparaisons.
-   **Trois Algorithmes de Matching :**
    1.  **Simple :** Basé sur le comptage de mots-clés.
    2.  **Sémantique (Meilleur Score) :** Utilise des embeddings pour trouver le meilleur score de similarité.
    3.  **Sémantique (Stable) :** Applique l'algorithme de Gale-Shapley pour un appariement optimal et stable.
-   **Cache de Performance :** Utilise ChromaDB pour stocker les embeddings et éviter les recalculs coûteux.
-   **Suite de Tests Complète :** Inclut des tests unitaires et des tests de bout en bout (E2E) pour garantir la fiabilité.

## Documentation Complète

Toute la documentation du projet est centralisée dans le répertoire `/docs`. Nous vous invitons à commencer par le [document d'introduction](docs/INTRODUCTION.md) pour une exploration guidée.