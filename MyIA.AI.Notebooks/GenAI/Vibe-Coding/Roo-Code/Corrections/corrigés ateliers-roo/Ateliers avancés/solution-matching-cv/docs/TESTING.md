# Guide des Tests

Ce document décrit la stratégie de test mise en place pour garantir la qualité, la fiabilité et la non-régression de l'application de matching CV.

## 1. Philosophie de Test

La testabilité a été un facteur clé dans les choix d'architecture (voir [HISTORY.md](HISTORY.md)). Le projet adopte une approche de test à plusieurs niveaux pour couvrir différents aspects de l'application.

## 2. Types de Tests

### 2.1. Tests Unitaires

-   **Objectif :** Valider chaque composant ou fonction de manière isolée.
-   **Localisation :** `tests/unit/`
-   **Description :** Ces tests se concentrent sur la logique métier des algorithmes de matching. Ils utilisent des données "mock" (des DataFrames Pandas créés en mémoire) pour vérifier que chaque algorithme produit les résultats attendus dans des conditions contrôlées.
-   **Exemple :** `test_simple_matching.py` vérifie que l'algorithme simple compte correctement les compétences communes.

### 2.2. Tests de Bout en Bout (End-to-End)

-   **Objectif :** Simuler une interaction utilisateur complète pour valider l'intégration de tous les composants, de l'interface web au backend.
-   **Localisation :** `tests/e2e/`
-   **Technologie :** **Playwright** (via `pytest-playwright`).
-   **Description :** Ces tests lancent l'application Flask, ouvrent un navigateur, interagissent avec l'interface (choix d'un algorithme, clic sur le bouton "Lancer le Matching") et vérifient que les résultats attendus sont correctement affichés sur la page.
-   **Exemple :** `test_app_e2e.py` simule le parcours complet pour chaque algorithme.

### 2.3. Tests de Performance

-   **Objectif :** Valider quantitativement l'efficacité des optimisations, notamment le mécanisme de cache.
-   **Localisation :** `tests/performance/`
-   **Description :** Ces tests mesurent et comparent les temps d'exécution de certaines opérations critiques.
-   **Exemple :** `test_cache_performance.py` mesure le gain de temps obtenu grâce au cache ChromaDB en comparant une indexation "à froid" (base de données vide) et "à chaud" (base de données pré-remplie).

## 3. Comment Lancer les Tests

Assurez-vous d'avoir suivi le [guide de démarrage](GETTING_STARTED.md) et configuré correctement votre environnement et votre fichier `.env`.

### 3.1. Méthode Recommandée : Scripts d'Exécution

La manière la plus simple et la plus fiable de lancer les tests est d'utiliser les scripts fournis dans le dossier `/scripts`. Ils s'occupent de configurer l'environnement pour vous.

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
    *Note : Ce script générera un rapport `test_report.html` dans le dossier `/docs`.*

### 3.2. Méthode Avancée : Commandes `pytest` directes

Pour des besoins de débogage plus spécifiques, vous pouvez toujours utiliser `pytest` directement. Assurez-vous que votre environnement virtuel est activé.

-   **Lancer tous les tests :**
    ```bash
    pytest
    ```

-   **Lancer un fichier de test spécifique :**
    ```bash
    pytest tests/unit/test_simple_matching.py
    ```

-   **Voir les logs en direct (`print`) :**
    Par défaut, `pytest` capture les sorties. Pour les afficher, utilisez l'option `-s`.
    ```bash
    pytest -s