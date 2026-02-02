# Guide de Démarrage Rapide

Ce guide vous explique comment installer, configurer et lancer l'application de matching CV sur votre machine locale.

## 1. Prérequis

-   **Python 3.9+**
-   **Git**
-   Un compte **OpenAI** avec une clé d'API valide (pour les algorithmes sémantiques).

## 2. Installation

1.  **Clonez le dépôt :**
    ```bash
    git clone <URL_DU_DEPOT>
    cd solution-matching-cv
    ```

2.  **Créez un environnement virtuel :**

    ⚠️ **Important :** Si votre projet se trouve dans un dossier synchronisé par un service cloud (comme Google Drive, OneDrive, etc.), vous **devez** créer l'environnement virtuel en dehors de ce dossier pour éviter des problèmes de performance et de synchronisation.

    *Exemple pour Windows (dans un dossier temporaire) :*
    ```powershell
    python -m venv C:\Temp\solution-matching-cv-venv
    ```

    *Exemple pour macOS/Linux (dans votre dossier personnel) :*
    ```bash
    python3 -m venv ~/venvs/solution-matching-cv-venv
    ```

3.  **Activez l'environnement virtuel :**
    -   *Windows (en utilisant l'exemple ci-dessus) :*
        ```powershell
        C:\Temp\solution-matching-cv-venv\Scripts\activate
        ```
    -   *macOS/Linux (en utilisant l'exemple ci-dessus) :*
        ```bash
        source ~/venvs/solution-matching-cv-venv/bin/activate
        ```
    *Note : L'activation n'est nécessaire que si vous souhaitez utiliser des commandes comme `pytest` directement. Les scripts d'exécution n'en ont pas besoin.*

## 3. Configuration

1.  **Créez le fichier `.env` :**
    Copiez le fichier `.env.example` et renommez-le en `.env` à la racine du projet.

2.  **Configurez les variables d'environnement :**
    Ouvrez le fichier `.env` et remplissez les variables suivantes :

    ```dotenv
    # Clé d'API et organisation OpenAI
    OPENAI_API_KEY="sk-..."
    OPENAI_ORG_ID="org-..."

    # Chemin ABSOLU vers l'exécutable Python de votre environnement virtuel
    # C'est essentiel pour que les scripts de lancement fonctionnent.
    # Exemple Windows: VENV_PYTHON_PATH="C:\Temp\solution-matching-cv-venv\Scripts\python.exe"
    # Exemple macOS/Linux: VENV_PYTHON_PATH="/home/user/venvs/solution-matching-cv-venv/bin/python"
    VENV_PYTHON_PATH="CHEMIN_ABSOLU_VERS_VOTRE_VENV_PYTHON"
    ```
    -   Remplacez `sk-...` et `org-...` par vos propres informations d'identification OpenAI.
    -   **Très important :** Remplacez le chemin d'exemple de `VENV_PYTHON_PATH` par le chemin complet vers l'exécutable `python` de l'environnement que vous venez de créer.

## 4. Installation des Dépendances

Une fois votre fichier `.env` configuré, utilisez le script approprié pour installer toutes les dépendances requises.

-   *Windows :*
    ```powershell
    ./scripts/install_deps.ps1
    ```
-   *macOS/Linux :*
    ```bash
    ./scripts/install_deps.sh
    ```

## 5. Lancement de l'Application

-   *Windows :*
    ```powershell
    ./scripts/run_app.ps1
    ```
-   *macOS/Linux :*
    ```bash
    ./scripts/run_app.sh
    ```

Ouvrez votre navigateur et accédez à l'adresse `http://127.0.0.1:5000`.

## 6. Lancement des Tests

Pour plus de détails sur la stratégie de test, consultez le [guide des tests](TESTING.md).

-   *Windows :*
    ```powershell
    # Tests unitaires
    ./scripts/run_unit_tests.ps1

    # Tests End-to-End
    ./scripts/run_e2e_tests.ps1
    ```
-   *macOS/Linux :*
    ```bash
    # Tests unitaires
    ./scripts/run_unit_tests.sh

    # Tests End-to-End
    ./scripts/run_e2e_tests.sh