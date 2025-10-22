# Scripts d'Automatisation pour l'Authentification GenAI

## Contexte

Ce répertoire contient un ensemble de scripts PowerShell et Bash recréés suite à l'incident `git clean -fd` du 2025-10-22. Ces scripts permettent d'installer, configurer, tester, déployer et annuler le déploiement d'une solution d'authentification basée sur le custom node [ComfyUI-Login](https://github.com/11cafe/ComfyUI-Login) pour les services GenAI.

La recréation de ces scripts est basée sur les informations récupérées dans le rapport de mission SDDD : `recovery/07-RAPPORT-MISSION-SDDD-AUTHENTIFICATION-GENAI.md`.

## Prérequis Globaux

- **Docker**: Docker Desktop doit être installé et en cours d'exécution.
- **PowerShell**: Pour les scripts `.ps1`, PowerShell 7+ est recommandé.
- **Git Bash**: Pour les scripts `.sh`, un environnement Bash comme Git Bash est nécessaire sous Windows.
- **Permissions**: L'utilisateur doit avoir les droits pour exécuter des commandes Docker.
- **Module Bcrypt**: Le script `generate-bearer-tokens.ps1` nécessite le module PowerShell `Bcrypt`. Il tentera de l'installer automatiquement, mais si cela échoue, exécutez :
  ```powershell
  Install-Module -Name Bcrypt -Scope CurrentUser -Repository PSGallery -Force
  ```

## Ordre d'Exécution des Scripts

Les scripts sont conçus pour être exécutés dans un ordre précis pour un déploiement complet.

1.  **`install-comfyui-login.sh`**: Installe le custom node dans les conteneurs Docker.
2.  **`configure-comfyui-auth.ps1`**: Prépare les fichiers de configuration `.env` pour activer l'authentification.
3.  **`generate-bearer-tokens.ps1`**: Crée les comptes utilisateurs et les mots de passe/tokens.
4.  **`deploy-auth-solution.ps1`**: Orchestre le redémarrage des services avec la nouvelle configuration.
5.  **`extract-bearer-tokens.ps1`**: (Optionnel, si la génération manuelle échoue) Extrait les tokens depuis les logs après le premier démarrage.
6.  **`test-comfyui-auth.ps1`**: Valide que la solution d'authentification est fonctionnelle.
7.  **`rollback-auth-solution.ps1`**: (En cas de problème) Annule le déploiement et restaure la configuration précédente.

---

## Description Détaillée des Scripts

### 1. `install-comfyui-login.sh`

-   **Objectif**: Installer le custom node ComfyUI-Login.
-   **Usage**:
    ```bash
    ./install-comfyui-login.sh <container_name_1> [container_name_2] ...
    ```
-   **Exemple**:
    ```bash
    ./install-comfyui-login.sh comfyui-qwen comfyui-forge
    ```

### 2. `configure-comfyui-auth.ps1`

-   **Objectif**: Créer/mettre à jour les fichiers `.env` pour activer l'authentification.
-   **Usage**:
    ```powershell
    ./configure-comfyui-auth.ps1 -ServiceName <nom_du_service>
    ```
-   **Exemple**:
    ```powershell
    ./configure-comfyui-auth.ps1 -ServiceName "comfyui-qwen"
    ```

### 3. `generate-bearer-tokens.ps1`

-   **Objectif**: Générer des comptes utilisateurs et des mots de passe sécurisés.
-   **Usage**:
    ```powershell
    ./generate-bearer-tokens.ps1 -Usernames <user1>,<user2> -OutputPath <chemin_vers_tokens>
    ```
-   **Exemple**:
    ```powershell
    # Crée les fichiers .token et un .env.generated dans le répertoire spécifié
    ./generate-bearer-tokens.ps1 -Usernames "qwen-api-user", "forge-api-user" -OutputPath "./docker-configurations/comfyui-qwen/custom_nodes/ComfyUI-Login"
    ```
    **Important**: Le `OutputPath` doit pointer vers le répertoire où ComfyUI-Login s'attend à trouver les fichiers `.token` à l'intérieur du conteneur.

### 4. `extract-bearer-tokens.ps1`

-   **Objectif**: Extraire un token depuis les logs Docker après la première connexion.
-   **Usage**:
    ```powershell
    ./extract-bearer-tokens.ps1 -ContainerName <nom_conteneur> -EnvVarName <nom_variable_env>
    ```
-   **Exemple**:
    ```powershell
    ./extract-bearer-tokens.ps1 -ContainerName "comfyui-qwen" -EnvVarName "QWEN_API_TOKEN"
    ```

### 5. `test-comfyui-auth.ps1`

-   **Objectif**: Valider la configuration de l'authentification.
-   **Usage**:
    ```powershell
    ./test-comfyui-auth.ps1 -ApiUrl <url_api> -ValidToken <token_valide>
    ```
-   **Exemple**:
    ```powershell
    $myToken = "votre_token_ici"
    ./test-comfyui-auth.ps1 -ApiUrl "http://localhost:8888/system_stats" -ValidToken $myToken
    ```

### 6. `deploy-auth-solution.ps1`

-   **Objectif**: Orchestrer le déploiement complet.
-   **Usage**:
    ```powershell
    ./deploy-auth-solution.ps1
    ```
-   **Note**: Ce script sauvegarde automatiquement la configuration avant de procéder.

### 7. `rollback-auth-solution.ps1`

-   **Objectif**: Annuler le déploiement en cas de problème.
-   **Usage**:
    ```powershell
    ./rollback-auth-solution.ps1 -BackupPath <chemin_vers_backup>
    ```
-   **Exemple**:
    ```powershell
    ./rollback-auth-solution.ps1 -BackupPath ".\.backups\deploy_20251022183000"
    ```

## Variables d'Environnement

Pour que les services Docker prennent en compte l'authentification, les variables suivantes doivent être définies dans les fichiers `.env` respectifs de chaque service (gérés par `configure-comfyui-auth.ps1`):

-   `COMFYUI_LOGIN_ENABLED=true`: Active le custom node.
-   `COMFYUI_ARGS=--enable-auth`: Modifie les arguments de démarrage de ComfyUI.

Les tokens eux-mêmes sont gérés par les fichiers `.token` lus par ComfyUI-Login et ne sont pas directement passés comme variables d'environnement au conteneur.