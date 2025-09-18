# Analyse de l'Architecture Roo pour la Gestion des MCPs

Ce document détaille l'architecture de l'extension Roo pour VS Code en ce qui concerne la gestion des serveurs MCP (Model Context Protocol), avec un focus sur les serveurs écrits en Python.

## 1. Architecture des Processus

L'architecture de gestion des MCPs dans Roo repose sur trois composants principaux :

- **`McpServerManager.ts`**: Il s'agit d'un **singleton** qui garantit qu'une seule instance du `McpHub` est active pour toute l'extension VS Code. Il gère le cycle de vie global du hub.

- **`McpHub.ts`**: C'est le **cœur orchestral** du système. Une instance unique de cette classe est responsable de :
    - Lire et fusionner les configurations MCP depuis le fichier global (`mcp_settings.json`) et le fichier de projet (`.roo/mcp.json`).
    - Gérer le cycle de vie de chaque serveur MCP : démarrage, arrêt et redémarrage.
    - Établir la communication (via `stdio`, `sse`, ou `streamable-http`) avec les processus serveur.
    - Capturer les logs (`stderr`) des serveurs.

- **`ClineProvider.ts`**: C'est la couche de communication entre la logique de l'extension (le "backend") et l'interface utilisateur (la webview). Elle interagit avec le `McpHub` pour afficher l'état des serveurs et transmettre les actions de l'utilisateur (ex: redémarrer un serveur).

## 2. Cycle de Vie d'un Serveur MCP Python (`stdio`)

Le cycle de vie d'un serveur configuré avec le transport `stdio` est le suivant :

1.  **Démarrage** :
    - La méthode `connectToServer` dans `McpHub.ts` est appelée.
    - Elle lit la configuration du serveur (`command`, `args`, `env`, etc.).
    - **Sous Windows**, la commande est systématiquement encapsulée dans `cmd.exe /c ...`. Ceci est fait pour assurer la compatibilité avec des exécutables qui ne sont pas des `.exe` (comme les scripts PowerShell ou les batchs utilisés par certains gestionnaires de versions de Node.js).
    - Un nouveau processus enfant est lancé en utilisant les informations de la configuration.
    - Le `McpHub` attache des "listeners" aux flux `stdout` et `stderr` du processus pour établir la communication et capturer les logs.

2.  **Redémarrage ("Hot Reload")** :
    - Le redémarrage n'est **pas** automatique par défaut. Il doit être explicitement activé en ajoutant une propriété `"watchPaths": ["/chemin/vers/votre/code"]` à la configuration du serveur dans `mcp_settings.json`.
    - Si `watchPaths` est configuré, la méthode `setupFileWatcher` utilise la bibliothèque `chokidar` pour surveiller les changements dans les chemins spécifiés.
    - Lorsqu'un changement est détecté, la méthode `restartConnection` est invoquée.
    - `restartConnection` appelle `deleteConnection` (qui tue le processus enfant) puis `connectToServer` (qui en relance un nouveau).

3.  **Problème du Cache Python (`.pyc`)** :
    - Le cycle de redémarrage de Roo **ne nettoie pas les fichiers de bytecode Python (`.pyc`)**.
    - Si Python, lors du redémarrage, estime qu'un fichier `.pyc` existant est encore valide (ce qui peut arriver en cas de désynchronisation de l'horloge ou d'autres facteurs), il le chargera au lieu de recompiler le fichier `.py` modifié.
    - **C'est une cause très probable du problème de "code non mis à jour"**.

## 3. Configuration et Logs

- **Configuration** :
    - Le système utilise une configuration hiérarchique : les serveurs définis dans le fichier `.roo/mcp.json` du projet surchargent ceux définis dans le fichier global `mcp_settings.json`.
    - La configuration permet de définir des variables d'environnement (`env`), y compris le `PYTHONPATH`, qui influence directement la manière dont Python importe les modules.

- **Logs** :
    - Les logs sont exclusivement capturés depuis le flux `stderr` du processus MCP.
    - La méthode `connectToServer` dans `McpHub.ts` attache un listener à `stderr`.
    - Toute sortie sur `stderr` est stockée dans la propriété `errorHistory` de l'objet serveur, avec un timestamp.
    - Il n'existe pas de mécanisme simple pour visualiser ces logs depuis l'interface, ni de fichier de log centralisé dédié aux MCPs. Le `console.error` de l'extension VS Code reste le principal canal de débogage.


## 4. Stratégie de Diagnostic et Recommandations

Basé sur cette analyse, voici une procédure fiable pour le développement itératif de MCPs Python et des recommandations pour améliorer l'écosystème Roo.

### Procédure Fiable de Redémarrage pour MCPs Python

Pour garantir que les modifications du code Python sont toujours prises en compte, la procédure suivante doit être suivie :

1.  **Activer le Rechargement Automatique (Hot-Reload)** :
    Modifiez votre fichier `mcp_settings.json` pour inclure la propriété `watchPaths` dans la configuration de votre serveur. Le chemin doit pointer vers le répertoire racine de votre code MCP.

    **Exemple pour `jupyter-papermill-mcp-server`** :
    ```json
    "jupyter-papermill-mcp-server": {
      "command": "C:/Users/jsboi/.conda/envs/mcp-jupyter/python.exe",
      "args": [ "-m", "papermill_mcp.main_fastmcp" ],
      "env": { "PYTHONPATH": "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server" },
      "watchPaths": [ "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server/papermill_mcp" ],
      ...
    }
    ```
    Avec cette configuration, Roo redémarrera automatiquement le serveur à chaque modification d'un fichier Python dans le répertoire `papermill_mcp`.

2.  **Forcer le Nettoyage du Cache `.pyc`** :
    Pour contrer le problème de cache, la meilleure solution est de modifier la commande de démarrage pour qu'elle nettoie les fichiers `.pyc` avant de lancer le serveur. Étant donné que Roo sur Windows utilise `cmd.exe`, nous pouvons chaîner les commandes.

    La solution la plus propre est de créer un **script de lancement**.

    **a. Créez `start_jupyter_mcp.bat`** dans `D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server`:
    ```batch
    @echo off
    echo Cleaning Python cache...
    del /s /q __pycache__
    echo Starting MCP server...
    C:/Users/jsboi/.conda/envs/mcp-jupyter/python.exe -m papermill_mcp.main_fastmcp
    ```

    **b. Mettez à jour `mcp_settings.json`** pour utiliser ce script :
    ```json
    "jupyter-papermill-mcp-server": {
      "command": "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server/start_jupyter_mcp.bat",
      "args": [],
      "watchPaths": [ "D:/dev/roo-extensions/mcps/internal/servers/jupyter-papermill-mcp-server/papermill_mcp" ],
      ...
    }
    ```
    *Note : `env` avec `PYTHONPATH` peut ne plus être nécessaire si le script est lancé depuis le bon répertoire de travail (`cwd`), mais il est plus sûr de le conserver.*

### Recommandations pour `roo-state-manager`

L'expérience de diagnostic a montré des limitations dans les outils actuels. Voici des recommandations pour améliorer `roo-state-manager` :

1.  **Créer un outil `get_mcp_server_state`** :
    Cet outil permettrait d'inspecter l'état interne d'un ou de tous les serveurs MCP gérés par le `McpHub`.
    - **Arguments** : `server_name` (optionnel).
    - **Retour** : Un objet JSON contenant des informations pour chaque serveur :
        - `status` ('connected', 'disconnected', 'connecting')
        - `config` (la configuration appliquée)
        - `tools` (la liste des outils détectés)
        - `errorHistory` (les 10-20 derniers logs `stderr` avec timestamps).
    Cet outil aurait rendu le diagnostic des logs beaucoup plus direct.

2.  **Améliorer `rebuild_and_restart_mcp`** :
    - L'outil devrait détecter le type de projet MCP (ex: `package.json` vs `requirements.txt`/`pyproject.toml`).
    - Il devrait accepter un paramètre `project_path` pour savoir où exécuter la commande de build, au lieu de l'exécuter systématiquement dans le répertoire de travail courant.
    - Pour les projets Python, il pourrait automatiquement effectuer le nettoyage des `.pyc` avant de redémarrer.
