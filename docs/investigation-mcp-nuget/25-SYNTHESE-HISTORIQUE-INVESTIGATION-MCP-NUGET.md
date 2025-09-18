# Synthèse de l'Historique d'Investigation MCP-NuGet

Ce document retrace l'historique des tâches liées à la résolution du problème d'exécution des notebooks .NET Interactive avec des paquets NuGet via le MCP Jupyter.

## 1. Tâche `1d93baa9...`: Audit et Réparation de l'Environnement Jupyter Local (Point de Départ)

- **Objectif :** Réparer un environnement de développement local complètement cassé en urgence pour une formation.
- **Actions Clés :**
    - Création des scripts `audit_environment.ps1` et `setup_environment.ps1` pour un diagnostic et une réparation systématiques.
    - Identification et résolution de problèmes fondamentaux : `pip` non présent dans le `PATH`, source NuGet manquante pour `dotnet`, répertoires Jupyter inexistants.
- **Décision Critique :** Cette mission de réparation a mis en lumière l'instabilité de l'ancien serveur MCP Jupyter (Node.js) et a conduit à la décision de le **réécrire entièrement en Python en utilisant Papermill**.
- **Piste pour l'investigation actuelle :** Les correctifs appliqués (source NuGet, etc.) concernaient l'environnement de l'utilisateur. Il est essentiel de s'assurer que ces mêmes configurations sont présentes dans l'environnement d'exécution isolé du serveur MCP.


## 2. Tâche `e7106696...`: Naissance et Débogage du Serveur Python

- **Objectif :** Implémenter le nouveau serveur MCP Python pour remplacer l'ancienne version Node.js.
- **Parcours du Combattant :** La tâche a été une longue et difficile série de débogages pour faire fonctionner l'exécution de base.
    - **Problème `PYTHONPATH` :** Une lutte acharnée pour que l'interpréteur Python du MCP trouve à la fois le SDK `mcp` et le code source du serveur lui-même.
    - **Solution de Contournement :** La solution a été de *hardcoder* les chemins d'accès directement dans le `sys.path` au démarrage du script Python du serveur. C'est un indice crucial sur l'isolation de l'environnement d'exécution.
    - **Problèmes de dépendances :** Conflits entre `pydantic` et `pydantic-core`, et incompatibilités `asyncio`.
- **Angle Mort Critique :** Tous les efforts et validations de cette tâche monumentale se sont concentrés **uniquement sur l'exécution de notebooks Python**. Le cas d'usage `.NET/NuGet` n'a jamais été testé ou pris en compte dans l'architecture initiale. La fondation du serveur a été construite sur un périmètre purement Python.
- **Piste pour l'investigation actuelle :** Le hardcoding du `sys.path` prouve que des configurations essentielles ne sont pas héritées par l'environnement du MCP. Il est quasi certain que les variables d'environnement crues pour MSBuild et NuGet (`DOTNET_ROOT`, `MSBuildSDKsPath`, etc.) ne sont pas non plus transmises, ce qui cause l'erreur `path1 is null`.


## 3. Tâche `99615eac...`: La Validation "Réussie" du Serveur Python

- **Objectif :** Valider de manière exhaustive le nouveau serveur Python avant de l'adopter.
- **Déroulement :**
    - **Comparaison des API :** Une analyse a confirmé que le nouveau serveur couvrait 100% des outils de l'ancien, avec 47% de fonctionnalités en plus (grâce à Papermill).
    - **Problème de Version Python :** La validation a révélé une incompatibilité majeure : l'environnement conda existant (`mcp-jupyter`) utilisait Python 3.9, insuffisant pour le SDK `mcp`. Un nouvel environnement, `mcp-jupyter-py310`, a dû être créé.
    - **Tests approfondis (Python) :** Des tests fonctionnels, d'intégration Papermill et de performance ont été menés avec succès, mais **uniquement sur des notebooks Python**.
- **Angle Mort et Fausse Conclusion :**
    - Identique à la phase de développement, cette validation a **complètement ignoré le cas d'usage .NET/NuGet**. Tous les tests ont été effectués dans un contexte purement Python.
    - Le rapport final, bien que correct sur le périmètre testé, a conclu de manière trop optimiste que le serveur était "prêt pour la production", sans mentionner que la compatibilité avec une partie majeure de l'écosystème CoursIA (.NET) était inconnue.
- **Piste pour l'investigation actuelle :** La nécessité de créer un environnement conda dédié (`mcp-jupyter-py310`) est un autre indice de la complexité de la gestion de l'environnement. La configuration dans `mcp_settings.json` doit faire référence au bon environnement pour que les dépendances (et la version de Python) soient correctes.


## 4. Tâche `b27aaca6...`: Le Crash en Production - Crise `asyncio` et Refactorisation

- **Objectif :** Valider le nouveau serveur Python dans l'environnement de production Roo.
- **Le Choc avec la Réalité :** Dès son intégration dans Roo, le serveur a crashé.
    - **Cause Racine :** Un conflit fondamental de boucles `asyncio`. Le serveur, basé sur `FastMCP`, essayait de gérer sa propre boucle `asyncio`, alors que le processus hôte de Roo en avait déjà une en cours.
- **La Grande Refactorisation :**
    - Après de nombreuses tentatives de contournement infructueuses (`nest_asyncio`, modification du démarrage de `FastMCP`), la véritable cause est identifiée : **`FastMCP` est architecturalement incompatible** avec le mode d'hébergement de Roo.
    - **Décision :** Le serveur est complètement réécrit une seconde fois pour abandonner `FastMCP` et utiliser à la place le **SDK MCP Python standard**, qui est conçu pour ce scénario.
- **Second Cycle de Débogage :** La nouvelle version a également échoué, cette fois parce que le décorateur `@server.call_tool` était mal utilisé. La conversation s'est concentrée sur la correction syntaxique de tous les outils.
- **Angle Mort Maintenu :** Toute cette énergie a été consacrée à régler un problème d'infrastructure fondamental (`asyncio`). La question de l'exécution des notebooks, et en particulier des notebooks **.NET/NuGet**, est restée complètement en dehors du périmètre de cette tâche. Le problème d'environnement d'exécution (variables manquantes, etc.) est toujours latent sous ces problèmes architecturaux.


## 5. Tâche `1c951333...`: La Migration Administrative de la Configuration

- **Objectif :** Mettre à jour `mcp_settings.json` pour activer le nouveau serveur Python.
- **Déroulement :** Remplacement de l'entrée de l'ancien serveur Node.js par celle du nouveau serveur Python.
- **Découverte Technique Cruciale :** Pour que le serveur fonctionne, il a été nécessaire d'utiliser la clé `"env"` dans `mcp_settings.json` pour forcer la définition de la variable d'environnement `PYTHONPATH`.
- **Piste Fondamentale pour l'investigation actuelle :** Cette étape **prouve** que l'environnement d'exécution du MCP est isolé et n'hérite pas des variables système par défaut. Le mécanisme `"env"` est donc la piste la plus prometteuse et la plus directe pour injecter les variables requises par .NET et MSBuild (`DOTNET_ROOT`, `MSBuildSDKsPath`, etc.) et résoudre l'erreur `path1 is null`. Le fait que son utilisation ait été limitée à `PYTHONPATH` est au cœur du problème.


## 6. Tâche `75253714...`: Diagnostic de la Crise et Stratégie de Récupération

- **Contexte :** Double échec post-migration. Le serveur Python crashait (conflit `asyncio`) et le rollback vers le serveur Node.js a échoué (problème de `PATH`). **Résultat : 0 serveur fonctionnel**.
- **Diagnostic des Causes Racines :**
    1.  **Serveur Python :** Conflit `asyncio` confirmé. L'environnement `mcp-jupyter-py310` a été identifié comme "dégradé" (des paquets Jupyter essentiels manquaient).
    2.  **Serveur Node.js :**`jupyter` n'était pas dans le `PATH` système global, rendant le serveur inopérant.
- **Stratégie de Récupération :** La décision a été de se concentrer sur l'environnement conda `mcp-jupyter` (Python 3.9), qui était le seul stable et complet, et de l'utiliser comme base pour faire fonctionner le nouveau serveur Python.
- **Piste pour l'investigation actuelle :** La gestion des environnements conda s'est avérée complexe et a mené à des états incohérents. L'objectif étant de restaurer une fonctionnalité de base (pour Python), la question de l'environnement nécessaire pour .NET (variables, SDK, etc.) est restée un angle mort complet.


## 7. Tâche `2090c76a...`: Le Rollback Précipité et l'Effet Domino

- **Contexte :** Réaction immédiate à la crise `asyncio` du serveur Python.
- **Objectif :** Restaurer le service en urgence en revenant à l'ancien serveur Node.js.
- **Déroulement :** Le fichier `mcp_settings.json` a été modifié pour réactiver la configuration du serveur Node.js.
- **Le Double Échec :** Le rollback a lui-même échoué. Le serveur Node.js n'a pas pu démarrer car, comme diagnostiqué plus tard, il dépendait d'une commande `jupyter` présente dans le `PATH` système, qui n'était pas configuré. Cet échec a transformé une panne en une crise de "double échec".
- **Piste pour l'investigation actuelle :** Cette étape illustre parfaitement la fragilité des solutions qui dépendent de la configuration de l'environnement global de la machine. Cela renforce l'idée qu'une solution robuste pour .NET doit injecter son environnement de manière explicite et contrôlée via la configuration du MCP, plutôt que de compter sur un héritage implicite.


## 8. Tâche `54b74fdb...`: Le Moment "Eurêka" - Validation sur Notebooks Réels et Succès Partiel

- **Contexte :** Première validation du serveur Python contre les notebooks du projet CoursIA.
- **Le Premier Contact Douloureux avec NuGet :**
    - Les tests sur des notebooks .NET ont immédiatement échoué avec l'erreur `Value cannot be null. (Parameter 'path1')`.
    - Un test sur un vrai notebook Python a fonctionné parfaitement, prouvant que le problème était spécifique à .NET.
- **La Découverte Fondamentale - L'Isolation d'Environnement :**
    - Un test crucial a été effectué : exécuter `papermill` sur un notebook .NET **directement en ligne de commande** (`conda run ...`). **Et cela a fonctionné !**
    - **Conclusion :** Le problème ne venait pas de Papermill ou de .NET, mais de la **manière dont le serveur MCP invoquait Papermill**. L'appel via `subprocess` hérite d'un environnement plus complet que l'import direct dans le processus Python du serveur.
- **La Solution "Subprocess Isolation" et le Succès Partiel :**
    - Le code du serveur a été modifié pour appeler Papermill via `subprocess.run(["conda", "run", ...])`.
    - **PREMIER SUCCÈS .NET VIA MCP :** Avec cette modification, un notebook .NET simple (`Sudoku`) a été exécuté avec succès via le MCP. **L'utilisateur avait raison, un succès a bien eu lieu.**
- **L'Échec Persistant et la Piste Actuelle :**
    - Malgré ce succès, un notebook .NET plus complexe (`ML-1-Introduction`) continuait d'échouer avec la même erreur.
    - **Piste :** La solution `subprocess` est la bonne direction, mais l'environnement hérité par le sous-processus est encore incomplet. Il lui manque probablement des variables d'environnement spécifiques requises par les paquets NuGet plus complexes de ML.NET. L'étape suivante doit être d'enrichir l'environnement de ce `subprocess` en utilisant le mécanisme `"env"` de `mcp_settings.json`.
