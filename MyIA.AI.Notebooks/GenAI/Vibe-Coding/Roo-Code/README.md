# Démos Roo - Mini-ateliers guidés

Bienvenue dans le répertoire des mini-ateliers (`demos`) pour le framework Roo. Ces démos sont conçues pour vous guider à travers les fonctionnalités de base de Roo et vous aider à démarrer rapidement.

---

### Gestion des environnements de travail (Workspaces)

Pour une expérience d'apprentissage optimale, nous utilisons un système de workspaces personnalisés. Chaque participant doit créer son propre environnement de travail.

#### 1. Préparer votre environnement

Pour créer votre environnement personnel, ouvrez un terminal PowerShell à la racine du projet et exécutez le script suivant en remplaçant `"VotreNom"` par votre nom d'utilisateur ou un identifiant unique :

```powershell
./ateliers/demo-roo-code/prepare-workspaces.ps1 -UserName "VotreNom"
```

Ce script va créer un répertoire `workspaces/VotreNom` dans ce dossier, contenant une copie des ressources nécessaires pour chaque démo. Vous travaillerez directement dans ces répertoires personnalisés.

#### 2. Nettoyer votre environnement

Une fois que vous avez terminé vos démos, vous pouvez nettoyer votre environnement de travail :

*   **Pour supprimer uniquement votre workspace personnel :**

    ```powershell
    ./ateliers/demo-roo-code/clean-workspaces.ps1 -UserName "VotreNom"
    ```

*   **Pour supprimer tous les workspaces (utilisez avec précaution) :**

    ```powershell
    ./ateliers/demo-roo-code/clean-workspaces.ps1
    ```

    Cette commande demandera une confirmation avant de supprimer tous les répertoires d'utilisateurs sous `ateliers/demo-roo-code/workspaces`.

---

### Accéder aux Démos

Une fois votre environnement préparé, naviguez dans votre répertoire personnel (par exemple, `ateliers/demo-roo-code/workspaces/VotreNom`) et suivez les instructions spécifiques de chaque démo.

Pour un parcours d'apprentissage complet et des informations détaillées, veuillez consulter le document principal : [`docs/ROO-GUIDED-PATH.md`](docs/ROO-GUIDED-PATH.md)