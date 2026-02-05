# Guide d'Installation Simplifié de Roo

Ce guide vous explique comment installer l'environnement Roo de base pour la formation.

## Prérequis

- **Visual Studio Code** : Si vous ne l'avez pas, téléchargez-le depuis [le site officiel](https://code.visualstudio.com/).
- Une **connexion internet**.

## Étape 1 : Installer les extensions utiles

Avant d'installer Roo, nous allons installer quelques extensions qui amélioreront votre expérience de formation.

1.  Ouvrez **Visual Studio Code**.
2.  Accédez au panneau des **Extensions** sur la barre latérale gauche (icône carrée ou `Ctrl+Shift+X`).

### Extension Markdown Viewer
3.  Dans la barre de recherche, tapez `Markdown All in One`.
4.  Trouvez l'extension **Markdown All in One** de Yu Zhang et cliquez sur **Installer**.
5.  Cette extension vous permettra de visualiser et d'éditer plus facilement les fichiers README et guides de formation.

### Extension Peacock
6.  Dans la barre de recherche, tapez `Peacock`.
7.  Trouvez l'extension **Peacock** de John Papa et cliquez sur **Installer**.
8.  Cette extension vous permettra de coloriser VS Code pour différencier vos espaces de travail.
9.  Une fois installée, vous pouvez changer la couleur en ouvrant la palette de commandes (`Ctrl+Shift+P`) et en tapant `Peacock: Change Color`.

## Étape 2 : Installer l'extension Roo

1.  Dans la barre de recherche des extensions (toujours ouverte depuis l'étape précédente), tapez `Roo`.
2.  Trouvez l'extension officielle **Roo** et cliquez sur le bouton **Installer**.
3.  Une fois l'installation terminée, redémarrez Visual Studio Code si vous y êtes invité.



## Étape 3 : Configurer le fournisseur de modèles (OpenRouter)

Pour utiliser des modèles d'IA variés, nous allons configurer Roo pour utiliser OpenRouter, un service qui donne accès à de nombreux modèles via une seule clé API.

1.  Au lancement de Roo, sélectionnez le fournisseur Openrouter, ou après installation allez dans le premier onglet des paramètres **Roo › Paramètres: Fournisseurs**
3.  Dans Fournisseur d'API sélectionnez `OpenRouter` dans le menu déroulant.
4.  Juste en dessous, dans le champ **Clé API OpenRouter**, collez la clé qui vous sera fournie. :


## Étape 4 : Passer l'interface français

1. Ouvrez le menu des paramètres Roo en identifiant en haut l'icône ⚙️ correspondante
2. Repérez les différents sous-menus sur la gauche, et le menu Langue
3. Passez en français et enregistrez

## Étape 5 : Définir les profils de modèles

Les profils vous permettent de basculer rapidement entre différents modèles d'IA. Nous allons les ajouter manuellement via l'interface.

1.  Dans les paramètres fournisseurs de Roo, identifiez la liste déroulante "Profil de configuration".
2.  Le profil `default` est déjà présent. Il doit être défini à `anthropic/claude-sonnet-4`.
3.  Cliquez sur le bouton **+** pour ajouter un nouveau profil.
4.   Entrez les valeurs:
    *   **Nom du profil** : `Google-Gemini-2.5-Flash`
    *   **Fournisseur d'API** : `OpenRouter`
    *   **Value** : `google/gemini-2.5-flash`
5.  Cliquez sur **Enregistrer**.
6.  Répétez l'opération pour tous les modèles souhaités, par exemple :

| Nom du Profil (Key)         | Identifiant du Modèle (Value)            |
| --------------------------- | ---------------------------------------- |
| `Google-Gemini-2.5-Pro`     | `google/gemini-1.5-pro`                  |
| `Google-Gemini-2.5-Flash`     | `google/gemini-1.5-flash`                  |
| `Google-gemma-3-27b-it`     | `google/gemma-3-27b-it`                  |
| `OpenAI-gpt-4o-mini`        | `openai/gpt-4o-mini`                     |
| `OpenAI-gpt-4o`             | `openai/gpt-4o`                          |
| `OpenAI-o3-mini`                 | `openai/o3-mini`                   |
| `OpenAI-o3`                 | `openai/o3`                   |
| `Deepseek-Deepseek-r1`       | `deepseek/deepseek-r1`                 |
| `Qwen-Qwen-3-235b-a22b`      | `qwen/Qwen-3-235b-a22b`               |
| `Qwen-Qwen-3-32B`            | `qwen/Qwen-3-32b`                |
| `Qwen3-Coder-Next`           | `qwen/qwen3-coder-next`                 |
| `GLM-4.7`                    | `z-ai/glm-4.7`                           |
| `GLM-4.7-Flash`              | `z-ai/glm-4.7-flash`                     |
| `Mistral-Mistral-Small`    | `mistralai/mistral-small`         |

*Note : Certains noms de modèles demandés ont été adaptés aux identifiants disponibles sur OpenRouter.*

## Étape 6 : Configuration des autorisations

Pour une expérience plus fluide durant la formation, nous allons configurer Roo pour qu'il bénéficie d'un certain nombre d'autorisations par défaut, et nous attribuerons les autres au fil de l'eau.

1.  Dans les paramètres de Roo, cherchez la section **Roo › Paramètres: Auto-approbation**.
2.  Activez la case à cocher Auto-approbation activée au besoin.
3.  cliquez sur Lecture, Ecriture, Navigaeur, Réessayer, MCP, Mode, SOus-tâches, Exécuter et Todo


## Étape 7 : Configuration de la condensation de contexte

La condensation de contexte aide à gérer la mémoire lors de longues conversations. Nous allons l'activer et la configurer.

1.  Dans les paramètres de Roo, trouvez la section **Roo › Paramètres › Contexte**.
2.  A la fin de l'onglet, Cochez la case "Déclencher autoamtiquement la condensation intelligente de contexte"
3.  Juste en dessous, dans **Seuil de condensation du contexte**, vérifiez que le curseur autour de `50%` par défaut.
4.  Pour les modèles avec une très grande fenêtre de contexte (1M de tokens ou plus), il est pour l'instant recommandé de réduire ce niveau. Par exemple, dans la liste déroulante sélectionnez
    *   **Key**: `Google-Gemini-2.5-Flash` (ou tout autre modèle à 1M+)
    *   **Value**: `25%`



## Étape 8 : Configuration des MCPs (Model Context Protocol)

Les MCPs étendent les capacités de Roo. Voici la configuration recommandée :

1.  Allez dans l'onglet **Roo › Marché** du panneau Roo.
2.  Configurez le MCP `searxng` à partir du marketplace Roo (https://github.com/ihor-sokoliuk/mcp-searxng) :
    *   Si vous utilisez une instance privée, vous pouvez ajouter la variable d'environnement dans les paramètres de `searxng` : `"env": { "SEARXNG_URL": "https://search.myia.io/" }`.
3.  Optionnel: Installez le MCP `markitdown` :
    *   Ce MCP permet de convertir des documents ou des pages en Markdown. Il est disponible sur [GitHub](https://github.com/microsoft/markitdown/tree/main/packages/markitdown-mcp).
    *   Comme il n'est pas disponible dans le marketplace, Vous pouvez demander à Roo de l'installer pour vous en utilisant une instruction comme : "Installe le MCP markitdown en suivant les instructions disponibles dans la page https://github.com/microsoft/markitdown/tree/main/packages/markitdown-mcp". Fournissez lui au besoin le chemin du fichier de configuraiton global des MCPs roo, que vous pouvez ouvrir dans l'éditeur depuis le menu **Roo › Serveurs MCP** (caché derrière l'icone **...**)

## Étape 9 : Explorer l'environnement de démonstration

Le répertoire `demo-roo-code`, qui a été fourni pour cette formation, contient tous les exercices.

1.  **Préparer les exercices** :
    Avant de commencer, vous devez préparer les espaces de travail des démos. Ouvrez un terminal dans VS Code (`Terminal` > `Nouveau terminal`) et exécutez le script suivant :

    ```powershell
    # Pour les utilisateurs Windows
    .\ateliers\demo-roo-code\prepare-workspaces.ps1
    ```
    Ce script copiera les fichiers nécessaires dans chaque dossier d'exercice (`workspace`).

2.  **Lancer un exercice** :
    -   Utilisez l'explorateur de fichiers de VS Code pour naviguer dans le répertoire `demo-roo-code`.
    -   Choisissez un thème (par exemple, `01-decouverte`) puis une démo (par exemple, `demo-1-conversation`).
    -   Chaque dossier de démo contient un fichier `README.md` avec les instructions spécifiques à suivre pour l'exercice.

Vous êtes maintenant prêt à commencer la formation avec Roo !


## Étape 10 : Installation des extensions-roo

Forker le dépôt https://github.com/jsboige/roo-extensions
Le faire cartographier par un agent roo, initialiser les sous-modules, compiler et installer les MCPs.
Faire instruire une tâche pour valider le fonctionnement des différents outils des MCPs.

## Étape 11 : Configurer les Custom Instructions

Les Custom Instructions permettent de personnaliser le comportement de Roo selon vos projets et preferences.

### Configuration rapide projet

1. Creez le repertoire de rules a la racine de votre projet :

```bash
mkdir -p .roo/rules
```

2. Ajoutez vos conventions dans un fichier Markdown :

```bash
echo "# Conventions du projet" > .roo/rules/01-conventions.md
echo "- Repondre en francais" >> .roo/rules/01-conventions.md
echo "- Utiliser TypeScript strict" >> .roo/rules/01-conventions.md
```

### Configuration globale (tous projets)

Pour des instructions appliquees a tous vos projets :

**Windows (PowerShell) :**
```powershell
New-Item -ItemType Directory -Force -Path "$env:USERPROFILE\.roo\rules"
"Toujours repondre en francais" | Out-File "$env:USERPROFILE\.roo\rules\01-langue.md"
```

**macOS/Linux :**
```bash
mkdir -p ~/.roo/rules
echo "Toujours repondre en francais" > ~/.roo/rules/01-langue.md
```

### Hierarchie de priorite

| Source | Emplacement | Priorite |
|--------|-------------|----------|
| Global | `~/.roo/rules/` | Basse |
| Projet | `.roo/rules/` | Haute |
| Mode-specific | `.roo/rules-{mode}/` | Tres haute |

**Guide complet :** [CUSTOM-INSTRUCTIONS-ROO.md](./CUSTOM-INSTRUCTIONS-ROO.md)

