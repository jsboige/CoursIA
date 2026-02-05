# Parcours d'Apprentissage Guidé de Roo

Ce document présente un parcours d'apprentissage progressif pour prendre en main Roo, votre assistant IA intégré à VS Code. Chaque étape est une démonstration pratique conçue pour vous familiariser avec une fonctionnalité clé de Roo.

## Avant de commencer : Préparer votre environnement de travail

Pour commencer les démos, vous devez préparer votre environnement de travail. Chaque participant aura son propre espace de travail personnalisé, centralisé pour toutes les démos.

1.  **Ouvrez un terminal PowerShell** à la racine du projet.
2.  **Exécutez le script de préparation** en spécifiant votre nom d'utilisateur (ou un identifiant unique) :

    ```powershell
    ./ateliers/demo-roo-code/prepare-workspaces.ps1 -UserName "VotreNom"
    ```
    Remplacez `"VotreNom"` par le nom que vous souhaitez utiliser. Ce script va créer :
    *   Votre répertoire de travail principal : `ateliers/demo-roo-code/workspaces/VotreNom`
    *   À l'intérieur de ce répertoire, une copie personnalisée des ressources pour chaque démo.

    Vous travaillerez exclusivement dans ces répertoires personnalisés.

### Nettoyage de votre environnement de travail

Pour nettoyer votre environnement de travail après avoir terminé les démos :

*   **Pour supprimer votre workspace personnel uniquement :**

    ```powershell
    ./ateliers/demo-roo-code/clean-workspaces.ps1 -UserName "VotreNom"
    ```
    Remplacez `"VotreNom"` par le nom que vous avez utilisé lors de la préparation.

*   **Pour supprimer tous les workspaces (utilisation réservée aux formateurs ou avec précaution) :**

    ```powershell
    ./ateliers/demo-roo-code/clean-workspaces.ps1
    ```
    Cette commande vous demandera une confirmation avant de supprimer tous les répertoires d'utilisateurs sous `ateliers/demo-roo-code/workspaces`.

## Thème 1 : Découverte de Roo

### Étape 1 : Dialoguer avec Roo (10 min)

Votre premier contact avec Roo. Apprenez à converser, à poser des questions et à utiliser le contexte des fichiers ouverts.

*   **Dossier de la démo :** `ateliers/demo-roo-code/01-decouverte/demo-1-conversation/`
*   **Objectif :** Maîtriser les interactions fondamentales.

### Étape 2 : Analyse d'images avec Roo (15 min)

Découvrez comment Roo peut "voir" et analyser des images pour en extraire des informations.

*   **Dossier de la démo :** `ateliers/demo-roo-code/01-decouverte/demo-2-vision/`
*   **Objectif :** Comprendre les capacités multimodales de Roo.

## Thème 2 : Orchestration de Tâches

### Étape 3 : Organiser vos idées (15 min)

Découvrez comment Roo peut vous aider à structurer un projet ou une tâche complexe en créant un plan d'action détaillé.

*   **Dossier de la démo :** `ateliers/demo-roo-code/02-orchestration-taches/demo-1-planification/`
*   **Objectif :** Apprendre à utiliser le mode `Architect` pour planifier.

### Étape 4 : Recherche et synthèse (20 min)

Apprenez à utiliser Roo pour rechercher des informations sur le web et en faire une synthèse structurée.

*   **Dossier de la démo :** `ateliers/demo-roo-code/02-orchestration-taches/demo-2-recherche/`
*   **Objectif :** Utiliser les outils de recherche et de synthèse de Roo.

## Thème 3 : Roo comme Assistant Professionnel

### Étape 5 : Analyser des données (15 min)

Voyez comment Roo peut se transformer en un assistant d'analyse de données pour explorer un fichier, en extraire des informations et créer des visualisations.

*   **Dossier de la démo :** `ateliers/demo-roo-code/03-assistant-pro/demo-1-analyse/`
*   **Objectif :** Découvrir les capacités d'analyse et de synthèse de Roo.

### Étape 6 : Créer une présentation (15 min)

Utilisez Roo pour générer une présentation structurée sur un sujet donné.

*   **Dossier de la démo :** `ateliers/demo-roo-code/03-assistant-pro/demo-2-presentation/`
*   **Objectif :** Apprendre à générer du contenu de présentation.

### Étape 7 : Améliorer sa communication (15 min)

Roo peut vous aider à rédiger des e-mails, des rapports et d'autres communications professionnelles.

*   **Dossier de la démo :** `ateliers/demo-roo-code/03-assistant-pro/demo-3-communication/`
*   **Objectif :** Utiliser Roo comme un assistant à la rédaction.

## Thème 4 : Création de Contenu

### Étape 8 : Créer du contenu (15 min)

Utilisez la puissance de Roo pour générer du contenu, comme une page web simple, à partir d'une simple description.

*   **Dossier de la démo :** `ateliers/demo-roo-code/04-creation-contenu/demo-1-web/`
*   **Objectif :** S'initier à la génération de code avec le mode `Code`.

### Étape 9 : Stratégie pour les réseaux sociaux (20 min)

Découvrez comment Roo peut vous aider à élaborer une stratégie de contenu pour les réseaux sociaux.

*   **Dossier de la démo :** `ateliers/demo-roo-code/04-creation-contenu/demo-2-reseaux-sociaux/`
*   **Objectif :** Utiliser Roo pour la planification de contenu.

## Thème 5 : Projets Avancés

### Étape 10 : Conception d'architecture (25 min)

Apprenez à utiliser Roo pour concevoir l'architecture d'une application.

*   **Dossier de la démo :** `ateliers/demo-roo-code/05-projets-avances/demo-1-architecture/`
*   **Objectif :** Utiliser Roo pour des tâches d'architecture logicielle.

### Étape 11 : Documentation technique (20 min)

Découvrez comment Roo peut vous aider à générer de la documentation technique.

*   **Dossier de la démo :** `ateliers/demo-roo-code/05-projets-avances/demo-2-documentation/`
*   **Objectif :** Automatiser la création de documentation.

## Thème 6 : Personnalisation Avancée

### Étape 12 : Configurer les Custom Instructions (20 min)

Apprenez à personnaliser le comportement de Roo avec des règles projet et globales pour adapter l'assistant à vos conventions et préférences.

*   **Documentation :** [CUSTOM-INSTRUCTIONS-ROO.md](./CUSTOM-INSTRUCTIONS-ROO.md)
*   **Objectif :** Maîtriser le système de rules et AGENTS.md

**Concepts abordés :**

*   Configuration globale (`~/.roo/rules/`)
*   Configuration projet (`.roo/rules/`)
*   Rules mode-specific (`.roo/rules-code/`, `.roo/rules-architect/`)
*   Fichier AGENTS.md pour les équipes
*   Hiérarchie et priorité des sources

**Exercices pratiques :**

1.  Créer une configuration projet avec vos conventions
2.  Définir des rules spécifiques au mode Code
3.  Mettre en place un AGENTS.md pour standardiser le comportement en équipe