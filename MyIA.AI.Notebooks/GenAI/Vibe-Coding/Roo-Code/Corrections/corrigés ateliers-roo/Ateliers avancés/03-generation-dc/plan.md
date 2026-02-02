# Plan de Conception pour le Script `generation_dc.py` (Version 3 - Traitement Parallèle)

## 1. Objectif du Script

Ce script a pour but d'automatiser la génération de Dossiers de Compétences (DC) personnalisés pour chaque consultant d'une base de données, en réponse à chaque fiche de poste disponible. Il lira les données depuis des fichiers CSV, traitera chaque combinaison consultant/poste de manière **parallèle et asynchrone**, et sauvegardera chaque DC généré dans un fichier distinct. Le script utilisera la bibliothèque `python-dotenv` pour gérer les clés d'API et `asyncio` pour orchestrer les appels concurrents à l'API `gpt-4o-mini` via `semantic-kernel`.

## 2. Structure Générale du Script

Le script sera organisé autour d'une logique de traitement parallèle. Il préparera d'abord une liste de toutes les tâches à effectuer, puis les exécutera de manière concurrente par lots pour optimiser les performances et gérer la charge.

```mermaid
graph TD
    A[Début] --> B{Charger la configuration (.env)};
    B --> C{Charger les données des consultants et des postes};
    C --> D{Préparer une liste de toutes les paires (consultant, poste)};
    D --> E{Créer le répertoire de sortie};
    E --> F{Initialiser le Kernel Semantic Kernel};
    F --> G{Définir la fonction sémantique};
    G --> H{Traiter la liste des paires par lots (chunks)};
    H --> I{Pour chaque lot...};
    I --> J{Créer un ensemble de tâches asynchrones};
    J --> K{Exécuter les tâches en parallèle avec asyncio.gather};
    K --> L{Sauvegarder les résultats de chaque tâche};
    L --> H;
    H --> M[Fin du traitement des lots];
    M --> N[Fin];
```

## 3. Détail des Étapes

### Étape 1 : Chargement de la Configuration

-   **Objectif :** Charger les variables d'environnement, notamment la clé API OpenAI, de manière sécurisée.
-   **Actions :**
    1.  Importer la fonction `load_dotenv` de la bibliothèque `python-dotenv`.
    2.  Appeler `load_dotenv()` au début du script pour charger les variables du fichier `.env`.
    3.  Dans la configuration du service `OpenAIChatCompletion`, récupérer la clé API via `os.getenv("OPENAI_API_KEY")`.

### Étape 2 : Préparation de l'Environnement et des Données

-   **Objectif :** Mettre en place le répertoire de sortie et charger les données source.
-   **Actions :**
    1.  Définir et créer le répertoire de sortie `output/` s'il n'existe pas.
    2.  Charger `ateliers/data_metier_csv/Base consultants.csv` et `ateliers/data_metier_csv/Fiches de poste client.csv` dans des DataFrames `pandas`.

### Étape 3 : Initialisation du Kernel et de la Fonction Sémantique

-   **Objectif :** Configurer `semantic-kernel` pour la génération de texte.
-   **Actions :**
    1.  Importer les classes nécessaires (`Kernel`, `OpenAIChatCompletion`).
    2.  Instancier le Kernel.
    3.  Configurer et ajouter le service `gpt-4o-mini` en utilisant la clé API chargée à l'étape 1.
    4.  Définir un `prompt_template` flexible avec des placeholders (`{{$consultant_details}}`, `{{$job_requirements}}`).
    5.  Créer la fonction sémantique `generer_dc_function` à partir de ce template.

### Étape 4 : Stratégie de Traitement Parallèle

-   **Objectif :** Préparer et exécuter la génération des DC de manière asynchrone et concurrente.
-   **Actions :**
    1.  **Préparer les tâches :**
        a.   Créer une liste vide `tasks_to_run`.
        b.   Itérer sur les consultants et les postes pour créer chaque paire `(consultant, poste)`.
        c.   Ajouter chaque paire à la liste `tasks_to_run`.
    2.  **Définir la fonction de traitement unitaire :**
        a.   Créer une fonction `async def generer_un_dc(consultant, poste, kernel, function)` qui prend en charge la génération d'un seul DC.
        b.   Cette fonction contiendra la logique pour :
            i.   Préparer les `KernelArguments`.
            ii.  Invoquer la fonction sémantique de manière asynchrone : `await kernel.invoke(function, arguments)`.
            iii. Construire le nom du fichier de sortie.
            iv.  Sauvegarder le résultat dans le fichier.
            v.   Retourner le nom du fichier généré pour le suivi.
    3.  **Exécuter par lots (chunks) :**
        a.   Définir une taille de lot (ex: `CHUNK_SIZE = 25`).
        b.   Itérer sur la liste `tasks_to_run` par tranches de `CHUNK_SIZE`.
        c.   Pour chaque lot :
            i.   Créer une liste de coroutines en appelant `generer_un_dc` pour chaque paire du lot.
            ii.  Utiliser `await asyncio.gather(*coroutines_du_lot)` pour exécuter toutes les tâches du lot en parallèle.
            iii. Afficher un message de progression indiquant que le lot est terminé.

### Étape 5 : Fonction Principale Asynchrone

-   **Objectif :** Orchestrer l'exécution de l'ensemble du script.
-   **Actions :**
    1.  Créer une fonction `async def main():` qui encapsulera toute la logique (étapes 1 à 4).
    2.  Lancer le script via le point d'entrée standard :
        ```python
        if __name__ == "__main__":
            asyncio.run(main())
        ```

## 4. Dépendances requises

-   `semantic-kernel`
-   `python-dotenv`
-   `openai`
-   `pandas`
-   `aiofiles` (recommandé pour la sauvegarde asynchrone des fichiers)

Ce plan servira de feuille de route pour la refonte du script `generation_dc.py` vers une architecture parallèle et plus robuste.