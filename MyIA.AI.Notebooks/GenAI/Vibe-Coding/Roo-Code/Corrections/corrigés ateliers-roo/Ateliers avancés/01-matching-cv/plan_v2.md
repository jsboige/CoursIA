# Plan Technique Détaillé - V2 Matching Sémantique

Ce document décrit l'architecture et la logique du script Python `match_v2.py`, chargé de réaliser un matching sémantique entre des CV de consultants et des offres d'emploi.

## 1. Initialisation

Le script commencera par importer les bibliothèques nécessaires et charger les configurations.

*   **Bibliothèques requises :**
    *   `pandas` : Pour la manipulation des données.
    *   `openai` : Pour l'accès aux modèles d'embedding et de langage.
    *   `semantic-kernel` : Pour le moteur de recherche sémantique en mémoire.
    *   `dotenv` : Pour charger les variables d'environnement.
    *   `os` : Pour interagir avec le système d'exploitation.
    *   `asyncio` : Pour exécuter le code asynchrone de `semantic-kernel`.

*   **Variables d'environnement :**
    *   Le script devra charger une variable `OPENAI_API_KEY` depuis un fichier `.env`. Il est crucial de ne pas stocker la clé en dur dans le code.

## 2. Chargement des données

Les données sources seront chargées depuis les fichiers CSV présents dans le répertoire `data/`.

*   **Consultants :** Charger `consultants.csv` dans un DataFrame pandas.
*   **Offres d'emploi :** Charger `jobs.csv` dans un autre DataFrame pandas.
*   Des vérifications basiques (ex: colonnes attendues, gestion des valeurs manquantes) seront effectuées.

## 3. Mise en place du moteur sémantique

Le cœur du système sera basé sur `semantic-kernel` et l'API OpenAI.

*   **Client OpenAI :** Initialiser le client `OpenAI` en utilisant la clé API chargée précédemment.
*   **Kernel Sémantique :** Initialiser le `Kernel` de `semantic-kernel`.
*   **Service d'Embedding :** Configurer un service d'embedding dans le kernel en utilisant `OpenAITextEmbedding` avec le modèle `text-embedding-3-small`.
*   **Mémoire Sémantique :** Instancier une `VolatileMemoryStore` qui servira de base de données vectorielle en mémoire. Une collection sera créée pour stocker les profils des consultants (par exemple, "consultants").

## 4. Indexation des consultants

Chaque profil de consultant sera converti en vecteur et stocké dans la mémoire sémantique.

1.  **Boucle sur les consultants :** Itérer sur chaque ligne du DataFrame des consultants.
2.  **Création de la description :** Pour chaque consultant, concaténer les champs pertinents (ex: `Titre`, `Experience`, `Competences`) en une seule chaîne de caractères descriptive.
3.  **Génération de l'embedding :** Appeler le service d'embedding OpenAI pour obtenir le vecteur de cette description.
4.  **Stockage :** Utiliser la méthode `memory.upsert` de `semantic-kernel` pour stocker l'embedding dans la collection "consultants". Les métadonnées importantes comme l'ID du consultant et le texte original seront également sauvegardées dans l'enregistrement (`MemoryRecord`).

## 5. Processus de Matching

Pour chaque offre d'emploi, le script recherchera les consultants les plus pertinents.

1.  **Boucle sur les offres :** Itérer sur chaque ligne du DataFrame des offres d'emploi.
2.  **Génération de l'embedding de l'offre :** Générer le vecteur de la description de l'offre en utilisant le même modèle `text-embedding-3-small`.
3.  **Recherche de similarité :** Utiliser la méthode `memory.search` sur la collection "consultants". Cette méthode prendra en entrée l'embedding de l'offre et retournera les N consultants les plus similaires, avec leur score de pertinence. Le nombre de résultats (N) et le seuil de similarité minimal seront des paramètres configurables.

## 6. Génération des Résultats

Les résultats du matching seront formatés et sauvegardés.

*   **Structure des résultats :** Créer une liste de dictionnaires ou un DataFrame pandas contenant au minimum : `job_id`, `consultant_id`, `score_de_similarite`.
*   **Sauvegarde :** Exporter ces résultats dans un nouveau fichier CSV nommé `results_v2.csv` à la racine du projet `exercice-1-v2`.

## 7. (Optionnel) Justification par LLM

Cette étape est prévue pour une itération future et ne sera pas implémentée dans la V2 initiale du script.

*   **Principe :** Pour les meilleurs matchs (par exemple, ceux dépassant un certain score), le script pourrait faire un appel supplémentaire à un modèle de langage.
*   **Modèle :** `gpt-4o-mini` serait utilisé pour sa rapidité et son faible coût.
*   **Prompt :** Un prompt serait construit, incluant la description de l'offre et le profil du consultant, demandant au modèle de générer un court paragraphe (2-3 phrases) expliquant pourquoi le profil est pertinent pour l'offre.
*   **Résultat :** Ce texte de justification pourrait être ajouté comme une colonne supplémentaire dans le fichier `results_v2.csv`.