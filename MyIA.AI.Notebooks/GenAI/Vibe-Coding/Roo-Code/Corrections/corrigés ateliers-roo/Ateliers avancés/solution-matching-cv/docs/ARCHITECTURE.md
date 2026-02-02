# Architecture Technique

Ce document décrit l'architecture technique de l'application de matching CV/Poste. Pour une introduction générale au projet, veuillez consulter le [document d'introduction](INTRODUCTION.md).

## 1. Vue d'Ensemble

L'application est conçue comme une application web modulaire et testable, construite avec le micro-framework **Flask**. Elle permet de comparer différents algorithmes de matching.

```mermaid
graph TD
    subgraph "Navigateur Client"
        A[Interface Utilisateur<br>(index.html)]
    end

    subgraph "Serveur Backend (Flask)"
        B[main.py<br>Point d'Entrée & Contrôleur]
        C{Logique de Matching}
        D[simple_matching.py<br>Algorithme Simple]
        E[matching.py<br>Algorithmes Sémantiques]
    end

    subgraph "Services & Données"
        F[Données CSV<br>(CVs & Postes)]
        G[ChromaDB<br>Base de Données Vectorielle]
        H[API OpenAI<br>Embeddings]
    end

    A -- Requête HTTP (POST) --> B
    B -- Appelle --> C
    C -- Choisit --> D
    C -- Choisit --> E
    B -- Charge --> F
    E -- Indexe/Récupère --> G
    E -- Génère via --> H
```

### 1.1. Flux de Travail Typique

1.  **Au démarrage**, l'application pré-charge les données depuis les fichiers CSV.
2.  L'utilisateur accède à l'interface via une requête `GET`.
3.  Il choisit un algorithme et soumet le formulaire via une requête `POST`.
4.  Le backend Flask (`main.py`) appelle la logique métier correspondante (`simple_matching.py` ou `matching.py`).
5.  La logique sémantique interagit avec **ChromaDB** et l'**API OpenAI** si nécessaire.
6.  Les résultats sont retournés et affichés sur la page.

## 2. Structure du Code

La base de code est organisée pour séparer clairement les responsabilités :

-   `main.py`: **Point d'Entrée et Contrôleur**. Gère les routes, traite les requêtes HTTP et orchestre les appels aux logiques métier.
-   `app/simple_matching.py`: **Logique Métier Simple**. Contient l'algorithme de baseline. Pour plus de détails, voir la [description des algorithmes](ALGORITHMS.md).
-   `app/matching.py`: **Logique Métier Sémantique**. Contient les logiques `best_score` et `stable`, ainsi que le pipeline de traitement sémantique. Pour plus de détails, voir la [description des algorithmes](ALGORITHMS.md).
-   `templates/`: **Vue**. Contient le template HTML de l'interface.
-   `tests/`: **Suite de Tests**. Pour plus de détails, consultez le [guide des tests](TESTING.md).

## 3. Choix Technologiques Clés

-   **Backend :** **Flask**. Choisi pour sa légèreté et sa testabilité, un facteur décisif après l'échec d'un prototype Streamlit (voir [l'historique du projet](HISTORY.md)).
-   **Frontend :** **HTML / CSS simple (via Jinja2)**. Maintient l'application légère.
-   **Manipulation de Données :** **Pandas**. Pour une manipulation efficace des données CSV.
-   **Moteur Sémantique :** **`semantic-kernel`**. Pour interagir avec les modèles d'embedding.
-   **Base de Données Vectorielle :** **ChromaDB**. Pour stocker de manière persistante les embeddings avec un cache idempotent.
-   **Algorithme de Matching Stable :** **Bibliothèque `matching`**. Fournit une implémentation de l'algorithme de Gale-Shapley.
-   **Tests :** **`pytest`** et **`pytest-playwright`**. Pour les tests unitaires et E2E.