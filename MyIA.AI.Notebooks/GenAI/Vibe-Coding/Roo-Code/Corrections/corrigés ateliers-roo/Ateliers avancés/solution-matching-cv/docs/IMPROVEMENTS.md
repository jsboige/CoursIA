# Améliorations du Projet

Ce document liste les améliorations déjà apportées ainsi que les pistes futures pour faire évoluer ce prototype.

## 1. Améliorations Réalisées

-   **Base de Données Vectorielle Persistante :** L'indexation en mémoire a été remplacée par **ChromaDB**, qui stocke les embeddings des CVs sur le disque. Cela a drastiquement amélioré les performances en évitant le recalcul à chaque lancement.
-   **Migration de `semantic-kernel` :** La bibliothèque a été mise à jour vers une version majeure plus récente, impliquant une refonte de l'API. Cette maintenance a permis de résoudre les avertissements de dépréciation et de garantir la pérennité de la solution.
-   **Optimisation des Appels API :** Le calcul des embeddings pour les fiches de poste se fait désormais par lots (batching), ce qui a significativement réduit le temps de traitement.

## 2. Pistes d'Améliorations Futures

### 2.1. Améliorations des Algorithmes

-   **Génération de Synthèse Explicative :** Utiliser un LLM pour générer un paragraphe expliquant *pourquoi* un profil est pertinent, au-delà du simple score.
-   **Extraction d'Entités Nommées (NER) :** Extraire des informations structurées (années d'expérience, technologies) pour permettre des filtres stricts en plus de la recherche sémantique.

### 2.2. Industrialisation

-   **Exposition via une API REST :** Exposer la logique via une API (Flask ou FastAPI) pour permettre à d'autres applications de consommer le service.
-   **Utilisation de Modèles d'Embedding Open Source :** Remplacer l'API OpenAI par un modèle `sentence-transformers` pour réduire les coûts et la dépendance à un service externe.