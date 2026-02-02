# Description des Algorithmes de Matching

Ce document détaille les trois algorithmes de matching implémentés dans l'application. Chaque algorithme propose une approche différente pour comparer les CV des consultants aux fiches de poste.

## 1. Algorithme "Simple" (Baseline)

### Principe

Cet algorithme est une approche de baseline qui repose sur un comptage simple de mots-clés.

1.  **Extraction des Compétences :** Les compétences sont extraites des colonnes `Compétences` (pour les consultants) et `Compétences clés` (pour les postes).
2.  **Normalisation :** Les compétences sont nettoyées (suppression des espaces superflus) et converties en minuscules pour assurer une comparaison insensible à la casse.
3.  **Calcul du Score :** Pour chaque paire (consultant, poste), le score de matching est simplement le **nombre de compétences en commun**.
4.  **Assignation :** L'algorithme assigne à chaque poste le consultant ayant le score le plus élevé, en s'assurant qu'un consultant ne soit assigné qu'à un seul poste.

### Avantages

-   **Simple et rapide :** Très facile à implémenter et à exécuter.
-   **Interprétable :** Le score est directement lié au nombre de compétences partagées.

### Inconvénients

-   **Manque de Contexte :** Ne comprend pas les synonymes ou les concepts similaires (ex: "gestion de projet" vs "pilotage de projet").
-   **Sensible à la Formulation :** Une simple variation dans la manière de nommer une compétence peut faire échouer le matching.

## 2. Algorithme "Sémantique (Meilleur Score)"

### Principe

Cette approche utilise des embeddings sémantiques pour capturer le sens des compétences et des descriptions, au-delà des simples mots-clés.

1.  **Génération des Embeddings :**
    -   Pour chaque consultant, un embedding est généré à partir de la concaténation de ses compétences et expériences.
    -   Pour chaque fiche de poste, un embedding est généré à partir de ses compétences clés et de sa description.
2.  **Stockage et Cache :** Les embeddings des consultants sont stockés dans une base de données vectorielle **ChromaDB** pour la persistance. Un mécanisme de cache idempotent vérifie si un consultant a déjà été "vectorisé" avant de faire un appel à l'API OpenAI, optimisant ainsi les performances et les coûts.
3.  **Calcul de Similarité :** La similarité cosinus est calculée entre l'embedding de chaque poste et les embeddings de tous les consultants.
4.  **Assignation :** Pour chaque poste, le consultant ayant le **score de similarité le plus élevé** est sélectionné. Comme pour l'algorithme simple, une règle garantit qu'un consultant n'est assigné qu'à un seul poste.

### Avantages

-   **Compréhension du Sens :** Capable de faire correspondre des concepts sémantiquement proches même s'ils sont formulés différemment.
-   **Robuste :** Moins sensible aux variations de vocabulaire.

### Inconvénients

-   **Coût et Latence :** Nécessite des appels à une API externe (OpenAI) pour générer les embeddings.
-   **"Boîte Noire" :** Le score de similarité est moins directement interprétable qu'un simple comptage de mots.

## 3. Algorithme "Sémantique (Stable)"

### Principe

Cet algorithme va plus loin que le "meilleur score" en cherchant un appariement globalement optimal et stable, en utilisant l'algorithme de **Gale-Shapley** (plus précisément, une de ses variantes, l'algorithme Hospital-Resident, qui gère les cas de tailles inégales).

1.  **Calcul des Préférences :** Les scores de similarité sémantique (calculés comme dans l'algorithme précédent) sont utilisés pour établir une liste de préférences pour chaque poste et chaque consultant.
    -   Chaque poste classe les consultants du plus pertinent au moins pertinent.
    -   Chaque consultant classe les postes de la même manière.
2.  **Appariement Stable :** L'algorithme de Gale-Shapley est exécuté. Il simule un processus de "propositions" où un groupe (par exemple, les postes) fait des offres aux membres de l'autre groupe (les consultants), qui peuvent accepter ou rejeter en fonction de leurs préférences. Ce processus itératif garantit qu'il n'existe aucune paire (poste, consultant) qui préférerait être ensemble plutôt qu'avec leur partenaire actuel.
3.  **Résultat :** Le résultat est un ensemble de paires "stables", où la satisfaction globale est maximisée.

### Avantages

-   **Optimalité Globale :** Ne se contente pas du meilleur score local, mais cherche la meilleure solution pour l'ensemble du système.
-   **Évite les "Regrets" :** La stabilité garantit qu'il n'y a pas de situation où un poste et un consultant seraient mutuellement plus heureux ensemble.

### Inconvénients

-   **Complexité :** Plus complexe à implémenter et à comprendre.
-   **Sensibilité aux Préférences :** La qualité de l'appariement dépend entièrement de la qualité des scores de similarité initiaux.