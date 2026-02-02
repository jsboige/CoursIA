# Rapport de Validation - Atelier 1 : Matching CV / Fiche de Poste

## 1. Question

Le script `match.py` résout-il correctement la tâche principale décrite dans l'énoncé, à savoir "automatiser la comparaison des CVs et des fiches de poste pour calculer un score de matching" ?

## 2. Réponse Synthétique

**Non, le script ne résout pas correctement la tâche telle que décrite dans l'énoncé.**

Bien qu'il automatise un calcul de score et produise un résultat, la méthode employée est trop simpliste et ne répond pas aux exigences qualitatives et fonctionnelles du projet, notamment sur la dimension **sémantique** de l'analyse et la **génération d'une synthèse argumentée**.

## 3. Analyse Détaillée

| Point de Conformité | Énoncé (`README.md`) | Implémentation (`match.py`) | Verdict |
| :--- | :--- | :--- | :--- |
| **Objectif Principal** | Automatiser la comparaison pour calculer un score de matching. | Un score est calculé en itérant sur les CVs et les postes. | **Conforme** |
| **Méthode de Comparaison** | La comparaison doit être **sémantique**. | La comparaison est basée sur une **simple correspondance de mots-clés** issus d'un lexique (`LEXICON`) statique. Le sens des mots n'est pas interprété. | **Non Conforme** |
| **Extraction d'Informations** | Extraire compétences (techniques/fonctionnelles), expérience, séniorité. | Seules les compétences du lexique sont extraites. Aucune distinction n'est faite et les autres critères (expérience, séniorité) sont ignorés. | **Partiellement Conforme** |
| **Livrables Attendus** | Un rapport avec score et **note de synthèse** justifiant le matching. | Le script génère un fichier `results.csv` avec un score, mais **aucune note de synthèse** n'est produite. | **Partiellement Conforme** |

## 4. Conclusion et Recommandations

Le script `match.py` constitue une première étape fonctionnelle mais ne peut être considéré comme une solution valide au regard des objectifs fixés. L'approche par mots-clés est trop rigide et ne capture pas la richesse sémantique des descriptions de poste et des CVs.

Pour améliorer la solution, il faudrait :
1.  **Adopter une vraie approche sémantique :** Utiliser des modèles de langage (via des embeddings comme Word2Vec, BERT, ou des appels à des LLMs) pour comparer les textes sur la base de leur sens.
2.  **Enrichir l'extraction de données :** Mettre en place des routines pour extraire et-ou classifier les différents types d'informations demandées (compétences, expérience, etc.).
3.  **Implémenter la génération de synthèse :** Ajouter une étape qui, pour les meilleurs scores, génère un texte argumenté mettant en lumière les adéquations et les manques.