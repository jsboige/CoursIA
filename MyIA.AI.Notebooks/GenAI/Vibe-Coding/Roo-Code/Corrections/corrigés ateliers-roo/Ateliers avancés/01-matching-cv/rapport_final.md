# Rapport de Synthèse Final - Atelier 1 : Matching CV / Fiche de Poste

## 1. Introduction : Objectif du Projet

L'objectif initial de ce projet, tel que défini dans le document d'énoncé [`README.md`](exercice-1-v2/README.md), était de développer un assistant capable d'automatiser et d'objectiver la première phase de qualification des profils de consultants. Le but principal était de comparer sémantiquement des CVs à des fiches de poste pour accélérer le processus de recrutement et le fiabiliser.

## 2. Démarche Suivie

Le projet s'est déroulé en quatre étapes principales, chacune documentée par un livrable spécifique :

1.  **Planification (`plan.md`) :** Une approche technique a été définie, basée sur un script Python utilisant la librairie `pandas` et une méthode de matching par mots-clés à partir d'un lexique prédéfini.
2.  **Implémentation (`match.py`) :** Un script Python a été développé pour charger les données, normaliser le texte, extraire les mots-clés et calculer un score de correspondance, générant un fichier `results.csv`.
3.  **Débogage (`debug_report.md`) :** Le script initial contenait des erreurs (chemins de fichiers, logique d'extraction) qui ont été identifiées et corrigées pour assurer sa conformité avec le plan et la plausibilité des résultats.
4.  **Validation (`validation_report.md`) :** Une analyse critique a été menée pour évaluer si la solution répondait réellement à l'objectif métier initial, au-delà de la simple exécution technique.

## 3. Solution Développée

La solution finale est un script Python, [`match.py`](exercice-1-v2/match.py), qui opère de la manière suivante :
-   Il charge les CVs et les fiches de poste depuis des fichiers CSV.
-   Il normalise le contenu textuel (compétences, descriptions) pour uniformiser la comparaison.
-   Il recherche la présence de mots-clés d'un lexique défini (`['python', 'java', 'sql', ...]`) dans les documents normalisés.
-   Il calcule un `match_score` correspondant au nombre de mots-clés en commun entre un CV et une fiche de poste.
-   Les résultats sont consolidés dans le fichier [`results.csv`](exercice-1-v2/results.csv), qui liste les paires consultant/poste ayant au moins un mot-clé en commun.

## 4. Analyse Critique de la Solution

Comme souligné dans le [`validation_report.md`](exercice-1-v2/validation_report.md), la solution développée, bien que fonctionnelle sur le plan technique, **n'est pas satisfaisante au regard des objectifs métiers**.

-   **Absence de Sémantique :** L'approche par mots-clés est rigide. Elle ne comprend pas le contexte ni les synonymes (ex: "gestion de projet" vs "pilotage de projet"). Elle est incapable de saisir les nuances d'une compétence.
-   **Extraction d'Information Limitée :** Le script se contente de vérifier une liste de compétences et ignore des critères essentiels comme la séniorité, le type d'expérience ou les compétences fonctionnelles non listées.
-   **Manque de Synthèse :** Le livrable est un score brut. Il n'y a aucune note de synthèse argumentée qui justifie le score, un élément pourtant clé demandé dans l'énoncé pour aider les recruteurs.

En somme, le script répond à la question "quels consultants possèdent ces mots-clés exacts ?" mais échoue à répondre à la question "quels sont les consultants les plus pertinents pour cette mission ?".

## 5. Conclusion et Perspectives

Cet atelier a permis de réaliser une première brique d'automatisation et de mettre en évidence les limites d'une approche purement lexicale. Le travail de planification, de développement et de débogage a été mené à bien.

Pour une **Version 2** de la solution, les recommandations suivantes, issues du rapport de validation, doivent être suivies :
1.  **Adopter une Approche Sémantique :** Utiliser des modèles de langage (embeddings) pour comparer les documents sur la base de leur signification réelle, et non plus sur des mots-clés.
2.  **Enrichir l'Extraction de Données :** Développer des modules capables d'identifier et de structurer des informations complexes comme le nombre d'années d'expérience, les secteurs d'activité, ou le niveau de responsabilité.
3.  **Générer une Synthèse Automatique :** Intégrer une étape finale où un modèle de langage (LLM) génère un paragraphe de synthèse pour les profils les plus pertinents, expliquant les forces et faiblesses de la candidature par rapport au poste.

Cette nouvelle approche permettrait de créer un outil véritablement utile et performant pour les équipes de recrutement.