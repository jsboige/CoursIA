# Atelier 1 : Matching CV / Fiche de Poste

## 1. Contexte Métier

Le processus de recrutement chez Pauwels Consulting, comme dans de nombreuses ESN, repose sur notre capacité à identifier rapidement les bons profils pour les besoins de nos clients. Ce processus comporte plusieurs défis :
- **Hétérogénéité des descriptions :** Les fiches de poste des clients sont souvent vagues, incomplètes ou non structurées.
- **Volume de CVs :** Notre base de données interne contient de nombreux CVs qu'il est long de comparer manuellement à chaque nouvelle mission.
- **Subjectivité :** L'évaluation humaine peut introduire des biais ou manquer des correspondances subtiles.

L'objectif de cet atelier est de créer un **assistant IA capable d'automatiser et d'objectiver la première phase de qualification** pour accélérer le travail de nos recruteurs.

## 2. Objectifs Pédagogiques

À la fin de cet atelier, vous saurez utiliser l'assistant `roo` pour :
- **Analyser et structurer** un texte non formaté (une fiche de poste).
- **Comparer sémantiquement** deux documents (un CV et une fiche de poste).
- **Extraire des informations clés** et les reformuler selon un format défini.
- **Générer un rapport de synthèse** argumenté basé sur une analyse.
- **Orchestrer** plusieurs étapes de traitement de l'information.

## 3. Description du Scénario

Votre mission, si vous l'acceptez, est d'utiliser Roo pour créer un workflow qui :
1.  Prend en entrée le fichier `Base consultants.csv` contenant les profils des consultants.
2.  Prend en entrée le fichier `Fiches de poste client.csv` contenant les fiches de poste.
3.  **Analyse une fiche de poste** pour en extraire les compétences techniques, fonctionnelles, l'expérience et la séniorité requises.
4.  **Recherche dans la base consultants** les profils les plus pertinents pour cette fiche de poste.
5.  **Calcule un score de matching** pour chaque profil identifié.
6.  **Génère une note de synthèse** qui justifie le score pour les meilleurs profils, en mettant en évidence les points forts et les manques éventuels.

## 4. Données d'Entrée

Les nouvelles données métier sont disponibles directement dans le répertoire `ateliers/data_metier_csv` :
-   `Base consultants.csv`: Contient les profils des consultants.
-   `Fiches de poste client.csv`: Contient les fiches de poste des clients.

## 5. Livrables Attendus

À la fin de l'atelier, vous devrez avoir produit :
-   Un **rapport d'analyse** (au format Markdown, par exemple) contenant une liste des meilleurs profils pour une fiche de poste donnée, avec leur score de matching et une note de synthèse.
-   Une **conversation avec Roo** montrant clairement les étapes que vous avez suivies pour arriver à ce résultat.

## 6. Déroulé Suggéré

1.  **Prise en main :** Demandez à Roo de lister et de prendre connaissance des deux fichiers CSV.
2.  **Analyse d'une fiche de poste :** Choisissez une fiche de poste et demandez à Roo d'en extraire les critères clés.
3.  **Recherche et matching :** Demandez à Roo de rechercher les consultants correspondants dans la base et de calculer leur score de matching.
4.  **Synthèse :** Demandez à Roo de générer le rapport final pour les profils les plus pertinents.
5.  **(Bonus) Automatisation :** Essayez de créer une seule instruction complexe pour que Roo réalise toutes ces étapes en une seule fois pour une fiche de poste donnée.