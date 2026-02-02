# Atelier 3 : Génération de Dossiers de Compétences (DC) sur Mesure

## 1. Contexte et Objectif

La capacité à présenter un profil de consultant qui correspond parfaitement aux attentes d'un client est un avantage concurrentiel majeur. Cet atelier se concentre sur la **génération d'un Dossier de Compétences (DC) personnalisé** en combinant les informations d'un consultant avec les exigences d'une fiche de poste spécifique.

L'objectif est d'apprendre à préparer et structurer des données pour ensuite utiliser un modèle de langage (LLM) afin de générer un DC pertinent et sur mesure. Cet exercice met l'accent sur la préparation des données en amont de l'interaction avec le LLM.

## 2. Description de l'Exercice

Votre mission consiste à utiliser deux sources de données pour préparer la génération d'un DC :

1.  **Choisir un profil de consultant :**
    *   Le fichier [`../../data_metier_csv/Base consultants.csv`](../../data_metier_csv/Base%20consultants.csv) contient une liste de profils de consultants avec leurs compétences et expériences.
    *   Vous devrez sélectionner **un** consultant dans cette base.

2.  **Choisir une fiche de poste :**
    *   Le fichier [`../../data_metier_csv/Fiches de poste client.csv`](../../data_metier_csv/Fiches%20de%20poste%20client.csv) décrit les besoins et les attendus pour différents postes chez nos clients.
    *   Vous devrez sélectionner **une** fiche de poste pertinente.

3.  **Préparer les données pour le LLM :**
    *   L'objectif final est de fournir au LLM le profil du consultant et la fiche de poste afin qu'il génère un DC qui met en valeur les compétences du consultant en réponse aux besoins du client.

## 3. Le Script d'Aide à la Préparation

Pour vous assister, un script Python a été mis à votre disposition : `preparer_donnees.py`.

Ce script vous permet de :
- Charger les deux fichiers CSV.
- Sélectionner facilement un consultant et une fiche de poste (par leur nom ou leur ID).
- Afficher à l'écran les informations consolidées des deux sélections.

Une fois les informations affichées, vous pouvez simplement les copier-coller dans le prompt de votre LLM favori pour réaliser la génération du Dossier de Compétences.

## 4. Livrables Attendus

-   Une **discussion avec un LLM** où vous lui fournissez le profil et la fiche de poste, et où vous l'amenez à générer un DC de qualité.
-   Le **Dossier de Compétences final** généré par le LLM, au format Markdown.

Bonne génération !