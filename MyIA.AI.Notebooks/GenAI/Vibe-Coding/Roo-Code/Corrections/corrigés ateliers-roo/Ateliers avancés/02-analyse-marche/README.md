# Atelier 2 : Analyse de la Tension du Marché de l'IT avec des Données Structurées

## 1. Contexte Métier

Pour rester compétitives, les ESN comme Pauwels Consulting doivent avoir une compréhension fine et actualisée du marché de l'emploi IT. Croiser les **tendances du marché externe** avec nos **capacités et besoins internes** est crucial. Par exemple, savoir si nous avons les consultants disponibles pour répondre à une forte demande sur une technologie spécifique nous permet d'être plus réactifs.

L'objectif de cet atelier est d'automatiser l'analyse croisée de données de marché pré-collectées et d'indicateurs internes pour en extraire des insights stratégiques.

## 2. Objectifs Pédagogiques

À la fin de cet atelier, vous saurez utiliser un script Python avec `pandas` pour :
- **Lire et manipuler des données** depuis des fichiers CSV.
- **Nettoyer et structurer** des jeux de données hétérogènes.
- **Effectuer des analyses croisées** entre différentes sources de données.
- **Calculer des statistiques descriptives** (comptages, moyennes, etc.).
- **Générer un rapport d'analyse** synthétique directement dans la console.

## 3. Description du Scénario

Votre mission est d'utiliser le script `analyse_marche.py` pour analyser deux jeux de données :
1.  **Données du marché :** Un fichier CSV contenant des offres d'emploi scrapées.
2.  **Indicateurs internes :** Un fichier CSV listant les besoins en missions et les consultants disponibles.

Le script exécute les tâches suivantes :
- Il charge les deux jeux de données.
- Il identifie et affiche les **5 compétences les plus recherchées** sur le marché.
- Il liste les **profils pour lesquels des missions sont ouvertes** en interne.
- Il présente un résumé de ces informations pour une prise de décision rapide.

## 4. Données d'Entrée

Les fichiers de données se trouvent dans le répertoire `ateliers/data_metier_csv/` :
-   [`Marché (scraping).csv`](../data_metier_csv/Marché%20(scraping).csv): Données sur les offres d'emploi du marché IT.
-   [`Indicateurs internes.csv`](../data_metier_csv/Indicateurs%20internes.csv): Données sur les missions ouvertes et les consultants disponibles.

## 5. Livrables Attendus

-   L'exécution réussie du script `analyse_marche.py`.
-   Un **rapport d'analyse affiché dans le terminal**, montrant les compétences clés du marché et les besoins internes.

## 6. Instructions d'Exécution

1.  **Assurez-vous d'avoir Python et pandas installés :**
    ```bash
    pip install pandas
    ```

2.  **Exécutez le script d'analyse :**
    Ouvrez un terminal dans le répertoire `ateliers/02-analyse-marche/` et exécutez la commande suivante :
    ```bash
    python analyse_marche.py
    ```

3.  **Analysez les résultats :**
    Observez le rapport généré dans la console. Il vous donnera un aperçu des tendances du marché et des besoins de l'entreprise.