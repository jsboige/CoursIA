# -*- coding: utf-8 -*-
import pandas as pd
import os

def analyse_donnees_marche():
    """
    Analyse les données du marché et les indicateurs internes à partir de fichiers CSV.
    """
    print("--- Début de l'analyse de marché ---")

    # Définir les chemins relatifs vers les fichiers de données
    base_path = os.path.join(os.path.dirname(__file__), '..', 'data_metier_csv')
    path_marche = os.path.join(base_path, 'Marché (scraping).csv')
    path_indicateurs = os.path.join(base_path, 'Indicateurs internes.csv')

    # --- 1. Analyse des données du marché ---
    print("\n--- 1. Analyse des Données du Marché (Scraping) ---")
    try:
        df_marche = pd.read_csv(path_marche)
        print("Aperçu des données du marché :")
        print(df_marche.head())
        
        # Compter les compétences les plus demandées
        df_marche['Compétences demandées'] = df_marche['Compétences demandées'].str.split('; ')
        competences = df_marche.explode('Compétences demandées')['Compétences demandées']
        top_competences = competences.value_counts().nlargest(5)
        
        print("\nTop 5 des compétences les plus demandées :")
        print(top_competences)

    except FileNotFoundError:
        print(f"ERREUR : Le fichier {path_marche} n'a pas été trouvé.")
        return

    # --- 2. Analyse des indicateurs internes ---
    print("\n--- 2. Analyse des Indicateurs Internes ---")
    try:
        df_indicateurs = pd.read_csv(path_indicateurs)
        print("Aperçu des indicateurs internes :")
        print(df_indicateurs.head())

        # Filtrer les profils avec des missions ouvertes
        missions_ouvertes = df_indicateurs[df_indicateurs['Missions ouvertes'] > 0]
        
        if not missions_ouvertes.empty:
            print("\nProfils avec des missions actuellement ouvertes :")
            print(missions_ouvertes[['Profil', 'Missions ouvertes', 'Consultants disponibles']])
        else:
            print("\nAucune mission ouverte identifiée dans les indicateurs.")

    except FileNotFoundError:
        print(f"ERREUR : Le fichier {path_indicateurs} n'a pas été trouvé.")
        return

    print("\n--- Fin de l'analyse de marché ---")

if __name__ == '__main__':
    analyse_donnees_marche()
