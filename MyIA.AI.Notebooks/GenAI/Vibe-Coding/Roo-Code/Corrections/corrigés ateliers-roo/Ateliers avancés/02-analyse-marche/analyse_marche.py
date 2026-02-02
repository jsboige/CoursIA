import pandas as pd
import os

# 1. Constantes
# Définition des chemins de manière robuste en se basant sur l'emplacement du script.
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.normpath(os.path.join(SCRIPT_DIR, '../../ateliers/data_metier_csv/'))
MARKET_DATA_PATH = os.path.join(DATA_DIR, 'Marché (scraping).csv')
INTERNAL_DATA_PATH = os.path.join(DATA_DIR, 'Indicateurs internes.csv')

# 2. Fonctions d'analyse

def charger_donnees(chemin_fichier: str) -> pd.DataFrame:
    """Charge un fichier CSV dans un DataFrame pandas."""
    try:
        return pd.read_csv(chemin_fichier)
    except FileNotFoundError:
        print(f"Erreur : Le fichier '{chemin_fichier}' est introuvable.")
        return pd.DataFrame()

def analyser_competences_marche(df_marche: pd.DataFrame) -> pd.Series:
    """Analyse le DataFrame du marché pour extraire le top 5 des compétences."""
    colonne_competences = 'Compétences demandées'
    if colonne_competences not in df_marche.columns:
        print(f"Avertissement : Colonne '{colonne_competences}' non trouvée dans le fichier marché.")
        return pd.Series()
    
    # Remplacer les NaN par des chaînes vides pour éviter les erreurs
    competences = df_marche[colonne_competences].fillna('')
    toutes_les_competences = ';'.join(competences)
    liste_competences = toutes_les_competences.split(';')
    
    # Nettoyer et filtrer les chaînes vides
    competences_nettoyees = [comp.strip().lower() for comp in liste_competences if comp.strip()]
    
    if not competences_nettoyees:
        return pd.Series()

    series_competences = pd.Series(competences_nettoyees)
    return series_competences.value_counts().head(5)

def analyser_besoins_internes(df_interne: pd.DataFrame) -> list:
    """Analyse le DataFrame interne pour identifier les profils recherchés."""
    colonne_missions = 'Missions ouvertes'
    colonne_profil = 'Profil'

    if colonne_missions not in df_interne.columns or colonne_profil not in df_interne.columns:
        print(f"Avertissement : Colonnes '{colonne_missions}' ou '{colonne_profil}' non trouvées dans le fichier interne.")
        return []
        
    # Remplacer les NaN par 0 et s'assurer que la colonne est numérique
    df_interne[colonne_missions] = pd.to_numeric(df_interne[colonne_missions], errors='coerce').fillna(0)
    
    # Filtrer les profils où il y a plus de 0 missions ouvertes
    missions_ouvertes_df = df_interne[df_interne[colonne_missions] > 0]
    return missions_ouvertes_df[colonne_profil].tolist()

def generer_rapport_console(top_competences: pd.Series, besoins_internes: list):
    """Affiche les résultats de l'analyse de manière formatée dans la console."""
    print("==================================================")
    print("=== Rapport d'Analyse du Marché de l'Emploi IT ===")
    print("==================================================")
    print("\n--> Top 5 des compétences les plus demandées sur le marché :\n")
    
    if not top_competences.empty:
        for i, (competence, count) in enumerate(top_competences.items(), 1):
            print(f"{i}. {competence.capitalize()} (Mentionnée {count} fois)")
    else:
        print("Aucune donnée de compétence à afficher.")

    print("\n--> Besoins internes actuels (Missions ouvertes) :\n")
    
    if besoins_internes:
        for profil in besoins_internes:
            print(f"- {profil}")
    else:
        print("Aucun besoin interne identifié.")
        
    print("\n==================================================")

# 3. Fonction Principale (Orchestrateur)

def main():
    """Point d'entrée principal du script."""
    # Orchestration des appels de fonctions
    
    # Charger les données
    df_marche = charger_donnees(MARKET_DATA_PATH)
    df_interne = charger_donnees(INTERNAL_DATA_PATH)
    
    if not df_marche.empty and not df_interne.empty:
        # Analyser les données
        top_5_competences = analyser_competences_marche(df_marche)
        missions_ouvertes = analyser_besoins_internes(df_interne)
        
        # Générer le rapport
        generer_rapport_console(top_5_competences, missions_ouvertes)

# 4. Point d'entrée du script

if __name__ == "__main__":
    main()
