import pandas as pd
import os

def preparer_donnees_pour_dc():
    """
    Charge les données des consultants et des fiches de poste,
    permet à l'utilisateur de faire une sélection et affiche
    les informations prêtes à être utilisées dans un prompt LLM.
    """
    # Construire les chemins relatifs au script actuel
    script_dir = os.path.dirname(__file__)
    consultants_path = os.path.join(script_dir, '..', 'data_metier_csv', 'Base consultants.csv')
    postes_path = os.path.join(script_dir, '..', 'data_metier_csv', 'Fiches de poste client.csv')

    # Charger les fichiers CSV
    try:
        df_consultants = pd.read_csv(consultants_path)
        df_postes = pd.read_csv(postes_path)
    except FileNotFoundError as e:
        print(f"Erreur : Un des fichiers CSV n'a pas été trouvé.")
        print(e)
        return

    # --- Sélection du consultant ---
    print("--- Liste des Consultants ---")
    print(df_consultants[['Nom du consultant', 'Titre du profil']])
    
    selected_consultant = None
    while selected_consultant is None:
        try:
            consultant_id = input("Entrez le nom ou l'index du consultant à sélectionner : ")
            # Essayer de convertir en entier (sélection par index)
            try:
                consultant_index = int(consultant_id)
                if 0 <= consultant_index < len(df_consultants):
                    selected_consultant = df_consultants.iloc[consultant_index]
                else:
                    print("Index hors des limites. Veuillez réessayer.")
            # Sinon, traiter comme une sélection par nom
            except ValueError:
                result = df_consultants[df_consultants['Nom du consultant'].str.contains(consultant_id, case=False)]
                if not result.empty:
                    if len(result) > 1:
                        print("Plusieurs consultants trouvés, veuillez être plus spécifique ou utiliser l'index:")
                        print(result[['Nom du consultant', 'Titre du profil']])
                    else:
                        selected_consultant = result.iloc[0]
                else:
                    print("Aucun consultant trouvé avec ce nom. Veuillez réessayer.")
        except Exception as e:
            print(f"Une erreur est survenue : {e}")

    # --- Sélection de la fiche de poste ---
    print("\n--- Liste des Fiches de Poste ---")
    print(df_postes[['ID de la fiche', 'Titre du poste']])

    selected_poste = None
    while selected_poste is None:
        try:
            poste_id = input("Entrez l'ID ou le titre de la fiche de poste à sélectionner : ")
            # Essayer de convertir en entier (sélection par ID)
            try:
                poste_index = int(poste_id)
                result = df_postes[df_postes['ID de la fiche'] == poste_index]
                if not result.empty:
                    selected_poste = result.iloc[0]
                else:
                    print("Aucun poste trouvé avec cet ID. Veuillez réessayer.")
            # Sinon, traiter comme une sélection par titre
            except ValueError:
                result = df_postes[df_postes['Titre du poste'].str.contains(poste_id, case=False)]
                if not result.empty:
                    if len(result) > 1:
                        print("Plusieurs postes trouvés, veuillez être plus spécifique ou utiliser l'ID:")
                        print(result[['ID de la fiche', 'Titre du poste']])
                    else:
                        selected_poste = result.iloc[0]
                else:
                    print("Aucun poste trouvé avec ce titre. Veuillez réessayer.")
        except Exception as e:
            print(f"Une erreur est survenue : {e}")


    # --- Affichage des informations pour le prompt ---
    print("\n" + "="*50)
    print("=== INFORMATIONS POUR LE PROMPT DE GÉNÉRATION DE DC ===")
    print("="*50 + "\n")

    print("--- PROFIL DU CONSULTANT ---")
    print(selected_consultant.to_string())
    
    print("\n" + "-"*50 + "\n")

    print("--- FICHE DE POSTE CLIENT ---")
    print(selected_poste.to_string())
    
    print("\n" + "="*50)
    print("Copiez-collez les informations ci-dessus dans votre LLM.")
    print("="*50)


if __name__ == "__main__":
    preparer_donnees_pour_dc()