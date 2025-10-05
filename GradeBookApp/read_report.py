import pandas as pd

# Path to the generated Excel file
report_path = r"G:\Mon Drive\MyIA\Formation\Epita\2025\rapport_notes_PrCon.xlsx"

try:
    # Read the Excel file
    df = pd.read_excel(report_path)

    # Find the row for the "Quoridor" group
    quoridor_data = df[df["Groupe (Sujet)"] == "Quoridor"]

    if not quoridor_data.empty:
        # Get all intermediate grades for the whole class
        all_intermediate_grades = df["Note Intermédiaire (avec bonus/malus)"]
        
        # Calculate mean and std dev for the final step
        overall_intermediate_mean = all_intermediate_grades.mean()
        overall_intermediate_std = all_intermediate_grades.std()

        print("--- Analyse pour le groupe 'Quoridor' (après corrections) ---")
        print(quoridor_data.to_string())
        
        print("\n--- Statistiques des notes intermédiaires pour toute la classe (avant standardisation finale) ---")
        print(f"Moyenne des notes intermédiaires : {overall_intermediate_mean:.2f}")
        print(f"Écart-type des notes intermédiaires : {overall_intermediate_std:.2f}")

    else:
        print("Le groupe 'Quoridor' n'a pas été trouvé dans le rapport.")

except FileNotFoundError:
    print(f"Erreur : Le fichier rapport '{report_path}' n'a pas été trouvé.")
except Exception as e:
    print(f"Une erreur est survenue : {e}")