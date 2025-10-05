import os
import glob
import pandas as pd
from gradebook import process_grades, load_student_records, generate_qualitative_summary

# --- Paramètres ---
# Le chemin racine où se trouvent les données des différentes classes.
# IMPORTANT: Assurez-vous que ce chemin est correct et accessible.
DATA_ROOT = r"G:\Mon Drive\MyIA\Formation\Epita\2025"

# Le répertoire où les rapports de notes seront sauvegardés.
# Par défaut, nous le plaçons dans le même répertoire que les données.
OUTPUT_DIR = DATA_ROOT 

# --- Logique d'orchestration ---

def find_files(data_root):
    """
    Trouve les fichiers d'inscription et d'évaluation pour chaque classe.
    Retourne un dictionnaire où les clés sont les noms des classes.
    """
    class_files = {}

    # Mapper les noms de classe trouvés dans les fichiers d'évaluation
    # aux mots-clés à rechercher dans les fichiers d'inscription.
    class_to_registration_keyword = {
        "IASY": "IA Symbolique",
        "PrCon": "PrCon"
    }

    # Trouve tous les fichiers d'évaluation
    evaluation_files = glob.glob(os.path.join(data_root, "*Evaluations*.csv"))
    if not evaluation_files:
        print("Erreur: Aucun fichier d'évaluation (*Evaluations*.csv) n'a été trouvé.")
        return {}

    # Trouve tous les fichiers d'inscription
    all_registration_files = glob.glob(os.path.join(data_root, "*Inscription*.csv"))
    if not all_registration_files:
        print("Erreur: Aucun fichier d'inscription (*Inscription*.csv) n'a été trouvé.")
        return {}

    for eval_file in evaluation_files:
        filename = os.path.basename(eval_file)
        
        class_name = None
        if "IASY" in filename:
            class_name = "IASY"
        elif "PCon" in filename:
            class_name = "PrCon"
        else:
            print(f"Info: Fichier d'évaluation ignoré car il ne contient ni 'IASY' ni 'PCon': {filename}")
            continue

        if class_name in class_files:
            continue # Déjà traité

        # Trouve le fichier d'inscription correspondant
        keyword = class_to_registration_keyword.get(class_name)
        found_reg_file = None
        if keyword:
            for reg_file in all_registration_files:
                if keyword in reg_file:
                    found_reg_file = reg_file
                    break
        
        if found_reg_file:
            print(f"Info: Pour la classe '{class_name}', association trouvée :")
            print(f"  - Évaluation : {os.path.basename(eval_file)}")
            print(f"  - Inscription: {os.path.basename(found_reg_file)}")
            class_files[class_name] = {
                "registration": found_reg_file,
                "evaluation": eval_file
            }
        else:
            print(f"Erreur: Aucun fichier d'inscription correspondant au mot-clé '{keyword}' n'a été trouvé pour la classe '{class_name}'.")

    return class_files

def verify_and_print_excel_head(filepath):
    """
    Vérifie si le fichier Excel existe, n'est pas vide et affiche ses 5 premières lignes.
    Tente la vérification plusieurs fois pour gérer les délais de synchronisation.
    """
    import time
    print(f"\n--- Vérification du contenu du fichier : {os.path.basename(filepath)} ---")
    
    max_retries = 5
    wait_time = 3 # secondes
    
    for attempt in range(max_retries):
        if os.path.exists(filepath):
            try:
                # Ajout d'une petite pause pour s'assurer que l'écriture est terminée
                time.sleep(1)
                df = pd.read_excel(filepath)
                if df.empty:
                    print("ERREUR: Le rapport généré est un fichier vide.")
                else:
                    print("Vérification réussie. Extrait des 5 premières lignes :")
                    print(df.head(5).to_string())
                return # Sortie de la fonction si la vérification est réussie
            except Exception as e:
                print(f"ERREUR: Une exception s'est produite lors de la lecture du fichier Excel : {e}")
                return # Sortie en cas d'erreur de lecture
        
        # Si le fichier n'existe pas, on attend avant de réessayer
        print(f"Tentative {attempt + 1}/{max_retries}: Fichier non trouvé. Attente de {wait_time}s...")
        time.sleep(wait_time)

    # Si on sort de la boucle, c'est que toutes les tentatives ont échoué
    print("ERREUR: Le fichier de rapport n'a pas été trouvé à l'emplacement attendu après plusieurs tentatives.")


def main():
    """
    Point d'entrée du script d'orchestration.
    """
    print(f"Recherche des fichiers dans : {DATA_ROOT}")
    files_to_process = find_files(DATA_ROOT)

    if not files_to_process:
        print("Aucune classe à traiter. Vérifiez les noms de vos fichiers.")
        return

    print(f"Classes à traiter : {', '.join(files_to_process.keys())}")

    # --- Pré-chargement de tous les étudiants pour la validation croisée ---
    all_students = []
    print("\n--- Pré-chargement des listes d'étudiants ---")
    for class_name, paths in files_to_process.items():
        try:
            print(f"Chargement des inscrits pour la classe '{class_name}'...")
            all_students.extend(load_student_records(paths["registration"]))
        except Exception as e:
            print(f"ERREUR CRITIQUE lors du chargement de {paths['registration']}: {e}")
            return
    print(f"Total de {len(all_students)} étudiants chargés pour la validation.")

    for class_name, paths in files_to_process.items():
        print(f"\n--- Lancement du traitement pour la classe : {class_name} ---")
        # Récupérer l'objet de projet traité
        project_evaluation = process_grades(
            registration_file=paths["registration"],
            evaluation_file=paths["evaluation"],
            output_dir=OUTPUT_DIR,
            class_name=class_name,
            all_students=all_students # Passer la liste complète
        )

        # Générer le rapport qualitatif si le traitement a réussi
        if project_evaluation:
            generate_qualitative_summary(project_evaluation, class_name)

        # ÉTAPE DE VÉRIFICATION
        output_filepath = os.path.join(OUTPUT_DIR, f"rapport_notes_{class_name}.xlsx")
        verify_and_print_excel_head(output_filepath)


    print("\n--- Tous les traitements sont terminés. ---")

if __name__ == "__main__":
    main()