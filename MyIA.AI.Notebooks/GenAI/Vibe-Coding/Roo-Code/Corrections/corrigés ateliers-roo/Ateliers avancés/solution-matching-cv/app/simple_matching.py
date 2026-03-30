import pandas as pd

def _preprocess_simple_data(consultants_df, jobs_df):
    """
    Valide et nettoie les dataframes pour le matching simple.
    """
    required_consultant_cols = ['Nom', 'Poste', 'Compétences']
    for col in required_consultant_cols:
        if col not in consultants_df.columns:
            raise ValueError(f"Colonne '{col}' manquante dans les données consultants.")

    required_job_cols = ['Titre', 'Compétences clés']
    for col in required_job_cols:
        if col not in jobs_df.columns:
            raise ValueError(f"Colonne '{col}' manquante dans les données jobs.")
            
    consultants_df.fillna('', inplace=True)
    jobs_df.fillna('', inplace=True)
    
    # Assurer la présence d'IDs uniques pour l'harmonisation
    if 'ID' not in consultants_df.columns:
        consultants_df['ID'] = consultants_df.index
    consultants_df['consultant_id'] = 'consultant_' + consultants_df['ID'].astype(str)

    if 'ID' not in jobs_df.columns:
        jobs_df['ID'] = jobs_df.index
    jobs_df['job_id'] = 'job_' + jobs_df['ID'].astype(str)
        
    return consultants_df, jobs_df

def run_simple_matching(consultants_df, jobs_df):
    """
    Exécute le processus complet de matching simple.
    """
    try:
        # Il est crucial de travailler sur des copies pour éviter les effets de bord
        consultants_df_processed, jobs_df_processed = _preprocess_simple_data(
            consultants_df.copy(), jobs_df.copy()
        )
        return perform_matching(consultants_df_processed, jobs_df_processed)

    except Exception as e:
        print(f"Erreur lors de l'exécution du matching simple : {e}")
        # Renvoyer un DataFrame vide en cas d'erreur pour maintenir la cohérence
        return pd.DataFrame()

def perform_matching(consultants_df, jobs_df):
    """
    Exécute un matching simple basé sur la recherche de mots-clés entre 
    les compétences des consultants et les compétences requises pour les postes.
    """
    results = []

    for _, job in jobs_df.iterrows():
        # Gère le cas où 'Compétences clés' n'est pas une chaîne de caractères
        job_skills_str = job['Compétences clés'] if isinstance(job['Compétences clés'], str) else ""
        job_skills = [skill.strip().lower() for skill in job_skills_str.split(',') if skill.strip()]
        
        for _, consultant in consultants_df.iterrows():
            # Gère le cas où 'Compétences' n'est pas une chaîne de caractères (ex: NaN)
            competences = consultant['Compétences'] if isinstance(consultant['Compétences'], str) else ""
            consultant_skills = [skill.strip().lower() for skill in competences.split(',') if skill.strip()]
            
            # Calcule le nombre de compétences communes
            common_skills = set(job_skills) & set(consultant_skills)
            score = len(common_skills)
            
            if score > 0:
                results.append({
                    "job_id": job['job_id'],
                    "job_title": job['Titre'],
                    "consultant_id": consultant['consultant_id'],
                    "consultant_name": consultant['Nom'],
                    "matching_score": score,
                    "common_skills": ", ".join(common_skills)
                })

    if not results:
        return pd.DataFrame()

    # Logique d'assignation unique
    all_matches = pd.DataFrame(results)
    all_matches.sort_values(by='matching_score', ascending=False, inplace=True)

    final_matches = []
    assigned_consultants = set()
    assigned_jobs = set()

    for _, match in all_matches.iterrows():
        if match['consultant_id'] not in assigned_consultants and match['job_id'] not in assigned_jobs:
            final_matches.append(match)
            assigned_consultants.add(match['consultant_id'])
            assigned_jobs.add(match['job_id'])
            
    if not final_matches:
        return pd.DataFrame()

    final_df = pd.DataFrame(final_matches)
    
    # Sélectionner et ordonner les colonnes pour l'affichage final
    final_columns = ['job_id', 'job_title', 'consultant_id', 'consultant_name', 'matching_score', 'common_skills']
    return final_df[final_columns]