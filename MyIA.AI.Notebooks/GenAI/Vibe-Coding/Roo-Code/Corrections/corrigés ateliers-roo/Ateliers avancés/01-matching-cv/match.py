import pandas as pd
import re

# Étape 2: Chargement et Prétraitement des Données
def load_data(consultants_path, jobs_path):
    """Charge les données des consultants et des fiches de poste."""
    consultants_df = pd.read_csv(consultants_path)
    jobs_df = pd.read_csv(jobs_path)
    return consultants_df, jobs_df

def normalize_text(text):
    """Met le texte en minuscules et supprime la ponctuation."""
    if not isinstance(text, str):
        return ""
    text = text.lower()
    # Supprime toute la ponctuation et la remplace par des espaces
    text = re.sub(r'[^\w\s]', ' ', text)
    return text


# Étape 3: Définition des Mots-clés et Extraction
LEXICON = ['python', 'java', 'sql', 'gestion de projet', 'agile', 'data science', 'machine learning', 'api', 'react', 'angular', 'devops']

def extract_keywords(text, lexicon):
    """Extrait les mots-clés du lexique trouvés dans un texte."""
    if not isinstance(text, str):
        return set()
    
    normalized_text = normalize_text(text)
    
    found_keywords = set()
    for keyword in lexicon:
        # Utilise une expression régulière pour trouver le mot-clé comme un mot entier
        if re.search(r'\b' + re.escape(keyword) + r'\b', normalized_text):
            found_keywords.add(keyword)
    return found_keywords


# Étape 4: Implémentation de la Logique de Matching
def main():
    """Fonction principale pour orchestrer le matching."""
    # Fichiers source
    consultants_file = 'ateliers/data_metier_csv/Base consultants.csv'
    jobs_file = 'ateliers/data_metier_csv/Fiches de poste client.csv'
    output_file = 'exercice-1-v2/results.csv'

    # Charger les données
    consultants_df, jobs_df = load_data(consultants_file, jobs_file)

    # Normaliser les colonnes textuelles pertinentes
    # Normaliser les colonnes textuelles pertinentes
    consultants_df['normalized_skills'] = consultants_df['Compétences'].apply(normalize_text)
    jobs_df['normalized_description'] = jobs_df['Description brute'].apply(normalize_text)
    jobs_df['normalized_skills_cles'] = jobs_df['Compétences clés'].apply(normalize_text)


    results = []
    
    # Itérer sur les fiches de poste
    for _, job_row in jobs_df.iterrows():
        job_id = job_row['Titre']
        job_keywords_desc = extract_keywords(job_row['normalized_description'], LEXICON)
        job_keywords_cles = extract_keywords(job_row['normalized_skills_cles'], LEXICON)
        job_keywords = job_keywords_desc.union(job_keywords_cles)

        # Itérer sur les consultants
        for _, consultant_row in consultants_df.iterrows():
            consultant_id = consultant_row['Nom']
            consultant_keywords = extract_keywords(consultant_row['normalized_skills'], LEXICON)
            
            # Calculer le score
            match_score = len(job_keywords.intersection(consultant_keywords))
            
            # Stocker le résultat
            if match_score > 0: # Optionnel: ne stocker que les matchs pertinents
                results.append({
                    'consultant_id': consultant_id,
                    'job_id': job_id,
                    'match_score': match_score
                })

    # Étape 5: Génération du Fichier de Résultats
    results_df = pd.DataFrame(results)
    results_df.to_csv(output_file, index=False)
    print(f"Le fichier de résultats a été généré : {output_file}")

if __name__ == "__main__":
    main()