"""
Configuration EPF Min2 (MSMIN5IN52 + MSMIN5IN43) - 2 épreuves
=============================================================

Classe Min2 avec 2 projets :
- Projet 1 : IA Exploratoire et Symbolique (Search-Symbolic) - Décembre 2025
- Projet 2 : Probabilités et Machine Learning - Janvier 2026

Note: Ali FASSY FEHRY est exclu de Min2 (déjà noté en Min1 uniquement)

Ce fichier fusionne les 2 inscriptions et lance le pipeline multi-épreuves.
"""

from pathlib import Path
import pandas as pd
import os

# Répertoire des données
DATA_DIR = r"G:\Mon Drive\MyIA\Formation\EPF\2026"

# Configuration spécifique EPF Min2
CONFIG = {
    'nom_classe': 'EPF Min2 2026 - IA Exploratoire + Probas ML',

    # Fichier d'inscription fusionné (sera créé)
    'inscriptions_path': os.path.join(DATA_DIR, 'Min2_Inscriptions_Fusionnees.csv'),

    # Définition des 2 épreuves
    'epreuves': [
        {
            'nom': 'Search-Symbolic',
            'inscription_col': 'Sujet choisi',  # Colonne pour le groupe projet 1 (attention à la casse)
            'evaluations_path': os.path.join(DATA_DIR, 'EPF - 2025 - Min2 - IA Exploratoire et symbolique (réponses) - Réponses au formulaire 1.csv'),
            'poids': 0.5,  # 50% de la note finale
            'target_mean': 14.0,
            'target_std': 2.8  # Augmenté pour avoir ~2.0 sur la moyenne finale
        },
        {
            'nom': 'Probas-ML',
            'inscription_col': 'Sujet choisi P2',  # Colonne pour le groupe projet 2
            'evaluations_path': os.path.join(DATA_DIR, 'EPF - 2025 - 2026 - MSMIN5IN43 - Min2 - Evaluations IA - Projet 2 (réponses) - Réponses au formulaire 1.csv'),
            'poids': 0.5,  # 50% de la note finale
            'target_mean': 14.0,
            'target_std': 2.8  # Augmenté pour avoir ~2.0 sur la moyenne finale
        }
    ],

    # Fichier de sortie
    'output_path': os.path.join(DATA_DIR, 'Notes_Finales_Min2_2026.xlsx'),

    # Paramètres de pondération
    'teacher_weight': 1.0,  # 50%/50% prof/étudiants
    'professor_email': 'jsboige@gmail.com',

    # Étudiants à exclure (déjà notés ailleurs)
    'excluded_students': [
        'ali.fassyfehry@epfedu.fr',  # Déjà noté en Min1
    ],

    # Groupes blacklistés (doublons connus)
    'blacklisted_groups': []
}


def create_merged_inscriptions():
    """
    Fusionne les 2 fichiers d'inscription Min2 (Projet 1 et Projet 2)
    en un seul fichier avec 2 colonnes de groupes.
    Exclut Ali FASSY FEHRY (déjà noté en Min1).
    """
    p1_path = os.path.join(DATA_DIR, 'Min2_Projet1_Inscription.xlsx - Sheet1.csv')
    p2_path = os.path.join(DATA_DIR, 'Min2_Projet2_Inscription.xlsx - Sheet1.csv')
    output_path = CONFIG['inscriptions_path']

    print(f"Fusion des inscriptions Min2...")

    # Charger les deux fichiers
    df1 = pd.read_csv(p1_path)
    df2 = pd.read_csv(p2_path)

    # Exclure Ali FASSY FEHRY
    df1 = df1[~df1['Adresse de courriel'].str.contains('fassyfehry', case=False, na=False)]
    df2 = df2[~df2['Adresse de courriel'].str.contains('fassyfehry', case=False, na=False)]

    # Renommer la colonne Sujet du P2
    df2 = df2.rename(columns={'Sujet choisi': 'Sujet choisi P2'})

    # Fusionner sur Prénom + Nom
    df1['key'] = df1['Prénom'].str.lower().str.strip() + '_' + df1['Nom de famille'].str.lower().str.strip()
    df2['key'] = df2['Prénom'].str.lower().str.strip() + '_' + df2['Nom de famille'].str.lower().str.strip()

    # Fusionner
    merged = df1.merge(df2[['key', 'Sujet choisi P2']], on='key', how='left')
    merged = merged.drop(columns=['key'])

    # Sauvegarder
    merged.to_csv(output_path, index=False)
    print(f"✅ Fichier fusionné créé : {output_path}")
    print(f"   {len(merged)} étudiants avec les 2 projets (Ali FASSY FEHRY exclu)")

    return merged


if __name__ == '__main__':
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent.parent))

    # Créer le fichier fusionné si nécessaire
    if not os.path.exists(CONFIG['inscriptions_path']):
        create_merged_inscriptions()

    from gradebook import run_multi_epreuve_pipeline
    run_multi_epreuve_pipeline(CONFIG)
