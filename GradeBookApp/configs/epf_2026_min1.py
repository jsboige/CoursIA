"""
Configuration EPF Min1 (MSMIN5IN52 + MSMIN5IN43) - 2 épreuves
=============================================================

Classe Min1 avec 2 projets :
- Projet 1 : IA Exploratoire et Symbolique (Search-Symbolic) - Décembre 2025
- Projet 2 : Probabilités et Machine Learning - Janvier 2026

Ce fichier fusionne les 2 inscriptions et lance le pipeline multi-épreuves.
"""

from pathlib import Path
import pandas as pd
import os

# Répertoire des données
DATA_DIR = r"G:\Mon Drive\MyIA\Formation\EPF\2026"

# Configuration spécifique EPF Min1
CONFIG = {
    'nom_classe': 'EPF Min1 2026 - IA Exploratoire + Probas ML',

    # Fichier d'inscription fusionné (sera créé)
    'inscriptions_path': os.path.join(DATA_DIR, 'Min1_Inscriptions_Fusionnees.csv'),

    # Définition des 2 épreuves
    'epreuves': [
        {
            'nom': 'Search-Symbolic',
            'inscription_col': 'Sujet Choisi',  # Colonne pour le groupe projet 1
            'evaluations_path': os.path.join(DATA_DIR, 'EPF - 2025 - Min1 - IA Exploratoire et symbolique (réponses) - Réponses au formulaire 1.csv'),
            'poids': 0.5,  # 50% de la note finale
            'target_mean': 14.0,
            'target_std': 2.8  # Augmenté pour avoir ~2.0 sur la moyenne finale
        },
        {
            'nom': 'Probas-ML',
            'inscription_col': 'Sujet Choisi P2',  # Colonne pour le groupe projet 2
            'evaluations_path': os.path.join(DATA_DIR, 'EPF - 2025 - 2026 - MSMIN5IN43 - Min1 - Evaluations IA - Projet 2 (réponses) - Réponses au formulaire 1.csv'),
            'poids': 0.5,  # 50% de la note finale
            'target_mean': 14.0,
            'target_std': 2.8  # Augmenté pour avoir ~2.0 sur la moyenne finale
        }
    ],

    # Fichier de sortie
    'output_path': os.path.join(DATA_DIR, 'Notes_Finales_Min1_2026.xlsx'),

    # Paramètres de pondération
    'teacher_weight': 1.0,  # 50%/50% prof/étudiants
    'professor_email': 'jsboige@gmail.com',

    # Emails alternatifs connus (mapping email personnel -> email EPF)
    'email_aliases': {
        'safaeberrichi23@gmail.com': 'safae.berrichi@epfedu.fr',
        'brendakoundjo88@gmail.com': 'brendaaudrey.koundjonguepkap@epfedu.fr',
        'brendaaudrey.koundjonguepkap@gmail.com': 'brendaaudrey.koundjonguepkap@epfedu.fr',
    },

    # Groupes blacklistés (doublons connus)
    'blacklisted_groups': []
}


def create_merged_inscriptions():
    """
    Fusionne les 2 fichiers d'inscription Min1 (Projet 1 et Projet 2)
    en un seul fichier avec 2 colonnes de groupes.
    """
    p1_path = os.path.join(DATA_DIR, 'Min1_Projet1_Inscription.xlsx - Sheet1.csv')
    p2_path = os.path.join(DATA_DIR, 'Min1_Projet2_Inscription.xlsx - Sheet1.csv')
    output_path = CONFIG['inscriptions_path']

    print(f"Fusion des inscriptions Min1...")

    # Charger les deux fichiers
    df1 = pd.read_csv(p1_path)
    df2 = pd.read_csv(p2_path)

    # Renommer la colonne Sujet du P2
    df2 = df2.rename(columns={'Sujet Choisi': 'Sujet Choisi P2'})

    # Fusionner sur Prénom + Nom
    df1['key'] = df1['Prénom'].str.lower().str.strip() + '_' + df1['Nom de famille'].str.lower().str.strip()
    df2['key'] = df2['Prénom'].str.lower().str.strip() + '_' + df2['Nom de famille'].str.lower().str.strip()

    # Fusionner
    merged = df1.merge(df2[['key', 'Sujet Choisi P2']], on='key', how='left')
    merged = merged.drop(columns=['key'])

    # Sauvegarder
    merged.to_csv(output_path, index=False)
    print(f"✅ Fichier fusionné créé : {output_path}")
    print(f"   {len(merged)} étudiants avec les 2 projets")

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
