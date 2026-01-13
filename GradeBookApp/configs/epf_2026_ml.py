"""
Configuration EPF MIS (MSMIS5IN11) - Machine Learning
======================================================

Wrapper de configuration pour la classe EPF MIS 2026.
Ce fichier définit la configuration spécifique et utilise gradebook_core.run_pipeline()
"""

from pathlib import Path

# Configuration spécifique EPF MIS
CONFIG = {
    'nom_classe': 'EPF MIS 2026 - Machine Learning',
    
    # Chemins des fichiers
    'inscriptions_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MIS\Projet -MSMIS5IN11 - Inscription.xlsx - Sheet1.csv",
    'evaluations_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MIS\EPF - 2025 - MSMIS5IN11 - IA probabiliste et machine learning (réponses) - Réponses au formulaire 1.csv",
    'output_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MIS\Notes_Finales_EPF_MIS_2026_V3.xlsx",
    
    # Mapping des colonnes du CSV d'inscription
    'column_mapping': {
        "Prénom": "prenom",
        "Nom de famille": "nom",
        "Sujet": "sujet_projet_1"
    },
    
    # Paramètres de redressement statistique
    'target_mean': 15.5,
    'target_std': 2.0,
    
    # Paramètres de pondération
    'teacher_weight': 1.0,  # 50%/50% prof/étudiants
    'professor_email': 'jsboige@gmail.com',
    
    # Groupes blacklistés (aucun pour MIS)
    'blacklisted_groups': []
}


if __name__ == '__main__':
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from gradebook import run_pipeline
    run_pipeline(CONFIG)
