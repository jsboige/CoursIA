"""
Configuration EPF GenAI (MSMIN5IN52) - IA Générative et Chatbots
=================================================================

Wrapper de configuration pour la classe EPF GenAI 2026.
Ce fichier définit la configuration spécifique et utilise gradebook_core.run_pipeline()
"""

from pathlib import Path

# Configuration spécifique EPF GenAI
CONFIG = {
    'nom_classe': 'EPF GenAI 2026 - IA Générative et Chatbots',
    
    # Chemins des fichiers
    'inscriptions_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MSMIN5IN52 IA Générative et Chatbots\Inscriptions_Corrigees_V2.csv",
    'evaluations_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MSMIN5IN52 IA Générative et Chatbots\EPF - 2025 - Min1 - GenAI (réponses) - Réponses au formulaire 1.csv",
    'output_path': r"G:\Mon Drive\MyIA\Formation\EPF\2026\MSMIN5IN52 IA Générative et Chatbots\Notes_Finales_GenAI_V6.xlsx",
    
    # Mapping des colonnes du CSV d'inscription
    'column_mapping': {
        "Prénom": "prenom",
        "Nom de famille": "nom",
        "Projet": "sujet_projet_1"
    },
    
    # Paramètres de redressement statistique
    'target_mean': 14.0,
    'target_std': 2.0,
    
    # Paramètres de pondération
    'teacher_weight': 1.0,  # 50%/50% prof/étudiants
    'professor_email': 'jsboige@gmail.com',
    
    # Groupes blacklistés (doublons connus)
    'blacklisted_groups': [
        "projet6_TALA_SOUZA_KOUNDJO",  # Doublon de "Groupe6_AgentDeRecrutementAugmente"
    ]
}


if __name__ == '__main__':
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from gradebook import run_pipeline
    run_pipeline(CONFIG)
