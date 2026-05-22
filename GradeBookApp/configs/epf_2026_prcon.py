"""
Configuration EPITA SCIA 2026 - Programmation par Contraintes (PrCon)
====================================================================

Wrapper de configuration pour la notation collegiale du projet PrCon
(soutenances 18 + 22 mai 2026, EPIC #927 Phase 3).

Modele identique aux configs EPF (notation 50% prof / 50% etudiants,
redressement statistique, bonus/malus selon la taille du groupe).

PREREQUIS D'EXECUTION (deux exports manuels obligatoires)
---------------------------------------------------------
Le pipeline lit des CSV **separes par des virgules** (gradebook.load_*
utilise pandas read_csv avec delimiter=','). Or les sources actuelles ne
sont pas dans ce format. Avant de lancer ce script, exporter en CSV
virgule (l'export par defaut de Google Sheets/Forms est deja en virgule) :

1. EVALUATIONS (le blocage principal) :
   "Epita - 2026 - PrCon - Evaluations (reponses)" est aujourd'hui un
   pointeur .gsheet (188 octets), PAS un CSV. L'exporter en CSV virgule
   sous le nom 'evaluations_path' ci-dessous.

2. INSCRIPTIONS :
   La source la plus recente est 'SCIA-2026-Inscription-PrCon.xlsx'
   (22 mai). Le CSV existant 'SCIA-2026-Inscription-PrCon-2.csv' (18 mai)
   est separe par des POINTS-VIRGULES et ne se chargera pas tel quel.
   Re-exporter l'inscription a jour en CSV virgule sous 'inscriptions_path'.

Tant que ces deux fichiers ne sont pas presents, run_pipeline() s'arrete
proprement avec un message "Fichier introuvable" (pas de crash).

NOTES DE NOTATION (verifiees 2026-05-23)
----------------------------------------
- Taille de groupe observee dans l'inscription : 1 a 4 (max = 4, 31 sujets
  distincts). Le bareme par defaut de gradebook.py
  {1:+3, 2:+1, 3:0, 4:-1} couvre donc exactement tous les groupes reels ;
  aucun override n'est necessaire. (Si un groupe de 5/6 apparaissait apres
  re-export, le defaut donnerait -2 ; le bareme PrCon voudrait -2 quint /
  -3 sext : il faudrait alors etendre group_size_adjustments dans
  gradebook.py.)
- L'inscription liste 31 sujets ; le brief de handoff mentionnait ~34
  groupes. Reconcilier (groupes non inscrits, ou sujets du formulaire
  d'eval absents de l'inscription) avant transmission des notes.
- Chaque groupe DOIT avoir une ligne d'evaluation prof (email ci-dessous)
  sinon la note collegiale du groupe est incomplete. Verifier la
  couverture prof avant export final.
- Caveats par groupe (plagiat, projet non note, etc.) : voir le document
  de revue 'EPITA-2026-PrCon-Review.md' (meme dossier G-drive). A integrer
  manuellement, ce n'est pas du ressort de ce wrapper.
"""

from pathlib import Path

# Dossier G-drive de la promo SCIA 2026 PrCon
_GDRIVE = r"G:\Mon Drive\MyIA\Formation\Epita\2026"

# Configuration specifique EPITA SCIA 2026 PrCon
CONFIG = {
    'nom_classe': 'EPITA SCIA 2026 - Programmation par Contraintes',

    # Chemins des fichiers (a produire par export CSV virgule, cf docstring)
    'inscriptions_path': rf"{_GDRIVE}\SCIA-2026-Inscription-PrCon-export.csv",
    'evaluations_path': rf"{_GDRIVE}\Epita - 2026 - PrCon - Evaluations (reponses).csv",
    'output_path': rf"{_GDRIVE}\Notes_Finales_PrCon_2026.xlsx",

    # Mapping des colonnes du CSV d'inscription
    # (verifie sur l'en-tete reel : F;Prenom;Nom;Mail;ID;Ordre de passage;Sujet...)
    'column_mapping': {
        "Prenom": "prenom",
        "Nom": "nom",
        "Sujet Projet de Programmation par Contrainte": "sujet_projet_1"
    },

    # Parametres de redressement statistique
    'target_mean': 14.5,
    'target_std': 2.0,

    # Parametres de ponderation
    'teacher_weight': 1.0,  # 50%/50% prof/etudiants
    'professor_email': 'jsboige@gmail.com',

    # Groupes blacklistes (doublons connus). Aucun pour PrCon a ce jour.
    'blacklisted_groups': []
}


if __name__ == '__main__':
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from gradebook import run_pipeline
    run_pipeline(CONFIG)
