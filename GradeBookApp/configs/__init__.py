"""
Configurations de notation — DEPLACEES SUR GDRIVE (depot agnostique des ecoles)
==============================================================================

Les configs par cohorte (notes, emails etudiants, overrides, ajustements) sont
des donnees PRIVEES. Elles ne vivent plus dans ce depot public : elles sont sur
Google Drive, point d'entree unique de tout le contenu specifique aux ecoles :

    G:\\Mon Drive\\MyIA\\Formation\\<ecole>\\<annee>\\grading\\

Le depot ne conserve que le MOTEUR agnostique des ecoles :
    - gradebook.py       : pipeline de notation (collegiale, redressement, multi-epreuve)
    - run_grading.py     : orchestrateur historique

Chaque config sur GDrive resout le moteur via la variable d'environnement
COURSIA_ROOT (fallback D:\\CoursIA) :

    import sys, os
    from pathlib import Path
    sys.path.insert(0, str(Path(os.environ.get("COURSIA_ROOT", r"D:\\CoursIA")) / "GradeBookApp"))
    from gradebook import run_pipeline

Exemple d'execution (depuis le dossier grading sur GDrive) :
    cd "G:\\Mon Drive\\MyIA\\Formation\\EPF\\2026\\grading"
    python epf_2026_ml.py

Cf docs/reference/ece-grading.md et docs/reference/esgf-grading.md pour le meme
schema applique aux cohortes ECE et ESGF.
"""

__version__ = '2.0.0'
__all__ = []  # configs deplacees sur GDrive (cf docstring)
