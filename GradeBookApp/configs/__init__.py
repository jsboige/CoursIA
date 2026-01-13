"""
Configurations pour les différentes classes
===========================================

Ce package contient les configurations spécifiques pour chaque classe.
Chaque configuration est un module autonome qui peut être exécuté directement.

Configurations disponibles:
- epf_2026_ml.py      : EPF MIS 2026 - Machine Learning (MSMIS5IN11)
- epf_2026_genai.py   : EPF GenAI 2026 - IA Générative et Chatbots (MSMIN5IN52)

Exemple d'utilisation:
    python -m GradeBookApp.configs.epf_2026_ml
    ou
    cd GradeBookApp/configs && python epf_2026_ml.py
"""

__version__ = '1.0.0'
__all__ = ['epf_2026_ml', 'epf_2026_genai']
