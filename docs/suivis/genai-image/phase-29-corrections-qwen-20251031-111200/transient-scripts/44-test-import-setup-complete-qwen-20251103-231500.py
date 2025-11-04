#!/usr/bin/env python3
"""
Script de test pour vérifier l'import du module setup_complete_qwen.py
Fait partie de la mission : Confirmation Tests Consolidés Après Corrections
"""

import sys
import os
from datetime import datetime

def main():
    print("=" * 70)
    print("TEST D'IMPORT MODULE setup_complete_qwen.py")
    print("=" * 70)
    print(f"Timestamp : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    # Ajout du chemin du module
    sys.path.insert(0, 'scripts/genai-auth/core')
    
    try:
        import setup_complete_qwen
        print("✅ setup_complete_qwen.py : Import OK")
        
        # Vérification de la version
        version = getattr(setup_complete_qwen, 'VERSION', 'Non spécifiée')
        print(f"Version : {version}")
        
        # Liste des fonctions disponibles
        fonctions = [f for f in dir(setup_complete_qwen) if not f.startswith('_')]
        print(f"Fonctions disponibles : {len(fonctions)}")
        for func in fonctions:
            print(f"  • {func}")
        
        print()
        print("=" * 70)
        print("✅ TEST D'IMPORT RÉUSSI")
        print("=" * 70)
        
        return True
        
    except Exception as e:
        print(f"❌ Erreur import : {str(e)}")
        print()
        import traceback
        traceback.print_exc()
        
        print()
        print("=" * 70)
        print("❌ TEST D'IMPORT ÉCHOUÉ")
        print("=" * 70)
        
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)