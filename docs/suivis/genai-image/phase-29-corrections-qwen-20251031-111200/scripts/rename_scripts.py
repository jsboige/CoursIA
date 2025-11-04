#!/usr/bin/env python3
"""
Script de renommage batch pour remplacer les tirets par des underscores
dans les noms de fichiers Python du projet genai-auth.

Auteur: Roo AI Assistant
Date: 2025-11-02
Phase: 29 - Corrections Critiques
"""

import os
import re
from pathlib import Path
import sys

def rename_scripts_with_underscores():
    """Renomme tous les scripts avec tirets en underscores"""
    print("🔧 RENOMMAGE BATCH SCRIPTS - GENAI-AUTH")
    print("=" * 50)
    
    # Répertoire de base pour les scripts genai-auth
    scripts_dir = Path("scripts/genai-auth")
    
    if not scripts_dir.exists():
        print(f"❌ Erreur: Répertoire {scripts_dir} introuvable")
        return False
    
    # Liste des fichiers à renommer (identifiés manuellement)
    files_to_rename = [
        "scripts/genai-auth/core/install_comfyui_login.py",
        "scripts/genai-auth/utils/test_comfyui_auth_simple.py", 
        "scripts/genai-auth/utils/test_comfyui_image_simple.py",
        "scripts/genai-auth/utils/test_generation_image_fp8_officiel.py"
    ]
    
    renamed_files = []
    errors = []
    
    for file_path_str in files_to_rename:
        file_path = Path(file_path_str)
        
        if not file_path.exists():
            print(f"⚠️  Fichier introuvable: {file_path}")
            errors.append(f"Fichier introuvable: {file_path}")
            continue
            
        if "-" not in file_path.name:
            print(f"ℹ️  Pas de tiret dans {file_path.name}, ignoré")
            continue
            
        # Générer le nouveau nom
        new_name = file_path.name.replace("-", "_")
        new_path = file_path.parent / new_name
        
        # Vérifier si le nouveau fichier existe déjà
        if new_path.exists():
            print(f"⚠️  Le fichier de destination existe déjà: {new_path}")
            errors.append(f"Fichier de destination existe: {new_path}")
            continue
            
        try:
            # Renommage du fichier
            file_path.rename(new_path)
            print(f"✅ Renommage: {file_path.name} → {new_name}")
            renamed_files.append({
                "old_path": str(file_path),
                "new_path": str(new_path),
                "old_name": file_path.name,
                "new_name": new_name
            })
        except Exception as e:
            print(f"❌ Erreur lors du renommage de {file_path.name}: {e}")
            errors.append(f"Erreur renommage {file_path.name}: {e}")
    
    # Résumé
    print("\n" + "=" * 50)
    print("📊 RÉSUMÉ DU RENOMMAGE")
    print("=" * 50)
    
    if renamed_files:
        print(f"✅ {len(renamed_files)} fichier(s) renommé(s) avec succès:")
        for file_info in renamed_files:
            print(f"   • {file_info['old_name']} → {file_info['new_name']}")
    else:
        print("ℹ️  Aucun fichier renommé")
        
    if errors:
        print(f"\n❌ {len(errors)} erreur(s) rencontrée(s):")
        for error in errors:
            print(f"   • {error}")
        return False
    
    print(f"\n🎉 Renommage terminé avec succès!")
    return True

def main():
    """Point d'entrée principal"""
    print("🚀 DÉMARRAGE DU SCRIPT DE RENOMMAGE")
    print(f"📁 Répertoire de travail: {os.getcwd()}")
    print(f"⏰ Heure de début: {os.popen('date').read().strip()}")
    print()
    
    success = rename_scripts_with_underscores()
    
    print(f"\n⏰ Heure de fin: {os.popen('date').read().strip()}")
    
    if success:
        print("✅ Script terminé avec succès")
        sys.exit(0)
    else:
        print("❌ Script terminé avec des erreurs")
        sys.exit(1)

if __name__ == "__main__":
    main()