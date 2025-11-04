#!/usr/bin/env python3
"""
Script de mise à jour des références après renommage des scripts.
Remplace toutes les références aux anciens noms de fichiers par les nouveaux.

Auteur: Roo AI Assistant
Date: 2025-11-02
Phase: 29 - Corrections Critiques
"""

import os
import re
from pathlib import Path
import sys

def update_references():
    """Met à jour toutes les références aux scripts renommés"""
    print("🔄 MISE À JOUR RÉFÉRENCES - GENAI-AUTH")
    print("=" * 50)
    
    # Mapping des renommages (ancien nom → nouveau nom)
    replacements = {
        "setup-complete-qwen": "setup_complete_qwen",
        "install-comfyui-login": "install_comfyui_login",
        "test-comfyui-auth-simple": "test_comfyui_auth_simple",
        "test-comfyui-image-simple": "test_comfyui_image_simple",
        "test-generation-image-fp8-officiel": "test_generation_image_fp8_officiel"
    }
    
    # Répertoire racine du projet
    root_dir = Path(".")
    
    if not root_dir.exists():
        print(f"❌ Erreur: Répertoire racine {root_dir} introuvable")
        return False
    
    # Extensions de fichiers à traiter
    target_extensions = [".py", ".md", ".yml", ".yaml", ".json", ".txt", ".ps1", ".sh"]
    
    updated_files = []
    errors = []
    total_files_processed = 0
    
    print("🔍 Recherche des fichiers à traiter...")
    
    # Parcourir tous les fichiers du projet
    for file_path in root_dir.rglob("*"):
        if not file_path.is_file():
            continue
            
        # Ignorer certains répertoires
        if any(skip_dir in str(file_path) for skip_dir in [
            ".git", "__pycache__", "node_modules", ".venv", "venv",
            ".secrets", "env", "dist", "build"
        ]):
            continue
            
        # Vérifier l'extension
        if file_path.suffix.lower() not in target_extensions:
            continue
            
        total_files_processed += 1
        
        try:
            # Lire le contenu du fichier
            content = file_path.read_text(encoding='utf-8')
            original_content = content
            
            # Appliquer les remplacements
            for old_name, new_name in replacements.items():
                # Remplacement direct
                content = content.replace(old_name, new_name)
                
                # Remplacement avec extension .py
                content = content.replace(f"{old_name}.py", f"{new_name}.py")
                
                # Remplacement avec chemin relatif
                content = content.replace(f"/{old_name}.py", f"/{new_name}.py")
                content = content.replace(f"\\{old_name}.py", f"\\{new_name}.py")
                
                # Remplacement dans les imports Python
                content = content.replace(f"from {old_name}", f"from {new_name}")
                content = content.replace(f"import {old_name}", f"import {new_name}")
            
            # Si le contenu a changé, écrire le fichier
            if content != original_content:
                file_path.write_text(content, encoding='utf-8')
                print(f"✅ Mis à jour: {file_path}")
                updated_files.append(str(file_path))
                
        except UnicodeDecodeError:
            # Ignorer les fichiers binaires
            continue
        except Exception as e:
            print(f"❌ Erreur traitement {file_path}: {e}")
            errors.append(f"Erreur traitement {file_path}: {e}")
    
    # Résumé
    print("\n" + "=" * 50)
    print("📊 RÉSUMÉ DE LA MISE À JOUR")
    print("=" * 50)
    
    print(f"📁 Fichiers analysés: {total_files_processed}")
    
    if updated_files:
        print(f"✅ {len(updated_files)} fichier(s) mis à jour:")
        for file_path in updated_files[:10]:  # Limiter l'affichage
            print(f"   • {file_path}")
        if len(updated_files) > 10:
            print(f"   ... et {len(updated_files) - 10} autres fichiers")
    else:
        print("ℹ️  Aucune référence trouvée à mettre à jour")
        
    if errors:
        print(f"\n❌ {len(errors)} erreur(s) rencontrée(s):")
        for error in errors[:5]:  # Limiter l'affichage
            print(f"   • {error}")
        if len(errors) > 5:
            print(f"   ... et {len(errors) - 5} autres erreurs")
        return False
    
    print(f"\n🎉 Mise à jour des références terminée avec succès!")
    return True

def main():
    """Point d'entrée principal"""
    print("🚀 DÉMARRAGE DU SCRIPT DE MISE À JOUR DES RÉFÉRENCES")
    print(f"📁 Répertoire de travail: {os.getcwd()}")
    print(f"⏰ Heure de début: {os.popen('date').read().strip()}")
    print()
    
    success = update_references()
    
    print(f"\n⏰ Heure de fin: {os.popen('date').read().strip()}")
    
    if success:
        print("✅ Script terminé avec succès")
        sys.exit(0)
    else:
        print("❌ Script terminé avec des erreurs")
        sys.exit(1)

if __name__ == "__main__":
    main()