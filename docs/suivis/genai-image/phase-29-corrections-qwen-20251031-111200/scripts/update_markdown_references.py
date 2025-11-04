#!/usr/bin/env python3
"""
Script simple de mise à jour des références dans les fichiers markdown uniquement.
Corrige les références aux scripts renommés avec tirets → underscores.

Auteur: Roo AI Assistant
Date: 2025-11-03
Phase: 29 - Corrections Critiques
"""

import os
from pathlib import Path

def update_markdown_references():
    """Met à jour les références dans les fichiers markdown uniquement"""
    print("🔄 MISE À JOUR RÉFÉRENCES MARKDOWN SEULEMENT")
    print("=" * 50)
    
    # Mapping des renommages (ancien nom → nouveau nom)
    replacements = {
        "setup-complete-qwen": "setup_complete_qwen",
        "test-comfyui-auth-simple": "test_comfyui_auth_simple",
        "test-comfyui-image-simple": "test_comfyui_image_simple",
    }
    
    # Répertoire racine du projet
    root_dir = Path(".")
    
    updated_files = []
    errors = []
    
    print("🔍 Recherche des fichiers markdown à traiter...")
    
    # Parcourir uniquement les fichiers markdown
    for file_path in root_dir.rglob("*.md"):
        if not file_path.is_file():
            continue
            
        # Ignorer certains répertoires
        if any(skip_dir in str(file_path) for skip_dir in [
            ".git", "__pycache__", "node_modules", ".venv", "venv",
            ".secrets", "env", "dist", "build"
        ]):
            continue
            
        try:
            # Lire le contenu du fichier
            content = file_path.read_text(encoding='utf-8')
            original_content = content
            
            # Appliquer les remplacements
            for old_name, new_name in replacements.items():
                content = content.replace(old_name, new_name)
            
            # Si le contenu a changé, écrire le fichier
            if content != original_content:
                file_path.write_text(content, encoding='utf-8')
                updated_files.append(str(file_path))
                print(f"✅ Mis à jour: {file_path}")
                
        except Exception as e:
            errors.append(f"{file_path}: {e}")
            print(f"❌ Erreur traitement {file_path}: {e}")
    
    # Résumé
    print("\n" + "=" * 50)
    print("📊 RÉSUMÉ DE LA MISE À JOUR")
    print("=" * 50)
    print(f"✅ Fichiers mis à jour: {len(updated_files)}")
    print(f"❌ Erreurs: {len(errors)}")
    
    if updated_files:
        print("\n📝 Fichiers modifiés:")
        for file_path in updated_files:
            print(f"  - {file_path}")
    
    if errors:
        print("\n🚨 Erreurs rencontrées:")
        for error in errors:
            print(f"  - {error}")
    
    print(f"\n🎯 MISE À JOUR TERMINÉE: {len(updated_files)} fichiers markdown corrigés")
    return len(updated_files) > 0

if __name__ == "__main__":
    success = update_markdown_references()
    exit(0 if success else 1)