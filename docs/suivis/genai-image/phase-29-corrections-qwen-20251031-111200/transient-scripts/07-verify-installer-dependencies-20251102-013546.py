#!/usr/bin/env python3
"""
Script de vérification des dépendances pour qwen-custom-nodes-installer.py
Phase 29 - Corrections Qwen ComfyUI

Vérifie que toutes les dépendances Python requises sont disponibles
avant l'exécution du script d'installation.

USAGE:
    python docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/07-verify-installer-dependencies-20251102-013546.py
"""

import sys
from pathlib import Path
from datetime import datetime

def check_imports():
    """Vérifie que tous les imports nécessaires sont disponibles."""
    
    print("=" * 80)
    print("🔍 VÉRIFICATION DÉPENDANCES - qwen-custom-nodes-installer.py")
    print("=" * 80)
    print()
    
    missing_modules = []
    successful_imports = []
    
    # Liste des modules requis
    required_modules = [
        ("os", "os"),
        ("sys", "sys"),
        ("subprocess", "subprocess"),
        ("json", "json"),
        ("time", "time"),
        ("requests", "requests"),
        ("datetime", "datetime.datetime"),
        ("pathlib", "pathlib.Path"),
        ("typing", "typing.Dict, typing.List, typing.Any, typing.Optional")
    ]
    
    print("📦 Vérification des modules Python...\n")
    
    for module_name, import_path in required_modules:
        try:
            # Tester l'import
            if module_name == "typing":
                from typing import Dict, List, Any, Optional
            elif module_name == "datetime":
                from datetime import datetime
            elif module_name == "pathlib":
                from pathlib import Path
            else:
                __import__(module_name)
            
            successful_imports.append(import_path)
            print(f"  ✅ {import_path}")
            
        except ImportError as e:
            missing_modules.append((import_path, str(e)))
            print(f"  ❌ {import_path} - MANQUANT")
    
    print()
    print("=" * 80)
    
    if missing_modules:
        print("❌ VÉRIFICATION ÉCHOUÉE")
        print("=" * 80)
        print()
        print("Modules manquants:")
        for module, error in missing_modules:
            print(f"  • {module}: {error}")
        print()
        print("Action requise:")
        print("  pip install requests")
        print()
        return False
    else:
        print("✅ VÉRIFICATION RÉUSSIE")
        print("=" * 80)
        print()
        print(f"Total modules vérifiés: {len(successful_imports)}")
        print()
        print("🚀 Le script qwen-custom-nodes-installer.py peut être exécuté:")
        print("   python scripts/genai-auth/qwen-custom-nodes-installer.py")
        print()
        return True

def verify_script_exists():
    """Vérifie que le script principal existe."""
    
    print("📄 Vérification script principal...\n")
    
    script_path = Path("scripts/genai-auth/qwen-custom-nodes-installer.py")
    
    if script_path.exists():
        print(f"  ✅ {script_path}")
        print(f"  Taille: {script_path.stat().st_size} bytes")
        print()
        return True
    else:
        print(f"  ❌ {script_path} - INTROUVABLE")
        print()
        return False

def verify_credentials_files():
    """Vérifie que les fichiers de credentials existent."""
    
    print("🔑 Vérification fichiers credentials...\n")
    
    required_files = [
        ".secrets/.env.generated",
        ".secrets/qwen-api-user.token"
    ]
    
    all_exist = True
    for file_path in required_files:
        path = Path(file_path)
        if path.exists():
            print(f"  ✅ {file_path}")
        else:
            print(f"  ❌ {file_path} - MANQUANT")
            all_exist = False
    
    print()
    
    if not all_exist:
        print("⚠️  Fichiers credentials manquants - Exécuter d'abord:")
        print("   python scripts/genai-auth/resync-credentials-complete.py")
        print()
    
    return all_exist

def main():
    """Point d'entrée principal."""
    
    timestamp_start = datetime.now()
    
    # Vérifications
    script_ok = verify_script_exists()
    imports_ok = check_imports()
    credentials_ok = verify_credentials_files()
    
    # Résumé final
    print("=" * 80)
    print("📊 RÉSUMÉ VÉRIFICATION")
    print("=" * 80)
    print()
    print(f"  Script principal      : {'✅' if script_ok else '❌'}")
    print(f"  Dépendances Python    : {'✅' if imports_ok else '❌'}")
    print(f"  Fichiers credentials  : {'✅' if credentials_ok else '❌'}")
    print()
    
    all_checks_passed = script_ok and imports_ok and credentials_ok
    
    if all_checks_passed:
        print("✅ TOUTES LES VÉRIFICATIONS RÉUSSIES")
        print()
        print("Prochaine étape:")
        print("  python scripts/genai-auth/qwen-custom-nodes-installer.py")
        print()
        return 0
    else:
        print("❌ CERTAINES VÉRIFICATIONS ONT ÉCHOUÉ")
        print()
        print("Résoudre les problèmes avant d'exécuter l'installation.")
        print()
        return 1

if __name__ == "__main__":
    sys.exit(main())