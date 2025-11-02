#!/usr/bin/env python3
"""
Script Transient 13 - Inspection Code Source ComfyUI Authentication
Date: 2025-11-01 23:48:00
Phase: Phase 29 - Corrections Qwen ComfyUI

MISSION : Trouver où le hash bcrypt d'authentification est défini
dans le code source ComfyUI du container.

Stratégie:
1. Rechercher le hash ancien dans le code Python ComfyUI
2. Rechercher les fichiers qui gèrent l'authentification
3. Inspecter les custom nodes ComfyUI_QwenImageWanBridge
4. Vérifier les variables d'environnement du container
"""

import subprocess
import json

print("="*70)
print("🔍 INSPECTION CODE SOURCE COMFYUI - AUTHENTIFICATION")
print("="*70)

# Hash bcrypt ancien (celui que Docker charge)
HASH_ANCIEN = "$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni"
HASH_NOUVEAU = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"

# ============================================================================
# ÉTAPE 1 : RECHERCHE HASH ANCIEN DANS CODE COMFYUI
# ============================================================================
print("\n🔍 ÉTAPE 1/5 : Recherche hash ancien dans code ComfyUI")
print("-" * 70)

# Recherche du pattern "$2b$12$UDce" (début du hash)
search_pattern = "UDceblhZeEySDwVMC0ccN"
print(f"   Pattern recherché: {search_pattern}")

result = subprocess.run(
    ["wsl", "bash", "-c", 
     f"cd /home/jesse/SD/workspace/comfyui-qwen && "
     f"docker-compose exec -T comfyui-qwen bash -c "
     f"'grep -r \"{search_pattern}\" /workspace/ComfyUI/ 2>/dev/null | head -20'"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout.strip():
    print("✅ Hash ancien trouvé dans le code!")
    print(f"   Résultats:\n{result.stdout}")
else:
    print("❌ Hash ancien NOT found dans le code ComfyUI")
    print("   Le hash est peut-être stocké dans un fichier binaire ou variable d'environnement")

# ============================================================================
# ÉTAPE 2 : RECHERCHE FICHIERS AUTHENTIFICATION
# ============================================================================
print("\n🔍 ÉTAPE 2/5 : Recherche fichiers d'authentification")
print("-" * 70)

# Recherche des fichiers contenant "bcrypt" ou "auth"
result = subprocess.run(
    ["wsl", "bash", "-c",
     "cd /home/jesse/SD/workspace/comfyui-qwen && "
     "docker-compose exec -T comfyui-qwen bash -c "
     "'find /workspace/ComfyUI -name \"*.py\" -type f | xargs grep -l \"bcrypt\" 2>/dev/null | head -10'"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout.strip():
    print("✅ Fichiers avec bcrypt trouvés:")
    for file in result.stdout.strip().split('\n'):
        print(f"   📄 {file}")
else:
    print("⚠️  Aucun fichier avec 'bcrypt' trouvé")

# ============================================================================
# ÉTAPE 3 : INSPECTION CUSTOM NODE QWEN
# ============================================================================
print("\n🔍 ÉTAPE 3/5 : Inspection custom node QwenImageWanBridge")
print("-" * 70)

result = subprocess.run(
    ["wsl", "bash", "-c",
     "cd /home/jesse/SD/workspace/comfyui-qwen && "
     "docker-compose exec -T comfyui-qwen bash -c "
     "'find /workspace/ComfyUI/custom_nodes/ComfyUI_QwenImageWanBridge -name \"*.py\" -type f | head -10'"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout.strip():
    print("✅ Fichiers Python trouvés dans QwenImageWanBridge:")
    for file in result.stdout.strip().split('\n'):
        print(f"   📄 {file}")
    
    # Inspecter le fichier __init__.py
    print("\n📖 Contenu de __init__.py:")
    result = subprocess.run(
        ["wsl", "bash", "-c",
         "cd /home/jesse/SD/workspace/comfyui-qwen && "
         "docker-compose exec -T comfyui-qwen bash -c "
         "'cat /workspace/ComfyUI/custom_nodes/ComfyUI_QwenImageWanBridge/__init__.py'"],
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        print(result.stdout[:1000])
else:
    print("⚠️  Erreur lecture custom nodes")

# ============================================================================
# ÉTAPE 4 : VARIABLES D'ENVIRONNEMENT CONTAINER
# ============================================================================
print("\n🔍 ÉTAPE 4/5 : Variables d'environnement du container")
print("-" * 70)

result = subprocess.run(
    ["wsl", "bash", "-c",
     "cd /home/jesse/SD/workspace/comfyui-qwen && "
     "docker-compose exec -T comfyui-qwen bash -c 'env | grep -i \"AUTH\\|TOKEN\" | sort'"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("✅ Variables d'environnement:")
    for line in result.stdout.strip().split('\n'):
        print(f"   {line}")
else:
    print("❌ Erreur lecture variables d'environnement")

# ============================================================================
# ÉTAPE 5 : RECHERCHE FICHIER .TOKEN DANS WORKSPACE MONTÉ
# ============================================================================
print("\n🔍 ÉTAPE 5/5 : Vérification fichier token dans workspace monté")
print("-" * 70)

result = subprocess.run(
    ["wsl", "bash", "-c",
     "cd /home/jesse/SD/workspace/comfyui-qwen && "
     "docker-compose exec -T comfyui-qwen bash -c "
     "'find /workspace/ComfyUI/.secrets -name \"*token*\" -type f 2>/dev/null'"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout.strip():
    print("✅ Fichiers token trouvés dans container:")
    for file in result.stdout.strip().split('\n'):
        print(f"   📄 {file}")
    
    # Lire le contenu du fichier token
    for file in result.stdout.strip().split('\n'):
        if file.strip():
            print(f"\n📖 Contenu de {file}:")
            result_content = subprocess.run(
                ["wsl", "bash", "-c",
                 f"cd /home/jesse/SD/workspace/comfyui-qwen && "
                 f"docker-compose exec -T comfyui-qwen bash -c 'cat {file.strip()}'"],
                capture_output=True,
                text=True
            )
            if result_content.returncode == 0:
                content = result_content.stdout.strip()
                print(f"   {content[:100]}...")
                
                # Vérifier quel hash est présent
                if HASH_NOUVEAU in content:
                    print("   ✅ NOUVEAU HASH détecté!")
                elif HASH_ANCIEN in content:
                    print("   ❌ ANCIEN HASH détecté!")
                else:
                    print("   ⚠️  Hash inconnu")
else:
    print("❌ Aucun fichier token trouvé dans /workspace/ComfyUI/.secrets")

# ============================================================================
# RAPPORT FINAL
# ============================================================================
print("\n" + "="*70)
print("📊 RAPPORT FINAL - INSPECTION CODE SOURCE")
print("="*70)

print("\n🎯 Prochaines Actions Recommandées:")
print("   1. Si hash trouvé dans code Python: Modifier le fichier source")
print("   2. Si hash dans fichier .token du container: Vérifier bind mount")
print("   3. Si hash dans variable d'environnement: Modifier .env et redémarrer")
print("   4. Si aucun des cas ci-dessus: Inspecter main.py de ComfyUI")

print("\n📝 Voir rapport détaillé:")
print("   docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/16-regeneration-complete-credentials-20251101_232640.md")

print("\n" + "="*70)