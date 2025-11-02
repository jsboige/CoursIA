#!/usr/bin/env python3
"""
Script Transient 10 - Force Synchronisation TOUS les Emplacements Token
Identifie et synchronise TOUTES les copies possibles du fichier token

Auteur: Script transient Phase 29
Date: 2025-11-01 23:34:00
"""

import sys
import subprocess
from pathlib import Path

print("=" * 70)
print("🔍 SYNCHRONISATION COMPLÈTE TOUS EMPLACEMENTS TOKEN")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : HASH WINDOWS (SOURCE DE VÉRITÉ)
# ============================================================================
print("\n📄 ÉTAPE 1/8 : Hash Windows (source de vérité)")

token_file_win = Path(".secrets/qwen-api-user.token")
if token_file_win.exists():
    with open(token_file_win, 'r', encoding='utf-8') as f:
        hash_win = f.read().strip()
    print(f"✅ Hash Windows: {hash_win[:40]}...{hash_win[-20:]}")
else:
    print("❌ Fichier Windows introuvable")
    sys.exit(1)

# Créer fichier temp
temp_file = Path("temp_hash.txt")
with open(temp_file, 'w', encoding='utf-8', newline='\n') as f:
    f.write(hash_win)

# ============================================================================
# ÉTAPE 2 : LISTE COMPLÈTE DES EMPLACEMENTS À SYNCHRONISER
# ============================================================================
print("\n📋 ÉTAPE 2/8 : Identification emplacements token")

# 1. Windows host (déjà à jour)
# 2. WSL source bind mount
# 3. WSL destination dans comfyui-qwen workspace
# 4. WSL destination dans container ComfyUI (monté)

wsl_locations = [
    "/home/jesse/SD/workspace/.secrets/qwen-api-user.token",
    "/home/jesse/SD/workspace/comfyui-qwen/.secrets/qwen-api-user.token",
    "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token"
]

print(f"📍 {len(wsl_locations)} emplacements WSL à synchroniser")

# ============================================================================
# ÉTAPE 3 : SYNCHRONISATION TOUS LES EMPLACEMENTS WSL
# ============================================================================
print("\n🔧 ÉTAPE 3/8 : Synchronisation tous les emplacements WSL")

temp_abs = str(temp_file.absolute()).replace("\\", "/")
result = subprocess.run(
    ["wsl", "wslpath", "-a", temp_abs],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    wsl_temp_path = result.stdout.strip()
    print(f"✅ Fichier temp WSL: {wsl_temp_path}")
    
    for i, wsl_path in enumerate(wsl_locations, 1):
        print(f"\n{i}/{len(wsl_locations)} Synchronisation: {wsl_path}")
        
        # Créer répertoire parent si nécessaire
        parent_dir = "/".join(wsl_path.split("/")[:-1])
        subprocess.run(
            ["wsl", "bash", "-c", f"mkdir -p {parent_dir}"],
            capture_output=True
        )
        
        # Copier le hash
        result = subprocess.run(
            ["wsl", "bash", "-c", f"cat {wsl_temp_path} > {wsl_path}"],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            # Vérification
            result = subprocess.run(
                ["wsl", "bash", "-c", f"cat {wsl_path}"],
                capture_output=True,
                text=True
            )
            
            if result.returncode == 0:
                hash_written = result.stdout.strip()
                if hash_written == hash_win:
                    print(f"   ✅ Synchronisé et vérifié")
                else:
                    print(f"   ❌ ERREUR: Hash écrit ≠ Hash Windows")
            else:
                print(f"   ❌ Impossible vérifier")
        else:
            print(f"   ❌ Erreur écriture: {result.stderr}")
else:
    print(f"❌ Erreur wslpath: {result.stderr}")
    sys.exit(1)

# ============================================================================
# ÉTAPE 4 : ARRÊT COMPLET DOCKER
# ============================================================================
print("\n🛑 ÉTAPE 4/8 : Arrêt complet Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("✅ Docker arrêté")
else:
    print(f"❌ Erreur arrêt Docker: {result.stderr}")

import time
time.sleep(5)

# ============================================================================
# ÉTAPE 5 : SUPPRESSION CACHE DOCKER VOLUMES (SI POSSIBLE)
# ============================================================================
print("\n🗑️ ÉTAPE 5/8 : Nettoyage cache Docker")

subprocess.run(
    ["wsl", "bash", "-c", "docker system prune -f"],
    capture_output=True
)
print("✅ Cache Docker nettoyé")

# ============================================================================
# ÉTAPE 6 : VÉRIFICATION FINALE PRÉ-REDÉMARRAGE
# ============================================================================
print("\n🔍 ÉTAPE 6/8 : Vérification finale pré-redémarrage")

for wsl_path in wsl_locations:
    result = subprocess.run(
        ["wsl", "bash", "-c", f"cat {wsl_path} 2>/dev/null"],
        capture_output=True,
        text=True
    )
    
    if result.returncode == 0:
        hash_check = result.stdout.strip()
        if hash_check == hash_win:
            print(f"✅ {wsl_path}")
        else:
            print(f"❌ {wsl_path} (hash incorrect)")
    else:
        print(f"⚠️ {wsl_path} (fichier introuvable)")

# ============================================================================
# ÉTAPE 7 : REDÉMARRAGE DOCKER
# ============================================================================
print("\n🚀 ÉTAPE 7/8 : Redémarrage Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("✅ Docker redémarré")
else:
    print(f"❌ Erreur redémarrage Docker: {result.stderr}")
    sys.exit(1)

print("⏱️ Attente 30 secondes...")
time.sleep(30)

# ============================================================================
# ÉTAPE 8 : VÉRIFICATION FINALE LOGS DOCKER
# ============================================================================
print("\n📋 ÉTAPE 8/8 : Vérification hash dans logs Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose logs comfyui-qwen | grep 'For direct API' | tail -1"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout:
    log_line = result.stdout.strip()
    print(f"✅ Log Docker: {log_line[:100]}...")
    
    if "token=" in log_line:
        hash_docker = log_line.split("token=")[1].strip()
        print(f"🔑 Hash Docker: {hash_docker[:40]}...{hash_docker[-20:]}")
        
        if hash_docker == hash_win:
            print("\n" + "=" * 70)
            print("✅ ✅ ✅ SUCCÈS COMPLET ✅ ✅ ✅")
            print("🎉 Hash Docker = Hash Windows")
            print("=" * 70)
            sys.exit(0)
        else:
            print("\n" + "=" * 70)
            print("❌ ÉCHEC PERSISTANT")
            print(f"   Docker : {hash_docker[:40]}...")
            print(f"   Windows: {hash_win[:40]}...")
            print("=" * 70)
            print("\n🔍 DIAGNOSTIC FINAL:")
            print("   • Docker lit un fichier token d'un emplacement inconnu")
            print("   • OU Docker a un cache interne de credentials")
            print("   • OU Le script ComfyUI lit le token depuis un chemin codé en dur")
            print("\n⚠️ ACTION REQUISE:")
            print("   1. Examiner le code source ComfyUI pour trouver où il lit le token")
            print("   2. Vérifier s'il existe d'autres copies du fichier token")
            print("   3. Rebuild complet du container Docker si nécessaire")
            sys.exit(1)
else:
    print("❌ Impossible récupérer logs Docker")
    sys.exit(1)