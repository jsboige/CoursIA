#!/usr/bin/env python3
"""
Script Transient 09 - Diagnostic Bind Mount WSL + Force Update
Identifie le fichier RÉEL que Docker monte et force la synchronisation

Auteur: Script transient Phase 29
Date: 2025-11-01 23:29:00
"""

import sys
import subprocess
from pathlib import Path

print("=" * 70)
print("🔍 DIAGNOSTIC CRITIQUE BIND MOUNT WSL")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : LECTURE HASH WINDOWS
# ============================================================================
print("\n📄 ÉTAPE 1/6 : Hash Windows actuel")

token_file_win = Path(".secrets/qwen-api-user.token")
if token_file_win.exists():
    with open(token_file_win, 'r', encoding='utf-8') as f:
        hash_win = f.read().strip()
    print(f"✅ Hash Windows: {hash_win}")
    print(f"   Truncated  : {hash_win[:30]}...{hash_win[-20:]}")
else:
    print("❌ Fichier Windows introuvable")
    sys.exit(1)

# ============================================================================
# ÉTAPE 2 : VÉRIFICATION FICHIER WSL QUE DOCKER MONTE
# ============================================================================
print("\n🐧 ÉTAPE 2/6 : Vérification fichier WSL monté par Docker")

# Le docker-compose.yml monte ../../.secrets/qwen-api-user.token
# Depuis /home/jesse/SD/workspace/comfyui-qwen, cela pointe vers :
# /home/jesse/SD/workspace/.secrets/qwen-api-user.token

wsl_token_path = "/home/jesse/SD/workspace/.secrets/qwen-api-user.token"

result = subprocess.run(
    ["wsl", "bash", "-c", f"cat {wsl_token_path}"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    hash_wsl = result.stdout.strip()
    print(f"✅ Hash WSL trouvé: {hash_wsl}")
    print(f"   Truncated     : {hash_wsl[:30]}...{hash_wsl[-20:]}")
    
    if hash_wsl == hash_win:
        print("✅ Hash WSL = Hash Windows → SYNCHRONISÉ")
        sync_needed = False
    else:
        print("❌ Hash WSL ≠ Hash Windows → DÉSYNCHRONISATION DÉTECTÉE")
        print(f"   WSL    : {hash_wsl[:40]}...")
        print(f"   Windows: {hash_win[:40]}...")
        sync_needed = True
else:
    print(f"❌ Impossible lire fichier WSL: {result.stderr}")
    print("⚠️ Le fichier WSL n'existe peut-être pas")
    sync_needed = True

# ============================================================================
# ÉTAPE 3 : FORCE UPDATE FICHIER WSL
# ============================================================================
if sync_needed:
    print("\n🔧 ÉTAPE 3/6 : Force update fichier WSL")
    
    # Méthode sécurisée : écrire dans fichier temp local puis copier
    temp_file = Path("temp_hash.txt")
    with open(temp_file, 'w', encoding='utf-8', newline='\n') as f:
        f.write(hash_win)
    # Convertir path Windows vers WSL avec format correct
    temp_abs = str(temp_file.absolute()).replace("\\", "/")
    result = subprocess.run(
        ["wsl", "wslpath", "-a", temp_abs],
        capture_output=True,
        text=True
    )
    
    if result.returncode == 0:
        wsl_temp_path = result.stdout.strip()
        print(f"✅ Fichier temp WSL: {wsl_temp_path}")
        
        # Créer répertoire .secrets dans WSL si nécessaire
        subprocess.run(
            ["wsl", "bash", "-c", "mkdir -p /home/jesse/SD/workspace/.secrets"],
            capture_output=True
        )
        
        # Copier le fichier temp vers la destination finale
        result = subprocess.run(
            ["wsl", "bash", "-c", f"cat {wsl_temp_path} > {wsl_token_path}"],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print(f"✅ Hash écrit dans WSL: {wsl_token_path}")
        else:
            print(f"❌ Erreur écriture WSL: {result.stderr}")
            sys.exit(1)
    else:
        print(f"❌ Erreur wslpath: {result.stderr}")
        sys.exit(1)
    
    # Vérification post-écriture
    result = subprocess.run(
        ["wsl", "bash", "-c", f"cat {wsl_token_path}"],
        capture_output=True,
        text=True
    )
    
    if result.returncode == 0:
        hash_wsl_post = result.stdout.strip()
        if hash_wsl_post == hash_win:
            print("✅ VÉRIFICATION RÉUSSIE : Hash WSL = Hash Windows")
        else:
            print("❌ VÉRIFICATION ÉCHOUÉE : Hash WSL ≠ Hash Windows")
            print(f"   Attendu: {hash_win}")
            print(f"   Obtenu : {hash_wsl_post}")
            sys.exit(1)
else:
    print("\n⏭️ ÉTAPE 3/6 : Synchronisation WSL non nécessaire")

# ============================================================================
# ÉTAPE 4 : ARRÊT DOCKER
# ============================================================================
print("\n🛑 ÉTAPE 4/6 : Arrêt Docker")

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
# ÉTAPE 5 : REDÉMARRAGE DOCKER
# ============================================================================
print("\n🚀 ÉTAPE 5/6 : Redémarrage Docker")

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
# ÉTAPE 6 : VÉRIFICATION FINALE LOGS DOCKER
# ============================================================================
print("\n📋 ÉTAPE 6/6 : Vérification hash dans logs Docker")

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
        print(f"🔑 Hash Docker: {hash_docker[:30]}...{hash_docker[-20:]}")
        
        if hash_docker == hash_win:
            print("✅ ✅ ✅ SUCCÈS COMPLET : Hash Docker = Hash Windows ✅ ✅ ✅")
            print("\n" + "=" * 70)
            print("🎉 MISSION ACCOMPLIE - SYNCHRONISATION RÉUSSIE")
            print("=" * 70)
            sys.exit(0)
        else:
            print("❌ ÉCHEC : Hash Docker ≠ Hash Windows")
            print(f"   Docker : {hash_docker[:40]}...")
            print(f"   Windows: {hash_win[:40]}...")
            print("\n🔍 Le bind mount ne fonctionne pas comme attendu")
            sys.exit(1)
else:
    print("❌ Impossible récupérer logs Docker")
    sys.exit(1)