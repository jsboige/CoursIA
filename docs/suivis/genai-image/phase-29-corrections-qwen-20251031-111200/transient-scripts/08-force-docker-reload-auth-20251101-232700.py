#!/usr/bin/env python3
"""
Script Transient 08 - Force Redémarrage Docker Complet + Test Final
Effectue cycle down/up pour forcer rechargement volume mount + test authentification

Auteur: Script transient Phase 29
Date: 2025-11-01 23:27:00
"""

import sys
import subprocess
import time
from pathlib import Path
from datetime import datetime

print("=" * 70)
print("🔄 FORCE REDÉMARRAGE DOCKER COMPLET")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : ARRÊT COMPLET DOCKER
# ============================================================================
print("\n🛑 ÉTAPE 1/5 : Arrêt complet Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("✅ Docker arrêté avec succès")
else:
    print(f"❌ Erreur arrêt Docker: {result.stderr}")
    sys.exit(1)

print("⏱️ Attente 5 secondes...")
time.sleep(5)

# ============================================================================
# ÉTAPE 2 : VÉRIFICATION HASH WINDOWS ACTUEL
# ============================================================================
print("\n📄 ÉTAPE 2/5 : Vérification hash Windows actuel")

token_file_win = Path(".secrets/qwen-api-user.token")
if token_file_win.exists():
    with open(token_file_win, 'r', encoding='utf-8') as f:
        hash_win = f.read().strip()
    print(f"✅ Hash Windows: {hash_win[:30]}...{hash_win[-20:]}")
else:
    print("❌ Fichier token Windows introuvable")
    sys.exit(1)

# ============================================================================
# ÉTAPE 3 : REDÉMARRAGE DOCKER
# ============================================================================
print("\n🚀 ÉTAPE 3/5 : Redémarrage Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("✅ Docker redémarré avec succès")
else:
    print(f"❌ Erreur redémarrage Docker: {result.stderr}")
    sys.exit(1)

print("⏱️ Attente 30 secondes (démarrage ComfyUI)...")
time.sleep(30)

# ============================================================================
# ÉTAPE 4 : VÉRIFICATION LOGS DOCKER
# ============================================================================
print("\n📋 ÉTAPE 4/5 : Vérification hash dans logs Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose logs comfyui-qwen | grep 'For direct API' | tail -1"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout:
    log_line = result.stdout.strip()
    print(f"✅ Log trouvé: {log_line[:100]}...")
    
    if "token=" in log_line:
        hash_docker = log_line.split("token=")[1].strip()
        print(f"🔑 Hash Docker: {hash_docker[:30]}...{hash_docker[-20:]}")
        
        if hash_docker == hash_win:
            print("✅ ✅ ✅ CORRESPONDANCE PARFAITE : Hash Docker = Hash Windows ✅ ✅ ✅")
            hash_sync = True
        else:
            print("❌ DÉSYNCHRONISATION PERSISTANTE : Hash Docker ≠ Hash Windows")
            print(f"   Docker : {hash_docker[:40]}...")
            print(f"   Windows: {hash_win[:40]}...")
            hash_sync = False
    else:
        print("❌ Impossible extraire hash des logs")
        hash_sync = False
else:
    print("❌ Impossible récupérer logs Docker")
    hash_sync = False

# ============================================================================
# ÉTAPE 5 : TEST AUTHENTIFICATION
# ============================================================================
print("\n🌐 ÉTAPE 5/5 : Test authentification API")

if hash_sync:
    # Charger token brut
    env_generated = Path(".secrets/.env.generated")
    if env_generated.exists():
        with open(env_generated, 'r', encoding='utf-8') as f:
            for line in f:
                if line.startswith("QWEN_API_USER_TOKEN="):
                    token_brut = line.split('=', 1)[1].strip()
                    break
            else:
                print("❌ Token non trouvé dans .env.generated")
                token_brut = None
    else:
        print("❌ Fichier .env.generated introuvable")
        token_brut = None
    
    if token_brut:
        print(f"✅ Token brut chargé: {token_brut[:10]}...{token_brut[-10:]}")
        
        # Test curl direct (plus fiable que requests pour diagnostic)
        result = subprocess.run(
            ["curl", "-X", "GET", "-H", f"Authorization: Bearer {token_brut}", "http://localhost:8188/system_stats"],
            capture_output=True,
            text=True
        )
        
        if "cpu" in result.stdout.lower() or "memory" in result.stdout.lower():
            print("✅ ✅ ✅ AUTHENTIFICATION RÉUSSIE ✅ ✅ ✅")
            print(f"📦 Réponse API: {result.stdout[:200]}...")
            auth_success = True
        elif "401" in result.stderr or "Unauthorized" in result.stdout:
            print("❌ AUTHENTIFICATION ÉCHOUÉE (HTTP 401)")
            auth_success = False
        else:
            print(f"⚠️ Réponse inattendue:")
            print(f"   stdout: {result.stdout[:200]}")
            print(f"   stderr: {result.stderr[:200]}")
            auth_success = False
    else:
        print("❌ Impossible charger token brut")
        auth_success = False
else:
    print("⚠️ Hash désynchronisé, test authentification ignoré")
    auth_success = False

# ============================================================================
# RÉSUMÉ FINAL
# ============================================================================
print("\n" + "=" * 70)
if auth_success:
    print("🎉 MISSION COMPLÈTE - AUTHENTIFICATION FONCTIONNELLE")
    print("=" * 70)
    print(f"✅ Hash synchronisé : Docker = Windows")
    print(f"✅ Test authentification : HTTP 200")
    print(f"✅ Système prêt pour génération d'images")
    sys.exit(0)
else:
    print("❌ ÉCHEC MISSION")
    print("=" * 70)
    if not hash_sync:
        print("❌ Hash Docker ≠ Hash Windows")
        print("🔍 Cause probable: volume mount Docker ne rafraîchit pas le fichier")
        print("⚠️ ACTION REQUISE: Vérifier bind mount dans docker-compose.yml")
    else:
        print("❌ Test authentification échoué malgré hash synchronisé")
        print("🔍 Cause probable: ComfyUI ne charge pas correctement le hash")
    sys.exit(1)