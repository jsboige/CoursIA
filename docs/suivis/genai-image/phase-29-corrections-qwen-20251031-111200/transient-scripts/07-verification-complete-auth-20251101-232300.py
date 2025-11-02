#!/usr/bin/env python3
"""
Script Transient 07 - Vérification Complète Authentification Post-Régénération
Vérifie les logs Docker + Teste l'authentification + Génère rapport final

Auteur: Script transient Phase 29
Date: 2025-11-01 23:23:00
"""

import sys
import subprocess
import requests
import time
from pathlib import Path
from datetime import datetime

print("=" * 70)
print("🔍 VÉRIFICATION COMPLÈTE AUTHENTIFICATION COMFYUI QWEN")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : VÉRIFICATION HASH DOCKER
# ============================================================================
print("\n📋 ÉTAPE 1/4 : Vérification hash bcrypt dans logs Docker")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose logs comfyui-qwen | grep 'For direct API' | tail -1"],
    capture_output=True,
    text=True
)

if result.returncode == 0 and result.stdout:
    log_line = result.stdout.strip()
    print(f"✅ Log trouvé: {log_line[:100]}...")
    
    # Extraire le hash
    if "token=" in log_line:
        hash_docker = log_line.split("token=")[1].strip()
        print(f"🔑 Hash Docker: {hash_docker[:30]}...{hash_docker[-20:]}")
    else:
        print("❌ Impossible extraire hash des logs")
        hash_docker = None
else:
    print("❌ Impossible récupérer logs Docker")
    hash_docker = None

# Vérifier correspondance avec fichier Windows
token_file_win = Path(".secrets/qwen-api-user.token")
if token_file_win.exists():
    with open(token_file_win, 'r', encoding='utf-8') as f:
        hash_win = f.read().strip()
    print(f"📄 Hash Windows: {hash_win[:30]}...{hash_win[-20:]}")
    
    if hash_docker and hash_docker == hash_win:
        print("✅ CORRESPONDANCE PARFAITE : Hash Docker = Hash Windows")
    else:
        print("❌ DÉSYNCHRONISATION : Hash Docker ≠ Hash Windows")
        print("⚠️ Docker utilise un ancien hash mis en cache")
else:
    print("❌ Fichier token Windows introuvable")
    hash_win = None

# ============================================================================
# ÉTAPE 2 : LECTURE TOKEN BRUT CLIENT
# ============================================================================
print("\n🔐 ÉTAPE 2/4 : Lecture token brut client")

env_generated = Path(".secrets/.env.generated")
if env_generated.exists():
    with open(env_generated, 'r', encoding='utf-8') as f:
        for line in f:
            if line.startswith("QWEN_API_USER_TOKEN="):
                token_brut = line.split('=', 1)[1].strip()
                print(f"✅ Token brut chargé: {token_brut[:10]}...{token_brut[-10:]}")
                break
        else:
            print("❌ Token non trouvé dans .env.generated")
            token_brut = None
else:
    print("❌ Fichier .env.generated introuvable")
    token_brut = None

if not token_brut:
    print("❌ ERREUR : Impossible charger token brut, arrêt du test")
    sys.exit(1)

# ============================================================================
# ÉTAPE 3 : TEST AUTHENTIFICATION API
# ============================================================================
print("\n🌐 ÉTAPE 3/4 : Test authentification API ComfyUI")

url = "http://localhost:8188/system_stats"
headers = {"Authorization": f"Bearer {token_brut}"}

print(f"📡 Endpoint: {url}")
print(f"🔑 Token: {token_brut[:10]}...{token_brut[-10:]}")

try:
    response = requests.get(url, headers=headers, timeout=10)
    status_code = response.status_code
    print(f"📊 HTTP Status: {status_code}")
    
    if status_code == 200:
        print("✅ ✅ ✅ AUTHENTIFICATION RÉUSSIE ✅ ✅ ✅")
        data = response.json()
        print(f"📦 Données système récupérées: {len(str(data))} caractères")
        auth_success = True
    elif status_code == 401:
        print("❌ AUTHENTIFICATION ÉCHOUÉE (HTTP 401 Unauthorized)")
        print("🔍 Hash bcrypt et token brut sont désynchronisés")
        auth_success = False
    else:
        print(f"⚠️ Status inattendu: {status_code}")
        print(f"📄 Réponse: {response.text[:200]}")
        auth_success = False
        
except Exception as e:
    print(f"❌ Erreur requête: {e}")
    auth_success = False
    status_code = None

# ============================================================================
# ÉTAPE 4 : GÉNÉRATION RAPPORT FINAL
# ============================================================================
print("\n📄 ÉTAPE 4/4 : Génération rapport final SDDD")

rapport_dir = Path("docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports")
rapport_dir.mkdir(parents=True, exist_ok=True)

timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
rapport_file = rapport_dir / f"16-regeneration-complete-credentials-{timestamp}.md"

with open(rapport_file, 'w', encoding='utf-8') as f:
    f.write(f"# Rapport 16 - Régénération Complète Credentials ComfyUI Qwen\n\n")
    f.write(f"**Date** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    f.write(f"**Script** : `07-verification-complete-auth-20251101-232300.py`\n\n")
    
    f.write("## Résumé Exécution\n\n")
    if auth_success:
        f.write("✅ **SUCCÈS COMPLET - AUTHENTIFICATION FONCTIONNELLE**\n\n")
    else:
        f.write("❌ **ÉCHEC - AUTHENTIFICATION NON FONCTIONNELLE**\n\n")
    
    f.write("## Vérification Hash bcrypt\n\n")
    if hash_docker:
        f.write(f"- **Hash Docker** : `{hash_docker}`\n")
    if hash_win:
        f.write(f"- **Hash Windows** : `{hash_win}`\n")
    
    if hash_docker and hash_win:
        if hash_docker == hash_win:
            f.write("- **Statut** : ✅ Correspondance parfaite\n\n")
        else:
            f.write("- **Statut** : ❌ Désynchronisation détectée\n")
            f.write("- **Action requise** : Redémarrage Docker complet (`down` puis `up`)\n\n")
    
    f.write("## Credentials Actuels\n\n")
    if token_brut:
        f.write(f"- **Token brut** : `{token_brut}`\n")
    if hash_win:
        f.write(f"- **Hash bcrypt** : `{hash_win}`\n\n")
    
    f.write("## Test Authentification API\n\n")
    f.write(f"- **Endpoint** : `GET {url}`\n")
    if status_code:
        f.write(f"- **HTTP Status** : `{status_code}`\n")
    if auth_success:
        f.write("- **Résultat** : ✅ **AUTHENTIFICATION RÉUSSIE**\n\n")
    else:
        f.write("- **Résultat** : ❌ **AUTHENTIFICATION ÉCHOUÉE**\n")
        f.write("- **Diagnostic** : Token brut ou hash bcrypt incorrect\n\n")
    
    f.write("## Actions Recommandées\n\n")
    if auth_success:
        f.write("- [x] Système fonctionnel, prêt pour génération d'images\n")
        f.write("- [ ] Tester génération d'image avec script transient 03\n")
    else:
        f.write("- [ ] Vérifier correspondance hash Docker ≠ hash Windows\n")
        f.write("- [ ] Redémarrer Docker avec `docker-compose down && docker-compose up -d`\n")
        f.write("- [ ] Réexécuter ce script de vérification\n")
    
    f.write(f"\n---\n*Généré automatiquement par script transient 07*\n")

print(f"✅ Rapport créé: {rapport_file}")

# ============================================================================
# RÉSUMÉ FINAL
# ============================================================================
print("\n" + "=" * 70)
if auth_success:
    print("🎉 MISSION COMPLÈTE - AUTHENTIFICATION FONCTIONNELLE")
    print("=" * 70)
    print(f"✅ Token brut : {token_brut}")
    if hash_win:
        print(f"✅ Hash bcrypt: {hash_win}")
    print(f"✅ HTTP Status: {status_code}")
    print(f"✅ Rapport    : {rapport_file}")
    sys.exit(0)
else:
    print("❌ AUTHENTIFICATION ÉCHOUÉE")
    print("=" * 70)
    print(f"❌ Token brut : {token_brut}")
    if hash_docker and hash_win and hash_docker != hash_win:
        print(f"❌ Hash Docker ≠ Hash Windows → DÉSYNCHRONISATION")
        print(f"   Docker : {hash_docker[:40]}...")
        print(f"   Windows: {hash_win[:40]}...")
    print(f"❌ HTTP Status: {status_code}")
    print(f"📄 Rapport    : {rapport_file}")
    print("\n⚠️ ACTION REQUISE: Redémarrer Docker complètement")
    sys.exit(1)