#!/usr/bin/env python3
"""
Script Transient 06 - Régénération Complète Chaîne Authentification ComfyUI Qwen
ONE-LINER: Génère → Déploie → Redémarre → Teste

Auteur: Script transient Phase 29
Date: 2025-11-01
"""

import sys
import os
import subprocess
import secrets
import string
import bcrypt
import requests
import time
from pathlib import Path

print("=" * 70)
print("🔄 RÉGÉNÉRATION COMPLÈTE CHAÎNE AUTHENTIFICATION COMFYUI QWEN")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : GÉNÉRATION CREDENTIALS FRAIS
# ============================================================================
print("\n📝 ÉTAPE 1/5 : Génération credentials FRAIS")

# Générer token brut
chars = string.ascii_letters + string.digits + "!@#$%^&*()_+-="
token_brut = ''.join(secrets.choice(chars) for _ in range(32))
print(f"✅ Token brut généré: {token_brut[:10]}...{token_brut[-10:]}")

# Générer hash bcrypt
hash_bcrypt = bcrypt.hashpw(token_brut.encode('utf-8'), bcrypt.gensalt(rounds=12))
hash_str = hash_bcrypt.decode('utf-8')
print(f"✅ Hash bcrypt: {hash_str[:20]}...{hash_str[-20:]}")

# ============================================================================
# ÉTAPE 2 : DÉPLOIEMENT FICHIERS .ENV (TOUS)
# ============================================================================
print("\n📂 ÉTAPE 2/5 : Déploiement fichiers .env")

# Fichier 1: .secrets/.env.generated
env_generated = Path(".secrets/.env.generated")
env_generated.parent.mkdir(parents=True, exist_ok=True)
with open(env_generated, 'w', encoding='utf-8') as f:
    f.write(f"QWEN_API_USER_TOKEN={token_brut}\n")
print(f"✅ Créé: {env_generated}")

# Fichier 2: docker-configurations/comfyui-qwen/.env
docker_env = Path("docker-configurations/comfyui-qwen/.env")
with open(docker_env, 'w', encoding='utf-8') as f:
    f.write(f"QWEN_API_TOKEN={token_brut}\n")
print(f"✅ Créé: {docker_env}")

# Fichier 3: .secrets/qwen-api-user.token (Windows)
token_file_win = Path(".secrets/qwen-api-user.token")
with open(token_file_win, 'w', encoding='utf-8') as f:
    f.write(f"{hash_str}\n")
print(f"✅ Créé: {token_file_win}")

# Fichier 4: WSL /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token
print("\n📦 Déploiement hash bcrypt sur WSL...")
temp_hash_file = Path("temp_hash_deploy.txt")
with open(temp_hash_file, 'w', encoding='utf-8') as f:
    f.write(hash_str)

wsl_path = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token"
result = subprocess.run(
    ["wsl", "bash", "-c", f"wslpath 'd:/Dev/CoursIA/{temp_hash_file}' | xargs cat > {wsl_path}"],
    capture_output=True,
    text=True
)
if result.returncode == 0:
    print(f"✅ Créé WSL: {wsl_path}")
else:
    print(f"❌ Erreur WSL: {result.stderr}")
    sys.exit(1)

# Nettoyer fichier temporaire
temp_hash_file.unlink()

# Vérifier hash WSL
verify = subprocess.run(
    ["wsl", "bash", "-c", f"cat {wsl_path}"],
    capture_output=True,
    text=True
)
if verify.stdout.strip() == hash_str:
    print(f"✅ Vérification hash WSL OK")
else:
    print(f"❌ Hash WSL invalide: {verify.stdout[:30]}...")
    sys.exit(1)

# ============================================================================
# ÉTAPE 3 : REDÉMARRAGE DOCKER
# ============================================================================
print("\n🐳 ÉTAPE 3/5 : Redémarrage Docker ComfyUI")

# Arrêt
print("🛑 Arrêt Docker...")
subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down"],
    check=True,
    capture_output=True
)
print("✅ Docker arrêté")

# Démarrage
print("🚀 Démarrage Docker...")
subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"],
    check=True,
    capture_output=True
)
print("✅ Docker démarré")

# Attendre démarrage complet
print("⏳ Attente démarrage ComfyUI (30s)...")
time.sleep(30)

# ============================================================================
# ÉTAPE 4 : TEST AUTHENTIFICATION
# ============================================================================
print("\n🔐 ÉTAPE 4/5 : Test authentification")

url = "http://localhost:8188/system_stats"
headers = {"Authorization": f"Bearer {token_brut}"}

try:
    response = requests.get(url, headers=headers, timeout=10)
    print(f"📡 GET {url}")
    print(f"🔑 Token: {token_brut[:10]}...{token_brut[-10:]}")
    print(f"📊 Status: {response.status_code}")
    
    if response.status_code == 200:
        print("✅ ✅ ✅ AUTHENTIFICATION RÉUSSIE ✅ ✅ ✅")
        data = response.json()
        print(f"📦 Données système: {len(str(data))} caractères")
    elif response.status_code == 401:
        print("❌ ÉCHEC AUTHENTIFICATION (HTTP 401)")
        print("🔍 Hash bcrypt ou token brut désynchronisés")
        sys.exit(1)
    else:
        print(f"⚠️ Status inattendu: {response.status_code}")
        print(f"📄 Réponse: {response.text[:200]}")
        sys.exit(1)
        
except Exception as e:
    print(f"❌ Erreur requête: {e}")
    sys.exit(1)

# ============================================================================
# ÉTAPE 5 : RAPPORT FINAL
# ============================================================================
print("\n📄 ÉTAPE 5/5 : Génération rapport SDDD")

rapport_dir = Path("docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports")
rapport_dir.mkdir(parents=True, exist_ok=True)

from datetime import datetime
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
rapport_file = rapport_dir / f"16-regeneration-complete-credentials-{timestamp}.md"

with open(rapport_file, 'w', encoding='utf-8') as f:
    f.write(f"# Rapport 16 - Régénération Complète Credentials ComfyUI Qwen\n\n")
    f.write(f"**Date** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    f.write(f"**Script** : `06-regeneration-complete-auth-20251101-173400.py`\n\n")
    
    f.write("## Résumé Exécution\n\n")
    f.write("✅ **SUCCÈS COMPLET**\n\n")
    
    f.write("## Credentials Générés\n\n")
    f.write(f"- **Token brut** : `{token_brut}`\n")
    f.write(f"- **Hash bcrypt** : `{hash_str}`\n\n")
    
    f.write("## Fichiers Synchronisés\n\n")
    f.write(f"1. ✅ `.secrets/.env.generated`\n")
    f.write(f"2. ✅ `docker-configurations/comfyui-qwen/.env`\n")
    f.write(f"3. ✅ `.secrets/qwen-api-user.token` (Windows)\n")
    f.write(f"4. ✅ `/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token` (WSL)\n\n")
    
    f.write("## Test Authentification\n\n")
    f.write(f"- **Endpoint** : `GET {url}`\n")
    f.write(f"- **Status Code** : `200 OK`\n")
    f.write(f"- **Résultat** : ✅ **AUTHENTIFICATION RÉUSSIE**\n\n")
    
    f.write("## Livrables\n\n")
    f.write("- [x] Credentials FRAIS générés\n")
    f.write("- [x] TOUS les fichiers synchronisés\n")
    f.write("- [x] Docker redémarré\n")
    f.write("- [x] Test authentification HTTP 200 OK\n")
    f.write("- [x] Rapport SDDD numéroté 16 généré\n\n")
    
    f.write(f"---\n*Généré automatiquement par script transient 06*\n")

print(f"✅ Rapport créé: {rapport_file}")

print("\n" + "=" * 70)
print("🎉 MISSION COMPLÈTE - AUTHENTIFICATION FONCTIONNELLE")
print("=" * 70)
print(f"Token brut : {token_brut}")
print(f"Hash bcrypt: {hash_str}")
print(f"Rapport    : {rapport_file}")
print("=" * 70)