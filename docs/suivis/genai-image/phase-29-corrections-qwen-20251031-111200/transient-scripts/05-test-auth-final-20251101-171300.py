#!/usr/bin/env python3
"""
Script Transient 05 - Test Authentification Final ComfyUI Qwen
Utilise les credentials FRAIS régénérés manuellement sans régénération
"""

import sys
import os
import requests
from pathlib import Path

# Calcul du chemin racine
current_file = Path(__file__).resolve()
path_parts = current_file.parts
docs_index = path_parts.index('docs') if 'docs' in path_parts else -1
project_root = Path(*path_parts[:docs_index]) if docs_index >= 0 else current_file.parent.parent.parent.parent

print(f"📁 Racine projet: {project_root}")

# Lire le token depuis .secrets/.env.generated
env_file = project_root / ".secrets" / ".env.generated"
print(f"📄 Lecture token depuis: {env_file}")

if not env_file.exists():
    print(f"❌ Fichier .env.generated introuvable: {env_file}")
    sys.exit(1)

with open(env_file, 'r', encoding='utf-8') as f:
    for line in f:
        if line.startswith("QWEN_API_USER_TOKEN="):
            api_key = line.split('=', 1)[1].strip()
            print(f"✅ Token chargé: {api_key[:10]}...{api_key[-10:]}")
            break
else:
    print("❌ Token non trouvé dans .env.generated")
    sys.exit(1)

# Test 1: Endpoint /system_stats avec curl
print("\n" + "="*60)
print("TEST 1: Authentification API ComfyUI")
print("="*60)

url = "http://localhost:8188/system_stats"
headers = {"Authorization": f"Bearer {api_key}"}

try:
    response = requests.get(url, headers=headers, timeout=5)
    print(f"📡 Requête: GET {url}")
    print(f"🔑 Authorization: Bearer {api_key[:10]}...{api_key[-10:]}")
    print(f"📊 Status Code: {response.status_code}")
    
    if response.status_code == 200:
        print("✅ AUTHENTIFICATION RÉUSSIE")
        data = response.json()
        print(f"📦 Données reçues: {len(str(data))} caractères")
    elif response.status_code == 401:
        print("❌ ÉCHEC AUTHENTIFICATION (HTTP 401 Unauthorized)")
        print("🔍 Vérifier que le hash bcrypt WSL correspond au token brut")
    else:
        print(f"⚠️ Status inattendu: {response.status_code}")
        print(f"📄 Réponse: {response.text[:200]}")
        
except Exception as e:
    print(f"❌ Erreur requête: {e}")

print("="*60)