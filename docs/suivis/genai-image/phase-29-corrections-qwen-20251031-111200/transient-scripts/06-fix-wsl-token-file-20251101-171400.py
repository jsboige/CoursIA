#!/usr/bin/env python3
"""
Script pour corriger le fichier token serveur WSL
Date: 2025-11-01 17:14:00
"""

import subprocess
import sys

# Hash bcrypt complet du serveur
HASH_SERVEUR = "$2b$12$UDceblhZeEySDwVMC0ccN.IaQmMBfKdTY.aAE3poXcq1zsOP6coni"
WSL_PATH = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets/qwen-api-user.token"

print("=" * 80)
print("🔧 CORRECTION DU FICHIER TOKEN SERVEUR WSL")
print("=" * 80)

print(f"\n📋 Configuration:")
print(f"   - Hash serveur: {HASH_SERVEUR[:30]}...")
print(f"   - Chemin WSL: {WSL_PATH}")

# Créer le répertoire si nécessaire
print("\n📁 Création du répertoire .secrets...")
result = subprocess.run(
    ["wsl", "mkdir", "-p", "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/.secrets"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("   ✅ Répertoire créé/vérifié")
else:
    print(f"   ⚠️ Warning: {result.stderr}")

# Écrire le hash dans le fichier (sans newline)
print("\n✍️ Écriture du hash dans le fichier...")
cmd = f"echo -n '{HASH_SERVEUR}' > {WSL_PATH}"
result = subprocess.run(
    ["wsl", "bash", "-c", cmd],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("   ✅ Hash écrit avec succès")
else:
    print(f"   ❌ Erreur: {result.stderr}")
    sys.exit(1)

# Vérifier le contenu
print("\n🔍 Vérification du contenu...")
result = subprocess.run(
    ["wsl", "cat", WSL_PATH],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    content = result.stdout.strip()
    print(f"   Contenu lu: {content[:30]}...{content[-20:]}")
    
    if content == HASH_SERVEUR:
        print("   ✅ VÉRIFICATION RÉUSSIE: Le hash est correct!")
    else:
        print(f"   ❌ ERREUR: Le hash ne correspond pas!")
        print(f"      Attendu: {HASH_SERVEUR}")
        print(f"      Obtenu:  {content}")
        sys.exit(1)
else:
    print(f"   ❌ Erreur lecture: {result.stderr}")
    sys.exit(1)

print("\n" + "=" * 80)
print("✅ SUCCÈS: Fichier token serveur WSL corrigé")
print("=" * 80)
print("\n📝 Prochaine étape: Redémarrer le service Docker")
print("   wsl bash -c 'cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose restart'")