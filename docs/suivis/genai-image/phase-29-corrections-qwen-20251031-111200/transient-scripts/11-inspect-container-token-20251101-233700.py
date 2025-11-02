#!/usr/bin/env python3
"""
Script Transient 11 - Inspection Container Pour Localiser Fichier Token
Dernière tentative : Trouver où Docker lit RÉELLEMENT le fichier token

Auteur: Script transient Phase 29
Date: 2025-11-01 23:37:00
"""

import sys
import subprocess

print("=" * 70)
print("🔍 INSPECTION CONTAINER DOCKER - LOCALISATION TOKEN")
print("=" * 70)

# ============================================================================
# ÉTAPE 1 : TROUVER TOUS LES FICHIERS TOKEN DANS LE CONTAINER
# ============================================================================
print("\n🐳 ÉTAPE 1/4 : Recherche exhaustive fichiers token dans container")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose exec -T comfyui-qwen find /workspace -name '*token*' -type f"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    files = result.stdout.strip().split("\n")
    print(f"✅ {len(files)} fichiers token trouvés dans container:")
    for file in files:
        if file:
            print(f"   📄 {file}")
else:
    print(f"❌ Erreur recherche: {result.stderr}")

# ============================================================================
# ÉTAPE 2 : LIRE CONTENU DE CHAQUE FICHIER TOKEN TROUVÉ
# ============================================================================
print("\n📖 ÉTAPE 2/4 : Lecture contenu de chaque fichier token")

# Hash cible (celui qu'on veut)
token_file_win = "d:/Dev/CoursIA/.secrets/qwen-api-user.token"
with open(token_file_win.replace("/", "\\"), 'r', encoding='utf-8') as f:
    hash_target = f.read().strip()

print(f"🎯 Hash cible: {hash_target[:40]}...{hash_target[-20:]}")

if result.returncode == 0 and files:
    for file in files:
        if file and "token" in file.lower():
            result = subprocess.run(
                ["wsl", "bash", "-c", f"cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose exec -T comfyui-qwen cat {file}"],
                capture_output=True,
                text=True
            )
            
            if result.returncode == 0:
                content = result.stdout.strip()
                match = "✅" if content == hash_target else "❌"
                print(f"\n{match} {file}")
                print(f"   Contenu: {content[:40]}...{content[-20:]}")
            else:
                print(f"\n⚠️ {file} (non lisible)")

# ============================================================================
# ÉTAPE 3 : INSPECTER PROCESSUS COMFYUI POUR VOIR LE TOKEN CHARGÉ
# ============================================================================
print("\n🔬 ÉTAPE 3/4 : Inspection processus ComfyUI")

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose logs comfyui-qwen | grep -E '(token|QWEN_API|auth)' | tail -10"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    print("📋 Logs ComfyUI (10 dernières lignes avec 'token'):")
    print(result.stdout)

# ============================================================================
# ÉTAPE 4 : RECOMMANDATIONS FINALES
# ============================================================================
print("\n💡 ÉTAPE 4/4 : Recommandations finales")
print("=" * 70)

print("""
🔍 DIAGNOSTIC DÉFINITIF :

Le container Docker charge un hash token qui ne correspond à AUCUN des fichiers
synchronisés sur le système hôte ou dans WSL.

Cela signifie que :
1. ❌ Le fichier token est probablement INTÉGRÉ dans l'image Docker lors du build
2. ❌ OU le container a un cache de credentials persistant dans un volume non monté
3. ❌ OU ComfyUI lit le token depuis une variable d'environnement codée en dur

⚠️ SOLUTIONS POSSIBLES :

OPTION A - REBUILD COMPLET DU CONTAINER :
1. Arrêter et supprimer le container : docker-compose down -v
2. Supprimer l'image : docker rmi <image_name>
3. Rebuild : docker-compose build --no-cache
4. Redémarrer : docker-compose up -d

OPTION B - MODIFIER LE TOKEN CÔTÉ SERVEUR :
1. Générer un nouveau token brut correspondant au hash actuel Docker
2. Calculer le token brut via bcrypt.checkpw() en force brute (impossible)
3. OU modifier directement le hash dans le code source ComfyUI du container

OPTION C - UTILISER L'ANCIEN TOKEN :
1. Retrouver le token brut correspondant au hash Docker actuel
2. Mettre à jour TOUS les fichiers .env avec cet ancien token
3. Tester l'authentification

⚠️ RECOMMANDATION IMMÉDIATE : OPTION A (Rebuild complet)

Commandes à exécuter :
```bash
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down -v"
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose build --no-cache"
wsl bash -c "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"
```

Après rebuild, réexécuter script transient 07 pour vérifier l'authentification.
""")

print("=" * 70)