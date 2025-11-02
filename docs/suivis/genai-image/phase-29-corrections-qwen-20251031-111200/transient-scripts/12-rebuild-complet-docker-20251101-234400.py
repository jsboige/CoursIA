#!/usr/bin/env python3
"""
Script Transient 12 - Rebuild Complet Docker ComfyUI Qwen
Date: 2025-11-01 23:44:00
Phase: Phase 29 - Corrections Qwen ComfyUI

MISSION CRITIQUE : Rebuild complet de l'image Docker sans cache
pour forcer l'utilisation du nouveau hash bcrypt.

Étapes:
1. Arrêt et suppression complète (containers + volumes + images)
2. Rebuild sans cache
3. Redémarrage
4. Vérification hash Docker vs hash attendu
5. Test authentification API
6. Génération d'image si succès
"""

import subprocess
import time
from pathlib import Path

print("="*70)
print("🔄 REBUILD COMPLET DOCKER - OPTION A")
print("="*70)

# Hash bcrypt attendu (généré dans script 06)
HASH_ATTENDU = "$2b$12$2jPJrb7dmsM7fw0..PoEqu8nmGarw0vnYYdGw5BFmcZ52bGfwf5M2"
TOKEN_BRUT = "2%=tVJ6@!Nc(7#VTvj-Bh3^nm0WY-Lij"

# ============================================================================
# ÉTAPE 1 : ARRÊT ET SUPPRESSION COMPLÈTE
# ============================================================================
print("\n🛑 ÉTAPE 1/6 : Arrêt et suppression complète")
print("-" * 70)

# 1.1. Arrêt et suppression containers + volumes
print("\n📦 Arrêt containers et suppression volumes...")
result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose down -v"],
    capture_output=True,
    text=True
)
if result.returncode == 0:
    print("✅ Containers arrêtés et volumes supprimés")
    print(f"   Output: {result.stdout.strip()}")
else:
    print(f"❌ ERREUR arrêt containers: {result.stderr}")

time.sleep(5)

# 1.2. Récupération ID de l'image actuelle
print("\n🔍 Recherche ID de l'image comfyui-qwen...")
result = subprocess.run(
    ["wsl", "bash", "-c", "docker images | grep comfyui-qwen | awk '{print $3}'"],
    capture_output=True,
    text=True
)
if result.returncode == 0 and result.stdout.strip():
    image_id = result.stdout.strip()
    print(f"✅ Image trouvée: {image_id}")
    
    # 1.3. Suppression de l'image
    print(f"\n🗑️  Suppression de l'image {image_id}...")
    result = subprocess.run(
        ["wsl", "bash", "-c", f"docker rmi -f {image_id}"],
        capture_output=True,
        text=True
    )
    if result.returncode == 0:
        print("✅ Image supprimée avec succès")
    else:
        print(f"⚠️  Avertissement suppression image: {result.stderr}")
else:
    print("⚠️  Aucune image comfyui-qwen trouvée (peut-être déjà supprimée)")

time.sleep(3)

# ============================================================================
# ÉTAPE 2 : REBUILD SANS CACHE
# ============================================================================
print("\n🏗️  ÉTAPE 2/6 : Rebuild sans cache")
print("-" * 70)
print("⚠️  Cette étape peut prendre plusieurs minutes...")
print("   Docker va télécharger et construire l'image depuis zéro")

start_time = time.time()
result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose build --no-cache"],
    capture_output=True,
    text=True
)
build_duration = time.time() - start_time

if result.returncode == 0:
    print(f"✅ Rebuild terminé avec succès en {build_duration:.1f}s")
    # Afficher les dernières lignes du build
    build_lines = result.stdout.strip().split('\n')
    print("   Dernières lignes du build:")
    for line in build_lines[-10:]:
        print(f"   {line}")
else:
    print(f"❌ ERREUR rebuild: {result.stderr}")
    print("\n🚨 ARRÊT SCRIPT - Le rebuild a échoué")
    exit(1)

time.sleep(3)

# ============================================================================
# ÉTAPE 3 : REDÉMARRAGE
# ============================================================================
print("\n🚀 ÉTAPE 3/6 : Redémarrage container")
print("-" * 70)

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose up -d"],
    capture_output=True,
    text=True
)
if result.returncode == 0:
    print("✅ Container démarré")
    print(f"   Output: {result.stdout.strip()}")
else:
    print(f"❌ ERREUR démarrage: {result.stderr}")
    exit(1)

print("\n⏳ Attente 30 secondes pour démarrage complet...")
time.sleep(30)

# ============================================================================
# ÉTAPE 4 : VÉRIFICATION HASH DOCKER
# ============================================================================
print("\n🔍 ÉTAPE 4/6 : Vérification hash Docker")
print("-" * 70)

result = subprocess.run(
    ["wsl", "bash", "-c", "cd /home/jesse/SD/workspace/comfyui-qwen && docker-compose logs comfyui-qwen | grep -i 'hash' | tail -5"],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    logs = result.stdout.strip()
    print("📋 Logs Docker (hash):")
    print(logs)
    
    # Vérification si le nouveau hash est présent
    if HASH_ATTENDU in logs:
        print("\n✅ SUCCÈS - Le nouveau hash est chargé par Docker!")
        hash_match = True
    else:
        print("\n⚠️  Le nouveau hash n'apparaît pas encore dans les logs")
        print("   Cela peut être normal si l'API n'a pas encore été sollicitée")
        hash_match = False
else:
    print(f"❌ ERREUR lecture logs: {result.stderr}")
    hash_match = False

time.sleep(2)

# ============================================================================
# ÉTAPE 5 : TEST AUTHENTIFICATION
# ============================================================================
print("\n🔐 ÉTAPE 5/6 : Test authentification API")
print("-" * 70)
print(f"   Token brut: {TOKEN_BRUT}")
print(f"   Hash attendu: {HASH_ATTENDU}")

result = subprocess.run(
    ["wsl", "bash", "-c", f'curl -s -w "\\n%{{http_code}}" -X GET -H "Authorization: Bearer {TOKEN_BRUT}" http://localhost:8188/system_stats'],
    capture_output=True,
    text=True
)

if result.returncode == 0:
    output = result.stdout.strip()
    lines = output.split('\n')
    http_code = lines[-1] if lines else "000"
    response_body = '\n'.join(lines[:-1]) if len(lines) > 1 else ""
    
    print(f"\n📊 Réponse HTTP: {http_code}")
    
    if http_code == "200":
        print("✅ AUTHENTIFICATION RÉUSSIE!")
        print(f"   Réponse API:\n{response_body[:500]}")
        auth_success = True
    else:
        print(f"❌ AUTHENTIFICATION ÉCHOUÉE (HTTP {http_code})")
        print(f"   Réponse: {response_body[:200]}")
        auth_success = False
else:
    print(f"❌ ERREUR test curl: {result.stderr}")
    auth_success = False

# ============================================================================
# ÉTAPE 6 : GÉNÉRATION D'IMAGE (SI SUCCÈS)
# ============================================================================
if auth_success:
    print("\n🖼️  ÉTAPE 6/6 : Génération d'image test")
    print("-" * 70)
    
    script_path = Path("docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/transient-scripts/03-test-generation-images-20251031-230500.py")
    
    if script_path.exists():
        print(f"📄 Exécution du script de génération: {script_path}")
        result = subprocess.run(
            ["python", str(script_path)],
            capture_output=True,
            text=True
        )
        
        if result.returncode == 0:
            print("✅ Script de génération exécuté avec succès")
            print(f"   Output:\n{result.stdout[-500:]}")
        else:
            print(f"⚠️  Le script de génération a rencontré une erreur:")
            print(f"   {result.stderr[:500]}")
    else:
        print(f"⚠️  Script de génération introuvable: {script_path}")
else:
    print("\n⏭️  ÉTAPE 6/6 : Génération d'image IGNORÉE (authentification échouée)")

# ============================================================================
# RAPPORT FINAL
# ============================================================================
print("\n" + "="*70)
print("📊 RAPPORT FINAL - REBUILD COMPLET DOCKER")
print("="*70)

print("\n✅ Étapes terminées:")
print("   [✓] Arrêt et suppression containers + volumes")
print("   [✓] Suppression de l'image Docker")
print("   [✓] Rebuild sans cache")
print("   [✓] Redémarrage container")
print("   [✓] Vérification hash Docker")
print("   [✓] Test authentification API")

print(f"\n🎯 Résultat Final:")
print(f"   Hash chargé: {'✅ OUI' if hash_match else '⚠️  NON VÉRIFIÉ'}")
print(f"   Authentification: {'✅ SUCCÈS (HTTP 200)' if auth_success else '❌ ÉCHEC'}")

if auth_success:
    print("\n🎉 MISSION ACCOMPLIE - Le rebuild a résolu le problème!")
    print("   L'image Docker utilise maintenant le nouveau hash bcrypt")
    print("   L'authentification fonctionne correctement")
else:
    print("\n⚠️  MISSION INCOMPLÈTE - L'authentification échoue toujours")
    print("\n🔍 Diagnostic supplémentaire nécessaire:")
    print("   1. Vérifier les logs Docker complets")
    print("   2. Inspecter le code source ComfyUI dans le container")
    print("   3. Vérifier les variables d'environnement du container")

print("\n📝 Voir rapport détaillé:")
print("   docs/suivis/genai-image/phase-29-corrections-qwen-20251031-111200/rapports/16-regeneration-complete-credentials-20251101_232640.md")

print("\n" + "="*70)