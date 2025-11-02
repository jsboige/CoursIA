#!/usr/bin/env python3
"""
ÉTAPE 24F - Téléchargement Modèle Qwen2-VL Q4_K_M (GGUF)
Phase 29 - Corrections Qwen ComfyUI
Date: 2025-11-02 11:45:00

MISSION:
- Télécharger modèle Qwen2-VL-7B-Instruct-GGUF (Q4_K_M, 5.44 GB)
- Copier modèle dans container Docker comfyui-qwen
- Placer dans /workspace/ComfyUI/models/checkpoints/Qwen2-VL-Q4/
- Vérifier intégrité téléchargement

RÉFÉRENCES:
- Repository: https://huggingface.co/Comfy-Org/Qwen2-VL-7B-Instruct-GGUF
- Révision: 63782e2
- Token: .secrets/.env.huggingface
"""

import os
import sys
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
from typing import Optional

# Configuration
REPO_ID = "Comfy-Org/Qwen2-VL-7B-Instruct-GGUF"
REVISION = "63782e2"
TOKEN_FILE = Path(".secrets/.env.huggingface")
TEMP_DIR = Path("./temp_qwen2_q4_download")
CONTAINER_NAME = "comfyui-qwen"
CONTAINER_PATH = "/workspace/ComfyUI/models/checkpoints/Qwen2-VL-Q4/"

def print_section(title: str):
    """Affiche un séparateur de section"""
    print(f"\n{'='*80}")
    print(f"  {title}")
    print(f"{'='*80}\n")

def load_hf_token() -> str:
    """Charge le token HuggingFace depuis .secrets/.env.huggingface"""
    print_section("🔑 CHARGEMENT TOKEN HUGGINGFACE")
    
    if not TOKEN_FILE.exists():
        raise FileNotFoundError(
            f"Token HuggingFace non trouvé: {TOKEN_FILE}\n"
            f"Assurez-vous que le fichier existe avec le contenu: HF_TOKEN=hf_xxx"
        )
    
    with open(TOKEN_FILE) as f:
        content = f.read().strip()
        
    # Extraire le token (format: HF_TOKEN=hf_xxx ou juste hf_xxx)
    if "=" in content:
        token = content.split("=", 1)[1].strip()
    else:
        token = content.strip()
    
    if not token.startswith("hf_"):
        raise ValueError(f"Token invalide dans {TOKEN_FILE} (doit commencer par 'hf_')")
    
    print(f"✅ Token chargé depuis: {TOKEN_FILE}")
    print(f"✅ Token valide (commence par 'hf_', longueur: {len(token)} caractères)")
    
    return token

def check_dependencies():
    """Vérifie que les dépendances Python sont installées"""
    print_section("📦 VÉRIFICATION DÉPENDANCES")
    
    try:
        import huggingface_hub
        print(f"✅ huggingface_hub version: {huggingface_hub.__version__}")
    except ImportError:
        print("❌ huggingface_hub non installé")
        print("\nInstallation requise:")
        print("  pip install huggingface_hub")
        sys.exit(1)

def download_model(token: str) -> Path:
    """Télécharge le modèle depuis HuggingFace"""
    print_section("⬇️ TÉLÉCHARGEMENT MODÈLE QWEN2-VL Q4_K_M")
    
    from huggingface_hub import snapshot_download
    
    # Nettoyer le répertoire temporaire si existant
    if TEMP_DIR.exists():
        print(f"🧹 Nettoyage répertoire existant: {TEMP_DIR}")
        shutil.rmtree(TEMP_DIR)
    
    TEMP_DIR.mkdir(parents=True, exist_ok=True)
    
    print(f"📁 Répertoire temporaire: {TEMP_DIR}")
    print(f"🏢 Repository: {REPO_ID}")
    print(f"🔖 Révision: {REVISION}")
    print(f"📋 Patterns: *.gguf, *.json, config.json")
    print("\n⏳ Téléchargement en cours (5.44 GB attendus)...\n")
    
    start_time = datetime.now()
    
    try:
        local_path = snapshot_download(
            repo_id=REPO_ID,
            revision=REVISION,
            allow_patterns=["*.gguf", "*.json", "config.json"],
            token=token,
            local_dir=str(TEMP_DIR),
            local_dir_use_symlinks=False  # Copie réelle, pas de symlinks
        )
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        print(f"\n✅ Téléchargement terminé en {duration:.2f} secondes ({duration/60:.2f} minutes)")
        
        # Afficher la liste des fichiers téléchargés
        print("\n📋 Fichiers téléchargés:")
        total_size = 0
        for file in sorted(TEMP_DIR.rglob("*")):
            if file.is_file():
                size_mb = file.stat().st_size / (1024 * 1024)
                total_size += file.stat().st_size
                print(f"  - {file.name}: {size_mb:.2f} MB")
        
        total_size_gb = total_size / (1024 * 1024 * 1024)
        print(f"\n💾 Taille totale: {total_size_gb:.2f} GB")
        
        return Path(local_path)
        
    except Exception as e:
        print(f"\n❌ Erreur lors du téléchargement: {e}")
        raise

def check_docker_container() -> bool:
    """Vérifie que le container Docker existe et est en cours d'exécution"""
    print_section("🐳 VÉRIFICATION CONTAINER DOCKER")
    
    try:
        result = subprocess.run(
            ["docker", "ps", "--filter", f"name={CONTAINER_NAME}", "--format", "{{.Names}}"],
            capture_output=True,
            text=True,
            check=True
        )
        
        if CONTAINER_NAME in result.stdout:
            print(f"✅ Container '{CONTAINER_NAME}' en cours d'exécution")
            return True
        else:
            print(f"❌ Container '{CONTAINER_NAME}' non trouvé ou arrêté")
            print("\nCommandes pour démarrer:")
            print(f"  cd docker-configurations/comfyui-qwen")
            print(f"  docker-compose up -d")
            return False
            
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur Docker: {e}")
        return False
    except FileNotFoundError:
        print("❌ Docker non trouvé. Assurez-vous que Docker est installé.")
        return False

def copy_to_container(local_path: Path) -> bool:
    """Copie les fichiers téléchargés dans le container Docker"""
    print_section("📦 COPIE VERS CONTAINER DOCKER")
    
    print(f"📁 Source: {local_path}")
    print(f"🎯 Destination: {CONTAINER_NAME}:{CONTAINER_PATH}")
    print()
    
    # Créer le répertoire cible dans le container
    try:
        subprocess.run(
            ["docker", "exec", CONTAINER_NAME, "mkdir", "-p", CONTAINER_PATH],
            check=True,
            capture_output=True
        )
        print(f"✅ Répertoire créé dans container: {CONTAINER_PATH}")
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur création répertoire: {e}")
        return False
    
    # Copier les fichiers
    try:
        # Docker cp nécessite un / à la fin pour copier le contenu
        source = f"{local_path}/."
        destination = f"{CONTAINER_NAME}:{CONTAINER_PATH}"
        
        print(f"\n⏳ Copie en cours...")
        subprocess.run(
            ["docker", "cp", source, destination],
            check=True
        )
        
        print(f"✅ Copie terminée")
        return True
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur lors de la copie: {e}")
        return False

def verify_in_container() -> bool:
    """Vérifie la présence des fichiers dans le container"""
    print_section("✅ VÉRIFICATION CONTAINER")
    
    try:
        result = subprocess.run(
            ["docker", "exec", CONTAINER_NAME, "ls", "-lh", CONTAINER_PATH],
            capture_output=True,
            text=True,
            check=True
        )
        
        print("📋 Contenu du répertoire dans container:")
        print(result.stdout)
        
        # Vérifier présence de fichiers .gguf
        if ".gguf" in result.stdout:
            print("✅ Fichiers .gguf détectés dans le container")
            return True
        else:
            print("❌ Aucun fichier .gguf trouvé dans le container")
            return False
            
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur vérification: {e}")
        return False

def cleanup_temp_dir():
    """Nettoie le répertoire temporaire"""
    print_section("🧹 NETTOYAGE")
    
    if TEMP_DIR.exists():
        try:
            shutil.rmtree(TEMP_DIR)
            print(f"✅ Répertoire temporaire supprimé: {TEMP_DIR}")
        except Exception as e:
            print(f"⚠️ Erreur nettoyage (non-bloquant): {e}")

def main():
    """Fonction principale"""
    print_section("🚀 TÉLÉCHARGEMENT MODÈLE QWEN2-VL Q4_K_M")
    print(f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"📁 Workspace: {Path.cwd()}")
    
    try:
        # 1. Vérifier dépendances
        check_dependencies()
        
        # 2. Charger token HuggingFace
        token = load_hf_token()
        
        # 3. Vérifier container Docker
        if not check_docker_container():
            print("\n⚠️ Container Docker non disponible. Arrêt du script.")
            sys.exit(1)
        
        # 4. Télécharger modèle
        local_path = download_model(token)
        
        # 5. Copier vers container
        if not copy_to_container(local_path):
            print("\n❌ Échec de la copie vers container")
            sys.exit(1)
        
        # 6. Vérifier présence dans container
        if not verify_in_container():
            print("\n❌ Vérification échouée")
            sys.exit(1)
        
        # 7. Nettoyer répertoire temporaire
        cleanup_temp_dir()
        
        # 8. Résumé final
        print_section("✅ MISSION ACCOMPLIE")
        print("📦 Modèle Qwen2-VL Q4_K_M téléchargé et installé avec succès")
        print(f"📁 Emplacement container: {CONTAINER_PATH}")
        print(f"🔖 Repository: {REPO_ID}")
        print(f"🔖 Révision: {REVISION}")
        print("\n📝 PROCHAINES ÉTAPES:")
        print("  - ÉTAPE 24G: Créer workflow custom nodes Q4")
        print("  - Installer custom node ComfyUI-GGUF si nécessaire")
        print("  - Tester génération d'image avec modèle Q4")
        
    except Exception as e:
        print(f"\n❌ ERREUR CRITIQUE: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main()