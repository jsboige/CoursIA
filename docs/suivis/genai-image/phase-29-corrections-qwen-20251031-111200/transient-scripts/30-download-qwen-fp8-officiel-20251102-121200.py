#!/usr/bin/env python3
"""
ÉTAPE 30 - Remplacement Modèle FP8 Non-Standard par Version Officielle
Phase 29 - Corrections Qwen ComfyUI
Date: 2025-11-02 12:12:00

MISSION:
- Valider disponibilité repo Comfy-Org/Qwen-Image-Edit_ComfyUI
- Supprimer ancien modèle non-standard (Qwen-Image-Edit-2509-FP8)
- Télécharger 3 fichiers .safetensors officiels (20GB total)
- Copier dans container Docker comfyui-qwen

FICHIERS CIBLES:
1. qwen_image_transformer.safetensors → /workspace/ComfyUI/models/checkpoints/
2. qwen_image_text_encoder.safetensors → /workspace/ComfyUI/models/text_encoders/
3. qwen_image_vae.safetensors → /workspace/ComfyUI/models/vae/

RÉFÉRENCES:
- Repository: https://huggingface.co/Comfy-Org/Qwen-Image-Edit_ComfyUI
- Token: .secrets/.env.huggingface
"""

import os
import sys
import subprocess
import shutil
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Optional

# Configuration
TOKEN_FILE = Path(".secrets/.env.huggingface")
TEMP_DIR = Path("./temp_qwen_fp8_download")
CONTAINER_NAME = "comfyui-qwen"

# Mapping fichiers → destinations dans container
# Format: (repo_id, filename, container_destination)
FILES_TO_DOWNLOAD = [
    {
        "repo_id": "Comfy-Org/Qwen-Image-Edit_ComfyUI",
        "filename": "split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "container_dest": "/workspace/ComfyUI/models/diffusion_models/",
        "expected_size_gb": 20.0
    },
    {
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "container_dest": "/workspace/ComfyUI/models/text_encoders/",
        "expected_size_gb": 9.0
    },
    {
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/vae/qwen_image_vae.safetensors",
        "container_dest": "/workspace/ComfyUI/models/vae/",
        "expected_size_gb": 0.25
    }
]

# Ancien modèle à supprimer
OLD_MODEL_PATH = "/home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/Qwen-Image-Edit-2509-FP8"

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

def validate_repos(token: str):
    """Valide la disponibilité de tous les repos et fichiers nécessaires"""
    print_section("🔍 VALIDATION REPOSITORIES HUGGINGFACE")
    
    from huggingface_hub import list_repo_files
    
    all_validated = True
    
    for idx, file_info in enumerate(FILES_TO_DOWNLOAD, 1):
        repo_id = file_info["repo_id"]
        filename = file_info["filename"]
        
        print(f"\n{idx}. Validation: {repo_id}")
        print(f"   Fichier: {filename}")
        
        try:
            all_files = list_repo_files(repo_id, repo_type="model", token=token)
            
            if filename in all_files:
                print(f"   ✅ Fichier trouvé")
            else:
                print(f"   ❌ Fichier NON trouvé")
                print(f"   Fichiers disponibles dans {repo_id}:")
                safetensors_files = [f for f in all_files if f.endswith(".safetensors")]
                for f in safetensors_files[:5]:  # Limite à 5 pour lisibilité
                    print(f"     - {f}")
                all_validated = False
                
        except Exception as e:
            print(f"   ❌ Erreur accès repository: {e}")
            all_validated = False
    
    if not all_validated:
        raise ValueError("Un ou plusieurs fichiers sont inaccessibles")
    
    print(f"\n✅ Tous les fichiers sont accessibles dans leurs repositories respectifs")

def remove_old_model():
    """Supprime l'ancien modèle non-standard via WSL bash"""
    print_section("🗑️ SUPPRESSION ANCIEN MODÈLE NON-STANDARD")
    
    print(f"📁 Chemin WSL: {OLD_MODEL_PATH}")
    
    # Vérifier d'abord si le répertoire existe
    check_cmd = ["wsl", "bash", "-c", f"test -d {OLD_MODEL_PATH} && echo 'EXISTS' || echo 'NOT_FOUND'"]
    
    try:
        result = subprocess.run(check_cmd, capture_output=True, text=True, check=True)
        
        if "NOT_FOUND" in result.stdout:
            print(f"⚠️ Ancien modèle déjà absent: {OLD_MODEL_PATH}")
            return
        
        # Supprimer le répertoire
        print(f"⏳ Suppression en cours...")
        rm_cmd = ["wsl", "bash", "-c", f"rm -rf {OLD_MODEL_PATH}"]
        subprocess.run(rm_cmd, check=True, capture_output=True)
        
        print(f"✅ Ancien modèle supprimé avec succès")
        
        # Vérifier suppression
        verify_cmd = ["wsl", "bash", "-c", f"ls -la /home/jesse/SD/workspace/comfyui-qwen/ComfyUI/models/checkpoints/"]
        result = subprocess.run(verify_cmd, capture_output=True, text=True)
        
        if "Qwen-Image-Edit-2509-FP8" not in result.stdout:
            print(f"✅ Vérification suppression OK")
        else:
            print(f"⚠️ Le répertoire semble toujours présent")
            
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur lors de la suppression: {e}")
        print(f"stderr: {e.stderr if hasattr(e, 'stderr') else 'N/A'}")
        raise

def download_file(token: str, file_info: dict) -> Path:
    """Télécharge un fichier depuis HuggingFace"""
    from huggingface_hub import hf_hub_download
    
    repo_id = file_info["repo_id"]
    filename = file_info["filename"]
    expected_size_gb = file_info["expected_size_gb"]
    
    print(f"\n{'─'*60}")
    print(f"📥 Téléchargement: {filename}")
    print(f"📦 Repository: {repo_id}")
    print(f"📊 Taille attendue: ~{expected_size_gb:.2f} GB")
    print(f"{'─'*60}\n")
    
    # Créer répertoire temporaire si nécessaire
    TEMP_DIR.mkdir(parents=True, exist_ok=True)
    
    start_time = datetime.now()
    
    try:
        local_file = hf_hub_download(
            repo_id=repo_id,
            filename=filename,
            token=token,
            local_dir=str(TEMP_DIR),
            local_dir_use_symlinks=False  # Copie réelle
        )
        
        end_time = datetime.now()
        duration = (end_time - start_time).total_seconds()
        
        # Vérifier taille fichier
        file_path = Path(local_file)
        size_mb = file_path.stat().st_size / (1024 * 1024)
        size_gb = size_mb / 1024
        
        print(f"✅ Téléchargement terminé en {duration:.2f}s ({duration/60:.2f} min)")
        print(f"💾 Taille réelle: {size_mb:.2f} MB ({size_gb:.2f} GB)")
        
        # Vérifier cohérence taille
        if abs(size_gb - expected_size_gb) > (expected_size_gb * 0.2):  # Tolérance 20%
            print(f"⚠️ Attention: Taille différente de l'attendu ({expected_size_gb:.2f} GB)")
        
        return file_path
        
    except Exception as e:
        print(f"❌ Erreur téléchargement {filename}: {e}")
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

def copy_to_container(local_file: Path, container_dest: str) -> bool:
    """Copie un fichier dans le container Docker"""
    filename = local_file.name
    
    print(f"\n{'─'*60}")
    print(f"📦 Copie: {filename}")
    print(f"🎯 Destination: {CONTAINER_NAME}:{container_dest}")
    print(f"{'─'*60}\n")
    
    # Debug: Afficher chemin source
    print(f"🔍 Source locale: {local_file}")
    print(f"🔍 Fichier existe: {local_file.exists()}")
    
    if not local_file.exists():
        print(f"❌ Fichier source introuvable: {local_file}")
        return False
    
    # Créer le répertoire cible dans le container
    try:
        subprocess.run(
            ["docker", "exec", CONTAINER_NAME, "mkdir", "-p", container_dest],
            check=True,
            capture_output=True
        )
        print(f"✅ Répertoire créé/vérifié: {container_dest}")
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur création répertoire: {e}")
        return False
    
    # Copier le fichier
    try:
        # Convertir en chemin absolu et utiliser format Windows natif
        source = str(local_file.resolve())
        destination = f"{CONTAINER_NAME}:{container_dest}{filename}"
        
        print(f"🔍 Commande: docker cp {source} {destination}")
        print(f"⏳ Copie en cours...")
        
        result = subprocess.run(
            ["docker", "cp", source, destination],
            check=True,
            capture_output=True,
            text=True
        )
        
        if result.stdout:
            print(f"📋 {result.stdout.strip()}")
        
        print(f"✅ Copie terminée")
        return True
        
    except subprocess.CalledProcessError as e:
        print(f"❌ Erreur lors de la copie: {e}")
        print(f"stderr: {e.stderr if hasattr(e, 'stderr') and e.stderr else 'N/A'}")
        return False

def verify_file_in_container(container_path: str, filename: str) -> bool:
    """Vérifie la présence et taille d'un fichier dans le container"""
    full_path = f"{container_path}{filename}"
    
    try:
        result = subprocess.run(
            ["docker", "exec", CONTAINER_NAME, "ls", "-lh", full_path],
            capture_output=True,
            text=True,
            check=True
        )
        
        print(f"✅ Fichier vérifié: {filename}")
        print(f"   {result.stdout.strip()}")
        return True
        
    except subprocess.CalledProcessError:
        print(f"❌ Fichier non trouvé: {full_path}")
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
    print_section("🚀 REMPLACEMENT MODÈLE FP8 NON-STANDARD → OFFICIEL")
    print(f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"📁 Workspace: {Path.cwd()}")
    
    stats = {
        "start_time": datetime.now(),
        "files_downloaded": [],
        "files_copied": [],
        "total_size_gb": 0.0
    }
    
    try:
        # 1. Vérifier dépendances
        check_dependencies()
        
        # 2. Charger token HuggingFace
        token = load_hf_token()
        
        # 3. Valider repositories
        validate_repos(token)
        
        # 4. Vérifier container Docker
        if not check_docker_container():
            print("\n⚠️ Container Docker non disponible. Arrêt du script.")
            sys.exit(1)
        
        # 5. Supprimer ancien modèle
        remove_old_model()
        
        # 6. Télécharger et copier chaque fichier
        print_section("⬇️ TÉLÉCHARGEMENT ET COPIE DES FICHIERS")
        
        for file_info in FILES_TO_DOWNLOAD:
            # Télécharger
            local_file = download_file(token, file_info)
            filename = Path(file_info["filename"]).name
            stats["files_downloaded"].append(filename)
            
            # Calculer taille
            size_gb = local_file.stat().st_size / (1024 * 1024 * 1024)
            stats["total_size_gb"] += size_gb
            
            # Copier dans container
            container_dest = file_info["container_dest"]
            if not copy_to_container(local_file, container_dest):
                print(f"\n❌ Échec copie {filename}")
                sys.exit(1)
            
            stats["files_copied"].append(filename)
            
            # Vérifier présence
            if not verify_file_in_container(container_dest, filename):
                print(f"\n❌ Vérification échouée pour {filename}")
                sys.exit(1)
        
        # 7. Nettoyer répertoire temporaire
        cleanup_temp_dir()
        
        # 8. Résumé final
        stats["end_time"] = datetime.now()
        stats["duration"] = (stats["end_time"] - stats["start_time"]).total_seconds()
        
        print_section("✅ MISSION ACCOMPLIE")
        print("📦 Modèle FP8 officiel installé avec succès\n")
        print("📊 STATISTIQUES:")
        print(f"  - Fichiers téléchargés: {len(stats['files_downloaded'])}")
        print(f"  - Taille totale: {stats['total_size_gb']:.2f} GB")
        print(f"  - Durée totale: {stats['duration']:.2f}s ({stats['duration']/60:.2f} min)\n")
        
        print("📁 FICHIERS INSTALLÉS:")
        for file_info in FILES_TO_DOWNLOAD:
            filename = Path(file_info["filename"]).name
            dest = file_info["container_dest"]
            print(f"  ✅ {filename}")
            print(f"     → {dest}")
        
        print("\n🗑️ ANCIEN MODÈLE SUPPRIMÉ:")
        print(f"  ✅ {OLD_MODEL_PATH}")
        
        print("\n📝 PROCHAINES ÉTAPES:")
        print("  - Redémarrer container si nécessaire (docker-compose restart)")
        print("  - Tester génération d'image avec workflow officiel")
        print("  - Créer rapport SDDD dans docs/suivis/genai-image/phase-29/rapports/")
        
    except Exception as e:
        print(f"\n❌ ERREUR CRITIQUE: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main()