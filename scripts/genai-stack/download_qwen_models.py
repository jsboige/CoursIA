#!/usr/bin/env python3
"""
Script de Teleargement des Modeles Qwen FP8 pour ComfyUI
=========================================================

Source: Phase 29 - docs/suivis/genai-image/phase-29-corrections-qwen/SYNTHESE-COMPLETE-PHASE-29.md

Modeles requis (architecture officielle Comfy-Org):
1. qwen_image_edit_2509_fp8_e4m3fn.safetensors (20GB) - Diffusion Model
2. qwen_2.5_vl_7b_fp8_scaled.safetensors (8.8GB) - Text Encoder
3. qwen_image_vae.safetensors (243MB) - VAE

Usage:
    python scripts/genai-stack/download_qwen_models.py [--dest /path/to/models]
    python scripts/genai-stack/download_qwen_models.py --docker  # Pour container Docker
"""

import os
import sys
import argparse
import subprocess
from pathlib import Path
from typing import Optional

# Configuration des modeles
MODELS = [
    {
        "name": "Diffusion Model (UNET)",
        "repo_id": "Comfy-Org/Qwen-Image-Edit_ComfyUI",
        "filename": "split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "local_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "subdir": "diffusion_models",
        "size_gb": 20.0
    },
    {
        "name": "Text Encoder (CLIP)",
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "local_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "subdir": "text_encoders",
        "size_gb": 8.8
    },
    {
        "name": "VAE",
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/vae/qwen_image_vae.safetensors",
        "local_name": "qwen_image_vae.safetensors",
        "subdir": "vae",
        "size_gb": 0.243
    }
]

TOTAL_SIZE_GB = sum(m["size_gb"] for m in MODELS)


def print_section(title: str):
    print(f"\n{'='*70}")
    print(f"  {title}")
    print(f"{'='*70}\n")


def check_huggingface_hub():
    """Verifie que huggingface_hub est installe."""
    try:
        import huggingface_hub
        print(f"huggingface_hub version: {huggingface_hub.__version__}")
        return True
    except ImportError:
        print("ERREUR: huggingface_hub n'est pas installe")
        print("Installation: pip install huggingface_hub")
        return False


def get_hf_token() -> Optional[str]:
    """Recupere le token HuggingFace depuis les variables d'environnement ou fichiers."""
    # 1. Variable d'environnement
    token = os.environ.get("HF_TOKEN") or os.environ.get("HUGGINGFACE_TOKEN")
    if token:
        print("Token HuggingFace trouve dans les variables d'environnement")
        return token

    # 2. Fichier .secrets
    secrets_paths = [
        Path(".secrets/.env.huggingface"),
        Path("docker-configurations/.secrets/.env.huggingface"),
        Path.home() / ".huggingface" / "token",
    ]

    for path in secrets_paths:
        if path.exists():
            try:
                content = path.read_text().strip()
                if "=" in content:
                    token = content.split("=", 1)[1].strip()
                else:
                    token = content
                if token.startswith("hf_"):
                    print(f"Token HuggingFace trouve dans: {path}")
                    return token
            except Exception:
                continue

    print("Aucun token HuggingFace trouve (telechargement public uniquement)")
    return None


def download_model(model: dict, dest_base: Path, token: Optional[str] = None):
    """Telecharge un modele depuis HuggingFace Hub."""
    from huggingface_hub import hf_hub_download

    dest_dir = dest_base / model["subdir"]
    dest_dir.mkdir(parents=True, exist_ok=True)

    dest_file = dest_dir / model["local_name"]

    if dest_file.exists():
        size_gb = dest_file.stat().st_size / (1024**3)
        print(f"  [SKIP] {model['name']} - deja present ({size_gb:.2f} GB)")
        return True

    print(f"  [DOWN] {model['name']} ({model['size_gb']} GB)...")
    print(f"         Repo: {model['repo_id']}")
    print(f"         File: {model['filename']}")

    try:
        downloaded_path = hf_hub_download(
            repo_id=model["repo_id"],
            filename=model["filename"],
            local_dir=str(dest_base),
            local_dir_use_symlinks=False,
            token=token
        )

        # Deplacer vers le bon emplacement si necessaire
        downloaded = Path(downloaded_path)
        if downloaded != dest_file:
            import shutil
            shutil.move(str(downloaded), str(dest_file))

        size_gb = dest_file.stat().st_size / (1024**3)
        print(f"  [OK] Telecharge: {dest_file} ({size_gb:.2f} GB)")
        return True

    except Exception as e:
        print(f"  [ERR] Echec telechargement: {e}")
        return False


def download_to_docker(container_name: str = "comfyui-qwen"):
    """Telecharge les modeles directement dans le container Docker."""
    print_section("TELECHARGEMENT DANS CONTAINER DOCKER")

    # Verifier que le container existe
    result = subprocess.run(
        ["docker", "ps", "-a", "--filter", f"name={container_name}", "--format", "{{.Names}}"],
        capture_output=True, text=True
    )

    if container_name not in result.stdout:
        print(f"ERREUR: Container '{container_name}' non trouve")
        return False

    # Telecharger localement puis copier
    temp_dir = Path("./temp_qwen_models")
    temp_dir.mkdir(exist_ok=True)

    token = get_hf_token()

    for model in MODELS:
        print(f"\nTelechargement: {model['name']}...")
        if download_model(model, temp_dir, token):
            src = temp_dir / model["subdir"] / model["local_name"]
            dest = f"/workspace/ComfyUI/models/{model['subdir']}/"

            print(f"  Copie vers container: {dest}")
            subprocess.run([
                "docker", "exec", container_name, "mkdir", "-p", dest
            ])
            subprocess.run([
                "docker", "cp", str(src), f"{container_name}:{dest}"
            ])

    print("\nNettoyage des fichiers temporaires...")
    import shutil
    shutil.rmtree(temp_dir, ignore_errors=True)

    return True


def main():
    parser = argparse.ArgumentParser(description="Telecharge les modeles Qwen FP8 pour ComfyUI")
    parser.add_argument("--dest", type=str, default=None,
                       help="Repertoire de destination (defaut: models/)")
    parser.add_argument("--docker", action="store_true",
                       help="Telecharger directement dans le container Docker")
    parser.add_argument("--container", type=str, default="comfyui-qwen",
                       help="Nom du container Docker (defaut: comfyui-qwen)")
    args = parser.parse_args()

    print_section("TELECHARGEMENT MODELES QWEN FP8")
    print(f"Modeles a telecharger: {len(MODELS)}")
    print(f"Taille totale estimee: {TOTAL_SIZE_GB:.1f} GB")

    if not check_huggingface_hub():
        sys.exit(1)

    if args.docker:
        success = download_to_docker(args.container)
    else:
        dest = Path(args.dest) if args.dest else Path("docker-configurations/shared/models")
        print(f"Destination: {dest.absolute()}")

        token = get_hf_token()

        success = True
        for model in MODELS:
            if not download_model(model, dest, token):
                success = False

    print_section("RESULTAT")
    if success:
        print("Tous les modeles ont ete telecharges avec succes!")
    else:
        print("Certains modeles n'ont pas pu etre telecharges.")
        sys.exit(1)


if __name__ == "__main__":
    main()
