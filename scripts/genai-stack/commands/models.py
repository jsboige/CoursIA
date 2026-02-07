#!/usr/bin/env python3
"""
commands/models.py - Gestion des modeles GenAI

Sous-commandes :
    genai.py models download-qwen       # Telecharger modeles Qwen FP8 (~29GB)
    genai.py models download-nunchaku   # Telecharger modeles Nunchaku INT4 (~4GB)
    genai.py models setup-zimage        # Configurer Z-Image/Lumina
    genai.py models list-checkpoints    # Lister checkpoints ComfyUI
    genai.py models list-nodes          # Lister custom nodes ComfyUI
"""

import os
import sys
import json
import time
import subprocess
import ssl
import urllib.request
from pathlib import Path
from typing import Optional, List, Dict

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import SHARED_MODELS_DIR, SERVICES_DIR


# --- Modeles Qwen FP8 ---

QWEN_MODELS = [
    {
        "name": "Diffusion Model (UNET)",
        "repo_id": "Comfy-Org/Qwen-Image-Edit_ComfyUI",
        "filename": "split_files/diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "local_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "subdir": "diffusion_models",
        "size_gb": 20.0,
    },
    {
        "name": "Text Encoder (CLIP)",
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "local_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "subdir": "text_encoders",
        "size_gb": 8.8,
    },
    {
        "name": "VAE",
        "repo_id": "Comfy-Org/Qwen-Image_ComfyUI",
        "filename": "split_files/vae/qwen_image_vae.safetensors",
        "local_name": "qwen_image_vae.safetensors",
        "subdir": "vae",
        "size_gb": 0.243,
    },
]

# --- Modeles Nunchaku INT4 ---

NUNCHAKU_MODELS = {
    "lightning-4step-r128": "svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors",
    "lightning-4step-r32": "svdq-int4_r32-qwen-image-edit-lightningv1.0-4steps.safetensors",
    "lightning-8step-r128": "svdq-int4_r128-qwen-image-edit-lightningv1.0-8steps.safetensors",
    "lightning-8step-r32": "svdq-int4_r32-qwen-image-edit-lightningv1.0-8steps.safetensors",
    "standard-r128": "svdq-int4_r128-qwen-image-edit.safetensors",
    "standard-r32": "svdq-int4_r32-qwen-image-edit.safetensors",
}

NUNCHAKU_REPO_ID = "nunchaku-ai/nunchaku-qwen-image-edit"

# --- Z-Image ---

ZIMAGE_VAE_CONFIG = {
    "url": "https://huggingface.co/madebyollin/sdxl-vae-fp16-fix/resolve/main/sdxl_vae.safetensors",
    "filename": "sdxl_vae.safetensors",
    "subfolder": "vae",
}


def _get_hf_token() -> Optional[str]:
    """Recupere le token HuggingFace."""
    token = os.environ.get("HF_TOKEN") or os.environ.get("HUGGINGFACE_TOKEN")
    if token:
        return token

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
                    return token
            except Exception:
                continue
    return None


def _ensure_huggingface_hub():
    """Verifie que huggingface_hub est installe."""
    try:
        import huggingface_hub
        return True
    except ImportError:
        print("Installation huggingface_hub...")
        subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "huggingface_hub"])
        return True


# --- Sous-commande download-qwen ---

def download_qwen(dest: Optional[str] = None, docker: bool = False, container: str = "comfyui-qwen"):
    """Telecharge les modeles Qwen FP8."""
    if not _ensure_huggingface_hub():
        return False
    from huggingface_hub import hf_hub_download

    total_gb = sum(m["size_gb"] for m in QWEN_MODELS)
    print(f"Modeles Qwen FP8: {len(QWEN_MODELS)} fichiers, ~{total_gb:.1f} GB")

    token = _get_hf_token()
    dest_base = Path(dest) if dest else SHARED_MODELS_DIR

    if docker:
        return _download_qwen_docker(container, token)

    print(f"Destination: {dest_base.absolute()}")
    success = True
    for model in QWEN_MODELS:
        dest_dir = dest_base / model["subdir"]
        dest_dir.mkdir(parents=True, exist_ok=True)
        dest_file = dest_dir / model["local_name"]

        if dest_file.exists():
            size_gb = dest_file.stat().st_size / (1024**3)
            print(f"  [SKIP] {model['name']} ({size_gb:.2f} GB)")
            continue

        print(f"  [DOWN] {model['name']} ({model['size_gb']} GB)...")
        try:
            downloaded_path = hf_hub_download(
                repo_id=model["repo_id"],
                filename=model["filename"],
                local_dir=str(dest_base),
                local_dir_use_symlinks=False,
                token=token,
            )
            downloaded = Path(downloaded_path)
            if downloaded != dest_file:
                import shutil
                shutil.move(str(downloaded), str(dest_file))
            print(f"  [OK] {dest_file}")
        except Exception as e:
            print(f"  [ERR] {e}")
            success = False
    return success


def _download_qwen_docker(container: str, token: Optional[str]) -> bool:
    """Telecharge les modeles dans un container Docker."""
    result = subprocess.run(
        ["docker", "ps", "-a", "--filter", f"name={container}", "--format", "{{{{.Names}}}}"],
        capture_output=True, text=True,
    )
    if container not in result.stdout:
        print(f"Container '{container}' non trouve")
        return False

    temp_dir = Path("./temp_qwen_models")
    temp_dir.mkdir(exist_ok=True)

    from huggingface_hub import hf_hub_download

    for model in QWEN_MODELS:
        dest_dir = temp_dir / model["subdir"]
        dest_dir.mkdir(parents=True, exist_ok=True)
        dest_file = dest_dir / model["local_name"]

        if not dest_file.exists():
            try:
                hf_hub_download(
                    repo_id=model["repo_id"],
                    filename=model["filename"],
                    local_dir=str(temp_dir),
                    local_dir_use_symlinks=False,
                    token=token,
                )
            except Exception as e:
                print(f"  [ERR] {e}")
                continue

        dest_container = f"/workspace/ComfyUI/models/{model['subdir']}/"
        subprocess.run(["docker", "exec", container, "mkdir", "-p", dest_container])
        subprocess.run(["docker", "cp", str(dest_file), f"{container}:{dest_container}"])

    import shutil
    shutil.rmtree(temp_dir, ignore_errors=True)
    return True


# --- Sous-commande download-nunchaku ---

def download_nunchaku(model_key: str = "lightning-4step-r128",
                      output_dir: Optional[str] = None,
                      list_models: bool = False):
    """Telecharge un modele Nunchaku INT4."""
    if list_models:
        print("Modeles Nunchaku disponibles:")
        for key, filename in NUNCHAKU_MODELS.items():
            print(f"  {key:25} -> {filename}")
        return True

    if model_key not in NUNCHAKU_MODELS:
        print(f"Modele inconnu: '{model_key}'")
        print(f"Disponibles: {', '.join(NUNCHAKU_MODELS.keys())}")
        return False

    if not _ensure_huggingface_hub():
        return False
    from huggingface_hub import hf_hub_download

    dest = Path(output_dir) if output_dir else SHARED_MODELS_DIR / "diffusion_models"
    dest.mkdir(parents=True, exist_ok=True)
    filename = NUNCHAKU_MODELS[model_key]
    output_path = dest / filename

    if output_path.exists():
        print(f"Modele deja present: {output_path}")
        return True

    print(f"Telechargement {filename} depuis {NUNCHAKU_REPO_ID}...")
    token = os.environ.get("HF_TOKEN")
    try:
        hf_hub_download(
            repo_id=NUNCHAKU_REPO_ID,
            filename=filename,
            local_dir=dest,
            token=token,
            local_dir_use_symlinks=False,
        )
        print(f"Telecharge: {output_path}")
        return True
    except Exception as e:
        print(f"Erreur: {e}")
        return False


# --- Sous-commande setup-zimage ---

def setup_zimage():
    """Configure Z-Image/Lumina : telecharge VAE et genere workflow."""
    ssl._create_default_https_context = ssl._create_unverified_context

    models_dir = SHARED_MODELS_DIR
    workspace_dir = SERVICES_DIR / "comfyui-qwen" / "workspace"

    # Telecharger VAE
    config = ZIMAGE_VAE_CONFIG
    target_dir = models_dir / config["subfolder"]
    target_dir.mkdir(parents=True, exist_ok=True)
    target_file = target_dir / config["filename"]

    if target_file.exists():
        print(f"  VAE deja present: {target_file.name}")
    else:
        print(f"  Telechargement VAE: {config['filename']}...")
        try:
            with urllib.request.urlopen(config["url"]) as response:
                total = int(response.info().get('Content-Length', 0))
                downloaded = 0
                with open(target_file, 'wb') as f:
                    while True:
                        buf = response.read(8192)
                        if not buf:
                            break
                        downloaded += len(buf)
                        f.write(buf)
                        if total:
                            pct = downloaded * 100 / total
                            sys.stdout.write(f"\r  {pct:.1f}%")
                            sys.stdout.flush()
            print(f"\n  OK: {target_file}")
        except Exception as e:
            print(f"\n  Erreur: {e}")
            if target_file.exists():
                os.remove(target_file)
            return False

    # Generer workflow
    workflow = {
        "1": {
            "inputs": {
                "model_path": "Alpha-VLLM/Lumina-Next-SFT-diffusers",
                "prompt": "A cinematic shot of a cyberpunk samurai in a neon city, raining, reflections, 8k, highly detailed, photorealistic",
                "negative_prompt": "blur, low quality, watermark, text, logo, bad anatomy, deformed",
                "num_inference_steps": 20,
                "guidance_scale": 4.0,
                "seed": 42,
                "batch_size": 1,
                "scaling_watershed": 0.3,
                "proportional_attn": True,
                "clean_caption": True,
                "max_sequence_length": 256,
                "use_time_shift": False,
                "t_shift": 4,
                "strength": 1.0,
            },
            "class_type": "LuminaDiffusersNode",
            "_meta": {"title": "Lumina-Next-SFT Diffusers"},
        },
        "8": {
            "inputs": {"samples": ["1", 0], "vae": ["9", 0]},
            "class_type": "VAEDecode",
            "_meta": {"title": "VAE Decode"},
        },
        "9": {
            "inputs": {"vae_name": config["filename"]},
            "class_type": "VAELoader",
            "_meta": {"title": "VAE Loader"},
        },
        "11": {
            "inputs": {"filename_prefix": "Z-Image-Reboot", "images": ["8", 0]},
            "class_type": "SaveImage",
            "_meta": {"title": "Save Image"},
        },
    }

    workspace_dir.mkdir(parents=True, exist_ok=True)
    wf_path = workspace_dir / "workflow_z_image_reboot.json"
    with open(wf_path, "w", encoding="utf-8") as f:
        json.dump(workflow, f, indent=2)
    print(f"  Workflow genere: {wf_path}")
    return True


# --- Sous-commandes list ---

def list_checkpoints():
    """Liste les checkpoints disponibles dans ComfyUI."""
    from core.auth_manager import GenAIAuthManager
    from core.comfyui_client import ComfyUIClient, ComfyUIConfig

    auth = GenAIAuthManager()
    config = auth.load_config()
    token = config.get('bcrypt_hash') if config else None
    client = ComfyUIClient(ComfyUIConfig(api_key=token))

    print("Recuperation des checkpoints...")
    try:
        info = client.get_object_info("CheckpointLoaderSimple")
        input_info = info['CheckpointLoaderSimple']['input']['required']['ckpt_name']
        models = input_info[0]
        print(f"Modeles trouves ({len(models)}):")
        for m in models:
            print(f"  - {m}")
        return True
    except Exception as e:
        print(f"Erreur: {e}")
        return False


def list_nodes():
    """Liste les custom nodes Qwen et Wrapper dans ComfyUI."""
    from core.auth_manager import GenAIAuthManager
    from core.comfyui_client import ComfyUIClient, ComfyUIConfig

    auth = GenAIAuthManager()
    config = auth.load_config()
    token = config.get('bcrypt_hash') if config else None
    client = ComfyUIClient(ComfyUIConfig(api_key=token))

    print("Recuperation des noeuds...")
    try:
        info = client.get_object_info()
        qwen_nodes = [k for k in info.keys() if "Qwen" in k]
        print(f"Noeuds Qwen ({len(qwen_nodes)}):")
        for node in qwen_nodes:
            print(f"  - {node}")

        nunchaku_nodes = [k for k in info.keys() if "Nunchaku" in k]
        print(f"\nNoeuds Nunchaku ({len(nunchaku_nodes)}):")
        for node in nunchaku_nodes:
            print(f"  - {node}")

        wrapper_nodes = [k for k in info.keys() if "Wrapper" in k]
        if wrapper_nodes:
            print(f"\nNoeuds Wrapper ({len(wrapper_nodes)}):")
            for node in wrapper_nodes:
                print(f"  - {node}")
        return True
    except Exception as e:
        print(f"Erreur: {e}")
        return False


# --- CLI ---

def register(subparsers):
    """Enregistre la sous-commande models."""
    parser = subparsers.add_parser('models', help='Gestion des modeles GenAI')
    sub = parser.add_subparsers(dest='models_action')

    # download-qwen
    p_qwen = sub.add_parser('download-qwen', help='Telecharger modeles Qwen FP8 (~29GB)')
    p_qwen.add_argument('--dest', type=str, help='Repertoire destination')
    p_qwen.add_argument('--docker', action='store_true', help='Telecharger dans container Docker')
    p_qwen.add_argument('--container', type=str, default='comfyui-qwen')

    # download-nunchaku
    p_nunchaku = sub.add_parser('download-nunchaku', help='Telecharger modeles Nunchaku INT4 (~4GB)')
    p_nunchaku.add_argument('--model', '-m', type=str, default='lightning-4step-r128',
                           choices=list(NUNCHAKU_MODELS.keys()))
    p_nunchaku.add_argument('--output-dir', '-o', type=str)
    p_nunchaku.add_argument('--list', '-l', action='store_true', help='Lister les modeles disponibles')

    # setup-zimage
    sub.add_parser('setup-zimage', help='Configurer Z-Image/Lumina')

    # list-checkpoints
    sub.add_parser('list-checkpoints', help='Lister checkpoints ComfyUI')

    # list-nodes
    sub.add_parser('list-nodes', help='Lister custom nodes ComfyUI')


def execute(args) -> int:
    """Execute la commande models."""
    action = getattr(args, 'models_action', None)

    if action == 'download-qwen':
        ok = download_qwen(dest=args.dest, docker=args.docker, container=args.container)
        return 0 if ok else 1

    elif action == 'download-nunchaku':
        ok = download_nunchaku(
            model_key=args.model,
            output_dir=getattr(args, 'output_dir', None),
            list_models=getattr(args, 'list', False),
        )
        return 0 if ok else 1

    elif action == 'setup-zimage':
        ok = setup_zimage()
        return 0 if ok else 1

    elif action == 'list-checkpoints':
        ok = list_checkpoints()
        return 0 if ok else 1

    elif action == 'list-nodes':
        ok = list_nodes()
        return 0 if ok else 1

    else:
        print("Utilisation: genai.py models <download-qwen|download-nunchaku|setup-zimage|list-checkpoints|list-nodes>")
        return 1


def main():
    """Point d'entree standalone."""
    import argparse
    parser = argparse.ArgumentParser(description="Gestion des modeles GenAI")
    register_sub = parser.add_subparsers(dest='models_action')

    p_qwen = register_sub.add_parser('download-qwen')
    p_qwen.add_argument('--dest', type=str)
    p_qwen.add_argument('--docker', action='store_true')
    p_qwen.add_argument('--container', type=str, default='comfyui-qwen')

    p_nunchaku = register_sub.add_parser('download-nunchaku')
    p_nunchaku.add_argument('--model', '-m', type=str, default='lightning-4step-r128',
                           choices=list(NUNCHAKU_MODELS.keys()))
    p_nunchaku.add_argument('--output-dir', '-o', type=str)
    p_nunchaku.add_argument('--list', '-l', action='store_true')

    register_sub.add_parser('setup-zimage')
    register_sub.add_parser('list-checkpoints')
    register_sub.add_parser('list-nodes')

    args = parser.parse_args()
    sys.exit(execute(args))


def main_download_qwen():
    """Point d'entree standalone pour download_qwen (retrocompatibilite)."""
    import argparse
    parser = argparse.ArgumentParser(description="Telecharger modeles Qwen FP8")
    parser.add_argument('--dest', type=str, help='Repertoire destination')
    parser.add_argument('--docker', action='store_true', help='Telecharger dans container Docker')
    parser.add_argument('--container', type=str, default='comfyui-qwen')
    args = parser.parse_args()
    ok = download_qwen(dest=args.dest, docker=args.docker, container=args.container)
    sys.exit(0 if ok else 1)


def main_download_nunchaku():
    """Point d'entree standalone pour download_nunchaku (retrocompatibilite)."""
    import argparse
    parser = argparse.ArgumentParser(description="Telecharger modeles Nunchaku INT4")
    parser.add_argument('--model', '-m', type=str, default='lightning-4step-r128',
                       choices=list(NUNCHAKU_MODELS.keys()))
    parser.add_argument('--output-dir', '-o', type=str)
    parser.add_argument('--list', '-l', action='store_true')
    args = parser.parse_args()
    ok = download_nunchaku(model_key=args.model, output_dir=args.output_dir,
                           list_models=getattr(args, 'list', False))
    sys.exit(0 if ok else 1)


def main_setup_zimage():
    """Point d'entree standalone pour setup_zimage (retrocompatibilite)."""
    ok = setup_zimage()
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
