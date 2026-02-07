#!/usr/bin/env python3
"""
config.py - Configuration partagee pour la stack GenAI

Source unique pour les constantes, chemins, services et configurations
utilisees par toutes les sous-commandes du CLI genai.py.
"""

from pathlib import Path
from typing import Dict, Any

# Chemins
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
DOCKER_CONFIG_DIR = PROJECT_ROOT / "docker-configurations"
SERVICES_DIR = DOCKER_CONFIG_DIR / "services"
SHARED_MODELS_DIR = DOCKER_CONFIG_DIR / "shared" / "models"
GENAI_DIR = PROJECT_ROOT / "MyIA.AI.Notebooks" / "GenAI"
ENV_FILE = GENAI_DIR / ".env"
SECRETS_DIR = PROJECT_ROOT / ".secrets"
WORKFLOWS_DIR = SCRIPT_DIR / "workflows"


def load_env() -> Dict[str, str]:
    """Charge les variables d'environnement depuis le fichier .env GenAI."""
    env_vars = {}
    if ENV_FILE.exists():
        with open(ENV_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    env_vars[key.strip()] = value.strip().strip('"').strip("'")
    return env_vars


# --- Services Docker ---

SERVICES: Dict[str, Dict[str, Any]] = {
    "comfyui-qwen": {
        "compose_dir": SERVICES_DIR / "comfyui-qwen",
        "container_name": "comfyui-qwen",
        "port": 8188,
        "health_endpoint": "/system_stats",
        "auth_type": "bearer",
        "auth_env_var": "COMFYUI_API_TOKEN",
        "gpu_id": 0,
        "vram_required": "20GB+",
        "remote_url": "https://qwen-image-edit.myia.io",
    },
    "forge-turbo": {
        "compose_dir": SERVICES_DIR / "forge-turbo",
        "container_name": "forge-turbo",
        "port": 17861,
        "health_endpoint": "/sdapi/v1/options",
        "auth_type": "basic",
        "auth_env_vars": ["FORGE_USER", "FORGE_PASSWORD"],
        "gpu_id": 1,
        "vram_required": "8GB+",
        "remote_url": "https://turbo.stable-diffusion-webui-forge.myia.io",
    },
    "vllm-zimage": {
        "compose_dir": SERVICES_DIR / "vllm-zimage",
        "container_name": "vllm-zimage",
        "port": 8001,
        "health_endpoint": "/health",
        "auth_type": None,
        "gpu_id": 1,
        "vram_required": "15GB+",
        "remote_url": "https://z-image.myia.io",
        "generation_endpoint": "/v1/images/generations",
    },
}


# --- Constantes ComfyUI ---

COMFYUI_URL = "http://localhost:8188"
FORGE_URL = "http://localhost:17861"
VLLM_ZIMAGE_URL = "http://localhost:8001"

# Nodes Qwen natifs (fournis par ComfyUI core)
EXPECTED_QWEN_NODES = [
    "ModelMergeQwenImage",
    "TextEncodeQwenImageEdit",
    "TextEncodeQwenImageEditPlus",
    "QwenImageDiffsynthControlnet",
]

# Nodes Nunchaku (fournis par ComfyUI-nunchaku plugin)
EXPECTED_NUNCHAKU_NODES = [
    "NunchakuQwenImageDiTLoader",
    "NunchakuLoraLoader",
]

# Nodes natifs ComfyUI requis pour le workflow Qwen Phase 29
REQUIRED_NATIVE_NODES = [
    "VAELoader",
    "CLIPLoader",
    "UNETLoader",
    "ModelSamplingAuraFlow",
    "CFGNorm",
    "ConditioningZeroOut",
    "EmptySD3LatentImage",
    "KSampler",
    "VAEDecode",
    "SaveImage",
]


# --- Mapping notebooks -> services ---

NOTEBOOK_SERVICE_MAP = {
    "cloud": [
        "00-1-Environment-Setup.ipynb",
        "00-2-Docker-Services-Management.ipynb",
        "00-3-API-Endpoints-Configuration.ipynb",
        "00-4-Environment-Validation.ipynb",
        "00-5-ComfyUI-Local-Test.ipynb",
        "01-1-OpenAI-DALL-E-3.ipynb",
        "01-2-GPT-5-Image-Generation.ipynb",
        "01-3-Basic-Image-Operations.ipynb",
    ],
    "forge": [
        "01-4-Forge-SD-XL-Turbo.ipynb",
    ],
    "qwen": [
        "01-5-Qwen-Image-Edit.ipynb",
        "02-1-Qwen-Image-Edit-2509.ipynb",
    ],
    "zimage": [
        "02-4-Z-Image-Lumina2.ipynb",
    ],
    "multi": [
        "02-2-FLUX-1-Advanced-Generation.ipynb",
        "02-3-Stable-Diffusion-3-5.ipynb",
        "03-1-Multi-Model-Comparison.ipynb",
        "03-2-Workflow-Orchestration.ipynb",
        "03-3-Performance-Optimization.ipynb",
    ],
    "apps": [
        "04-1-Educational-Content-Generation.ipynb",
        "04-2-Creative-Workflows.ipynb",
        "04-3-Production-Integration.ipynb",
    ],
}


# --- Configurations modeles ---

MODEL_CONFIGS = {
    "nunchaku": {
        "unet": "svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors",
        "clip": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "vae": "qwen_image_vae.safetensors",
        "vram_required_mb": 4000,
        "steps": 4,
        "cfg": 1.0,
        "workflow": "workflow_qwen_nunchaku_t2i.json",
    },
    "qwen": {
        "unet": "qwen-image-edit-2511-Q4_K_M.gguf",
        "clip": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "vae": "qwen_image_vae.safetensors",
        "lora": "Qwen-Image-Edit-2511-Lightning-4steps-V1.0-bf16.safetensors",
        "vram_required_mb": 13100,
        "steps": 4,
        "cfg": 1.0,
    },
    "qwen_fp8": {
        "unet": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
        "clip": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
        "vae": "qwen_image_vae.safetensors",
        "vram_required_mb": 29000,
        "steps": 20,
        "cfg": 1.0,
        "workflow": "workflow_qwen_native_t2i.json",
    },
    "zimage": {
        "checkpoint": "Lumina-Next-SFT",
        "unet": "z_image_turbo-Q5_K_M.gguf",
        "vae": "sdxl_vae.safetensors",
        "vram_required_mb": 10000,
    },
}
