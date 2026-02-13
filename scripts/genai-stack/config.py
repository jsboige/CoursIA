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
    # --- Services Image (existants) ---
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
    # --- Services Audio (nouveau) ---
    "whisper-webui": {
        "compose_dir": SERVICES_DIR / "whisper-webui",
        "container_name": "whisper-webui",
        "port": 36540,
        "health_endpoint": "/",
        "auth_type": "basic",
        "auth_env_vars": ["WHISPER_USER", "WHISPER_PASSWORD"],
        "gpu_id": 0,
        "vram_required": "10GB+",
        "remote_url": "https://whisper-webui.myia.io",
    },
    # --- Services Video (nouveau) ---
    "comfyui-video": {
        "compose_dir": SERVICES_DIR / "comfyui-video",
        "container_name": "comfyui-video",
        "port": 8189,
        "health_endpoint": "/system_stats",
        "auth_type": "bearer",
        "auth_env_var": "COMFYUI_VIDEO_TOKEN",
        "gpu_id": 0,
        "vram_required": "20GB+",
    },
}


# --- Constantes ComfyUI ---

COMFYUI_URL = "http://localhost:8188"
FORGE_URL = "http://localhost:17861"
VLLM_ZIMAGE_URL = "http://localhost:8001"
WHISPER_URL = "http://localhost:36540"
WHISPER_REMOTE_URL = "https://whisper-webui.myia.io"
COMFYUI_VIDEO_URL = "http://localhost:8189"

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
    # --- Image (existant) ---
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

    # --- Audio ---
    "audio_api": [
        "01-1-OpenAI-TTS-Intro.ipynb",
        "01-2-OpenAI-Whisper-STT.ipynb",
        "03-3-Realtime-Voice-API.ipynb",
    ],
    "audio_local": [
        "01-3-Basic-Audio-Operations.ipynb",
    ],
    "audio_whisper": [
        "01-4-Whisper-Local.ipynb",
    ],
    "audio_tts_light": [
        "01-5-Kokoro-TTS-Local.ipynb",
    ],
    "audio_tts_heavy": [
        "02-1-Chatterbox-TTS.ipynb",
        "02-2-XTTS-Voice-Cloning.ipynb",
    ],
    "audio_music": [
        "02-3-MusicGen-Generation.ipynb",
        "02-4-Demucs-Source-Separation.ipynb",
    ],
    "audio_orchestration": [
        "03-1-Multi-Model-Audio-Comparison.ipynb",
        "03-2-Audio-Pipeline-Orchestration.ipynb",
    ],
    "audio_apps": [
        "04-1-Educational-Audio-Content.ipynb",
        "04-2-Transcription-Pipeline.ipynb",
        "04-3-Music-Composition-Workflow.ipynb",
        "04-4-Audio-Video-Sync.ipynb",
    ],

    # --- Video ---
    "video_api": [
        "01-2-GPT-5-Video-Understanding.ipynb",
        "04-3-Sora-API-Cloud-Video.ipynb",
    ],
    "video_local": [
        "01-1-Video-Operations-Basics.ipynb",
    ],
    "video_qwenvl": [
        "01-3-Qwen-VL-Video-Analysis.ipynb",
    ],
    "video_enhance": [
        "01-4-Video-Enhancement-ESRGAN.ipynb",
    ],
    "video_diffusion_light": [
        "02-2-LTX-Video-Lightweight.ipynb",
        "02-3-Wan-Video-Generation.ipynb",
        "02-4-SVD-Image-to-Video.ipynb",
    ],
    "video_diffusion_heavy": [
        "01-5-AnimateDiff-Introduction.ipynb",
        "02-1-HunyuanVideo-Generation.ipynb",
    ],
    "video_orchestration": [
        "03-1-Multi-Model-Video-Comparison.ipynb",
        "03-2-Video-Workflow-Orchestration.ipynb",
    ],
    "video_comfyui": [
        "03-3-ComfyUI-Video-Workflows.ipynb",
    ],
    "video_apps": [
        "04-1-Educational-Video-Generation.ipynb",
        "04-2-Creative-Video-Workflows.ipynb",
        "04-4-Production-Video-Pipeline.ipynb",
    ],
}

# Groupes de notebooks par serie (meta-groupes)
NOTEBOOK_SERIES = {
    "image": ["cloud", "forge", "qwen", "zimage", "multi", "apps"],
    "audio": ["audio_api", "audio_local", "audio_whisper", "audio_tts_light",
              "audio_tts_heavy", "audio_music", "audio_orchestration", "audio_apps"],
    "video": ["video_api", "video_local", "video_qwenvl", "video_enhance",
              "video_diffusion_light", "video_diffusion_heavy", "video_orchestration",
              "video_comfyui", "video_apps"],
}

# Repertoires de recherche par serie
NOTEBOOK_SEARCH_DIRS = {
    "image": GENAI_DIR / "Image",
    "audio": GENAI_DIR / "Audio",
    "video": GENAI_DIR / "Video",
}


# --- Profils GPU ---

GPU_PROFILES: Dict[str, Dict[str, Any]] = {
    "image_default": {
        "description": "Profil par defaut - services Image",
        "services_up": ["comfyui-qwen", "forge-turbo"],
        "services_down": ["comfyui-video"],
        "gpu_0_usage": "comfyui-qwen (20GB) sur RTX 3090",
        "gpu_1_usage": "forge-turbo (6GB) sur RTX 3080 Ti",
    },
    "audio_api": {
        "description": "Notebooks Audio API-only (pas de GPU local requis)",
        "services_up": [],
        "services_down": [],
        "gpu_0_usage": "inchange",
        "gpu_1_usage": "inchange",
    },
    "audio_local_gpu": {
        "description": "Notebooks Audio avec modeles locaux (RTX 3090 pour kernel)",
        "services_up": [],
        "services_down": ["comfyui-qwen", "whisper-webui", "vllm-zimage", "comfyui-video"],
        "gpu_0_usage": "kernel notebook (jusqu'a 24GB RTX 3090)",
        "gpu_1_usage": "forge-turbo (6GB) sur RTX 3080 Ti",
    },
    "video_comfyui": {
        "description": "Video via ComfyUI avec nodes video (AnimateDiff, HunyuanVideo)",
        "services_up": ["comfyui-video"],
        "services_down": ["comfyui-qwen", "whisper-webui", "vllm-zimage"],
        "gpu_0_usage": "comfyui-video (20GB) sur RTX 3090",
        "gpu_1_usage": "libre",
    },
    "video_local_heavy": {
        "description": "Video avec gros modeles locaux (HunyuanVideo 18GB, Qwen-VL 18GB)",
        "services_up": [],
        "services_down": ["comfyui-qwen", "whisper-webui", "vllm-zimage",
                          "comfyui-video", "forge-turbo"],
        "gpu_0_usage": "kernel notebook (18-24GB RTX 3090)",
        "gpu_1_usage": "libre (RTX 3080 Ti disponible si besoin)",
    },
    "video_local_light": {
        "description": "Video avec modeles legers (LTX 8GB, Wan 10GB, SVD 10GB)",
        "services_up": [],
        "services_down": ["comfyui-qwen", "vllm-zimage", "comfyui-video"],
        "gpu_0_usage": "libre ou kernel notebook (RTX 3090)",
        "gpu_1_usage": "kernel notebook (8-10GB RTX 3080 Ti)",
    },
}

# Mapping groupe de notebooks -> profil GPU recommande
GROUP_GPU_PROFILE = {
    # Image
    "cloud": "image_default",
    "forge": "image_default",
    "qwen": "image_default",
    "zimage": "image_default",
    "multi": "image_default",
    "apps": "image_default",
    # Audio
    "audio_api": "audio_api",
    "audio_local": "audio_api",
    "audio_whisper": "audio_local_gpu",
    "audio_tts_light": "audio_local_gpu",
    "audio_tts_heavy": "audio_local_gpu",
    "audio_music": "audio_local_gpu",
    "audio_orchestration": "audio_local_gpu",
    "audio_apps": "audio_local_gpu",
    # Video
    "video_api": "audio_api",
    "video_local": "audio_api",
    "video_qwenvl": "video_local_heavy",
    "video_enhance": "video_local_light",
    "video_diffusion_light": "video_local_light",
    "video_diffusion_heavy": "video_local_heavy",
    "video_orchestration": "video_local_heavy",
    "video_comfyui": "video_comfyui",
    "video_apps": "video_local_heavy",
}


# --- Batches d'execution Audio/Video ---

EXECUTION_BATCHES = {
    1: {
        "name": "API-only + local sans GPU",
        "profile": "audio_api",
        "groups": ["audio_api", "audio_local", "video_api", "video_local"],
    },
    2: {
        "name": "Audio/Video GPU leger (2-6GB)",
        "profile": "video_local_light",
        "groups": ["audio_tts_light", "audio_music", "video_enhance"],
    },
    3: {
        "name": "Audio GPU moyen (8-10GB)",
        "profile": "audio_local_gpu",
        "groups": ["audio_whisper", "audio_tts_heavy"],
    },
    4: {
        "name": "Audio orchestration/apps (12-14GB)",
        "profile": "audio_local_gpu",
        "groups": ["audio_orchestration", "audio_apps"],
    },
    5: {
        "name": "Video GPU leger/moyen (8-12GB)",
        "profile": "video_local_light",
        "groups": ["video_diffusion_light"],
    },
    6: {
        "name": "Video GPU lourd (18-24GB, RTX 3090 exclusive)",
        "profile": "video_local_heavy",
        "groups": ["video_qwenvl", "video_diffusion_heavy"],
    },
    7: {
        "name": "Video ComfyUI (nodes video)",
        "profile": "video_comfyui",
        "groups": ["video_comfyui"],
    },
    8: {
        "name": "Video orchestration/apps (sequentiel)",
        "profile": "video_local_heavy",
        "groups": ["video_orchestration", "video_apps"],
    },
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
