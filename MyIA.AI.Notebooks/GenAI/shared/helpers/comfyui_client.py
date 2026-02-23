"""
Client pour interagir avec l'API ComfyUI avec authentification Bearer Token.
Workflow corrigé basé sur qwen_text_to_image_2509.json de référence.
"""

import json
import os
import random
import time
from pathlib import Path
from typing import Any, Dict, Optional
from urllib import request, error


class ComfyUIConfig:
    """Configuration pour le client ComfyUI."""
    
    def __init__(
        self,
        base_url: str = "http://localhost:8188",
        timeout: int = 120,
        poll_interval: int = 2,
        api_token: Optional[str] = None
    ):
        """
        Initialise la configuration.
        
        Args:
            base_url: URL du serveur ComfyUI
            timeout: Timeout en secondes pour les requêtes
            poll_interval: Intervalle de polling en secondes
            api_token: Token Bearer pour l'authentification
        """
        self.base_url = base_url
        self.timeout = timeout
        self.poll_interval = poll_interval
        self.api_token = api_token


class ComfyUIClient:
    """Client pour interagir avec ComfyUI via son API REST."""

    def __init__(self, base_url: str, api_token: Optional[str] = None):
        """
        Initialise le client ComfyUI.

        Args:
            base_url: URL du serveur ComfyUI (ex: http://localhost:8188)
            api_token: Token Bearer pour l'authentification (optionnel)
        """
        self.server_url = base_url.rstrip("/")
        self.api_token = api_token
        self.client_id = str(random.randint(1, 1000000))

    def _make_request(
        self, endpoint: str, method: str = "GET", data: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        Effectue une requête HTTP vers l'API ComfyUI.

        Args:
            endpoint: Endpoint de l'API (ex: /prompt)
            method: Méthode HTTP (GET, POST, etc.)
            data: Données à envoyer (pour POST)

        Returns:
            Réponse JSON de l'API

        Raises:
            Exception: Si la requête échoue
        """
        # S'assurer que server_url ne se termine pas par / et endpoint commence par /
        server_url = self.server_url.rstrip("/")
        endpoint = endpoint.lstrip("/")
        url = f"{server_url}/{endpoint}"
        headers = {"Content-Type": "application/json"}

        # Ajouter l'authentification Bearer si un token est fourni
        if self.api_token:
            headers["Authorization"] = f"Bearer {self.api_token}"

        # Préparer les données pour les requêtes non-GET
        request_data = None
        if method.upper() != "GET" and data is not None:
            request_data = json.dumps(data).encode()
        
        # Pour les requêtes GET, créer l'objet Request différemment
        if method.upper() == "GET":
            req = request.Request(url, headers=headers, method="GET")
        else:
            req = request.Request(
                url,
                data=request_data,
                headers=headers,
                method=method.upper(),  # Convertir en majuscules
            )

        try:
            with request.urlopen(req) as response:
                return json.loads(response.read().decode())
        except error.HTTPError as e:
            error_body = e.read().decode() if e.fp else "No error body"
            raise Exception(
                f"HTTP {e.code} Error calling {url}: {e.reason}\nBody: {error_body}"
            )
        except error.URLError as e:
            raise Exception(f"URL Error calling {url}: {e.reason}")

    def queue_prompt(self, workflow: Dict[str, Any]) -> str:
        """
        Envoie un workflow à ComfyUI pour exécution.

        Args:
            workflow: Workflow ComfyUI au format JSON

        Returns:
            ID du prompt en queue

        Raises:
            Exception: Si l'enqueue échoue
        """
        payload = {"prompt": workflow, "client_id": self.client_id}
        response = self._make_request("/prompt", method="POST", data=payload)

        if "prompt_id" not in response:
            raise Exception(f"Prompt queue failed: {response}")

        return response["prompt_id"]

    def get_system_stats(self) -> Dict[str, Any]:
        """
        Récupère les statistiques système de ComfyUI.

        Returns:
            Statistiques système
        """
        return self._make_request("/system_stats")

    def get_history(self, prompt_id: str) -> Dict[str, Any]:
        """
        Récupère l'historique d'exécution d'un prompt.

        Args:
            prompt_id: ID du prompt

        Returns:
            Historique d'exécution
        """
        return self._make_request(f"/history/{prompt_id}")

    def wait_for_completion(
        self, prompt_id: str, timeout: int = 300, poll_interval: int = 2
    ) -> Dict[str, Any]:
        """
        Attend la complétion d'un prompt.

        Args:
            prompt_id: ID du prompt
            timeout: Timeout en secondes
            poll_interval: Intervalle de polling en secondes

        Returns:
            Résultat de l'exécution

        Raises:
            TimeoutError: Si le timeout est dépassé
            Exception: Si l'exécution échoue
        """
        start_time = time.time()

        while True:
            if time.time() - start_time > timeout:
                raise TimeoutError(
                    f"Workflow execution timed out after {timeout}s (prompt_id: {prompt_id})"
                )

            history = self.get_history(prompt_id)

            if prompt_id in history:
                result = history[prompt_id]

                # Vérifier si l'exécution est terminée
                if "outputs" in result:
                    return result

                # Vérifier les erreurs
                if "errors" in result and result["errors"]:
                    raise Exception(
                        f"Workflow execution failed: {json.dumps(result['errors'], indent=2)}"
                    )

            time.sleep(poll_interval)

    def generate_text2image(
        self,
        prompt: str,
        width: int = 1024,
        height: int = 1024,
        num_inference_steps: Optional[int] = None,
        steps: Optional[int] = None,
        seed: Optional[int] = None,
        negative_prompt: str = "blurry, low quality, watermark",
        cfg: float = 1.0,
        save_prefix: str = "qwen_t2i",
    ) -> Dict[str, Any]:
        """
        Génère une image à partir d'un prompt texte.
        Workflow 100% NATIF ComfyUI - Phase 29 validé.

        Architecture: Nodes natifs ComfyUI + modèles FP8 Comfy-Org
        Modèles requis:
          - diffusion_models/qwen_image_edit_2509_fp8_e4m3fn.safetensors (20GB)
          - text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors (8.8GB)
          - vae/qwen_image_vae.safetensors (243MB)

        Args:
            prompt: Prompt textuel
            width: Largeur de l'image (défaut: 1024, aligné 32px)
            height: Hauteur de l'image (défaut: 1024, aligné 32px)
            num_inference_steps: Nombre de steps de débruitage (deprecated, use steps)
            steps: Nombre de steps de débruitage (défaut: 20)
            seed: Seed aléatoire (None = aléatoire)
            negative_prompt: Prompt négatif (non utilisé dans architecture native Qwen)
            cfg: Classifier-Free Guidance scale (défaut: 1.0 pour Qwen avec CFGNorm)
            save_prefix: Préfixe pour le fichier de sortie

        Returns:
            Résultat de la génération (historique ComfyUI)
        """
        # Gérer l'alias steps/num_inference_steps
        if steps is not None:
            inference_steps = steps
        elif num_inference_steps is not None:
            inference_steps = num_inference_steps
        else:
            inference_steps = 20  # Valeur optimale pour Qwen

        if seed is None:
            seed = random.randint(0, 2**32 - 1)

        # WORKFLOW 100% NATIF ComfyUI - Validé Phase 29
        # Source: docs/suivis/genai-image/phase-29-corrections-qwen/SYNTHESE-COMPLETE-PHASE-29.md
        # Architecture: Nodes natifs + modèles FP8 officiels Comfy-Org
        workflow = {
            # Chargement des modèles
            "1": {
                "class_type": "VAELoader",
                "inputs": {
                    "vae_name": "qwen_image_vae.safetensors"
                }
            },
            "2": {
                "class_type": "CLIPLoader",
                "inputs": {
                    "clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
                    "type": "sd3"
                }
            },
            "3": {
                "class_type": "UNETLoader",
                "inputs": {
                    "unet_name": "qwen_image_edit_2509_fp8_e4m3fn.safetensors",
                    "weight_dtype": "fp8_e4m3fn"
                }
            },
            # Configuration du modèle pour Qwen (AuraFlow sampling)
            "4": {
                "class_type": "ModelSamplingAuraFlow",
                "inputs": {
                    "model": ["3", 0],
                    "shift": 3.0
                }
            },
            # Normalisation CFG
            "5": {
                "class_type": "CFGNorm",
                "inputs": {
                    "model": ["4", 0],
                    "strength": 1.0
                }
            },
            # Encodage du prompt positif avec Qwen
            "6": {
                "class_type": "TextEncodeQwenImageEdit",
                "inputs": {
                    "clip": ["2", 0],
                    "prompt": prompt,
                    "vae": ["1", 0]
                }
            },
            # Conditioning négatif (vide pour Qwen)
            "7": {
                "class_type": "ConditioningZeroOut",
                "inputs": {
                    "conditioning": ["6", 0]
                }
            },
            # Création du latent vide (16 canaux pour Qwen)
            "8": {
                "class_type": "EmptySD3LatentImage",
                "inputs": {
                    "width": width,
                    "height": height,
                    "batch_size": 1
                }
            },
            # Sampling
            "9": {
                "class_type": "KSampler",
                "inputs": {
                    "model": ["5", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["8", 0],
                    "seed": seed,
                    "steps": inference_steps,
                    "cfg": cfg,
                    "sampler_name": "euler",
                    "scheduler": "beta",
                    "denoise": 1.0
                }
            },
            # Décodage VAE
            "10": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": ["9", 0],
                    "vae": ["1", 0]
                }
            },
            # Sauvegarde
            "11": {
                "class_type": "SaveImage",
                "inputs": {
                    "images": ["10", 0],
                    "filename_prefix": save_prefix
                }
            }
        }

        # Enqueue et attendre la complétion
        prompt_id = self.queue_prompt(workflow)
        result = self.wait_for_completion(prompt_id)

        return result

    def generate_text2image_lightning(
        self,
        prompt: str,
        width: int = 1024,
        height: int = 1024,
        steps: int = 4,
        seed: Optional[int] = None,
        cfg: float = 1.0,
        save_prefix: str = "qwen_lightning",
        timeout: int = 60,
    ) -> Dict[str, Any]:
        """
        Generation rapide avec modele Nunchaku Lightning V2.0 INT4 (4 steps).

        ~5x plus rapide que generate_text2image() grace a:
        - Quantification INT4 (12GB vs 20GB)
        - Seulement 4 steps de diffusion au lieu de 20
        - Modele distille (Lightning)

        V2.0 vs V1.0 : Moins de saturation, textures de peau plus naturelles.

        Modeles requis:
          - diffusion_models/svdq-int4_r128-qwen-image-edit-2509-lightningv2.0-4steps.safetensors
          - text_encoders/qwen_2.5_vl_7b_fp8_scaled.safetensors
          - vae/qwen_image_vae.safetensors

        Args:
            prompt: Prompt textuel
            width: Largeur de l'image (defaut: 1024)
            height: Hauteur de l'image (defaut: 1024)
            steps: Nombre de steps (defaut: 4 pour Lightning)
            seed: Seed aleatoire (None = aleatoire)
            cfg: CFG scale (defaut: 1.0)
            save_prefix: Prefixe pour le fichier de sortie
            timeout: Timeout en secondes (defaut: 60s car beaucoup plus rapide)

        Returns:
            Resultat de la generation (historique ComfyUI)
        """
        if seed is None:
            seed = random.randint(0, 2**32 - 1)

        # WORKFLOW NUNCHAKU LIGHTNING INT4 - 4 steps
        # Utilise NunchakuQwenImageDiTLoader au lieu de UNETLoader
        workflow = {
            # VAE
            "1": {
                "class_type": "VAELoader",
                "inputs": {
                    "vae_name": "qwen_image_vae.safetensors"
                }
            },
            # CLIP (text encoder)
            "2": {
                "class_type": "CLIPLoader",
                "inputs": {
                    "clip_name": "qwen_2.5_vl_7b_fp8_scaled.safetensors",
                    "type": "qwen_image",
                    "device": "default"
                }
            },
            # Nunchaku Lightning V2.0 INT4 Model Loader
            "3": {
                "class_type": "NunchakuQwenImageDiTLoader",
                "inputs": {
                    "model_path": "svdq-int4_r128-qwen-image-edit-2509-lightningv2.0-4steps.safetensors",
                    "cache_threshold": "enable",
                    "attention_mode": 20,
                    "moe_mode": "disable"
                }
            },
            # ModelSamplingAuraFlow
            "4": {
                "class_type": "ModelSamplingAuraFlow",
                "inputs": {
                    "model": ["3", 0],
                    "shift": 3.0
                }
            },
            # CFGNorm
            "5": {
                "class_type": "CFGNorm",
                "inputs": {
                    "model": ["4", 0],
                    "strength": 1.0
                }
            },
            # Encodage du prompt (positif)
            "6": {
                "class_type": "TextEncodeQwenImageEdit",
                "inputs": {
                    "clip": ["2", 0],
                    "prompt": prompt,
                    "vae": ["1", 0]
                }
            },
            # Conditioning negatif (vide)
            "7": {
                "class_type": "ConditioningZeroOut",
                "inputs": {
                    "conditioning": ["6", 0]
                }
            },
            # Latent vide
            "8": {
                "class_type": "EmptySD3LatentImage",
                "inputs": {
                    "width": width,
                    "height": height,
                    "batch_size": 1
                }
            },
            # KSampler - 4 steps avec scheduler simple
            "9": {
                "class_type": "KSampler",
                "inputs": {
                    "model": ["5", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["8", 0],
                    "seed": seed,
                    "steps": steps,
                    "cfg": cfg,
                    "sampler_name": "euler",
                    "scheduler": "simple",
                    "denoise": 1.0
                }
            },
            # VAE Decode
            "10": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": ["9", 0],
                    "vae": ["1", 0]
                }
            },
            # Save
            "11": {
                "class_type": "SaveImage",
                "inputs": {
                    "images": ["10", 0],
                    "filename_prefix": save_prefix
                }
            }
        }

        # Enqueue et attendre la completion
        prompt_id = self.queue_prompt(workflow)
        result = self.wait_for_completion(prompt_id, timeout=timeout)

        return result

    def generate_text2video_wan(
        self,
        prompt: str,
        width: int = 832,
        height: int = 480,
        num_frames: int = 16,
        steps: int = 20,
        seed: Optional[int] = None,
        negative_prompt: str = "色调艳丽，过曝，静态，细节模糊不清，字幕，风格，作品，画作，画面，静止，整体发灰，最差质量，低质量，JPEG压缩残留，丑陋的，残缺的，多余的手指，画得不好的手部，画得不好的脸部，畸形的，毁容的，形态畸形的肢体，手指融合，静止不动的画面，杂乱的背景，三条腿，背景人很多，倒着走",
        cfg: float = 6.0,
        save_prefix: str = "wan_t2v",
        timeout: int = 300,
    ) -> Dict[str, Any]:
        """
        Genere une video a partir d'un prompt texte avec Wan 2.1 1.3B.

        Modele Wan 2.1 T2V 1.3B - ~8GB VRAM requis
        Architecture: WanTextToVideo avec ModelSamplingSD3

        Modeles requis:
          - diffusion_models/wan2.1_t2v_1.3B_fp16.safetensors (~2.5GB)
          - text_encoders/umt5_xxl_fp8_e4m3fn_scaled.safetensors (~4GB)
          - vae/wan_2.1_vae.safetensors (~360MB)

        Args:
            prompt: Prompt textuel (FR, EN ou CN supporte)
            width: Largeur video (defaut: 832, aligne 32px)
            height: Hauteur video (defaut: 480, aligne 32px)
            num_frames: Nombre de frames (defaut: 16)
            steps: Nombre de steps de diffusion (defaut: 20)
            seed: Seed aleatoire (None = aleatoire)
            negative_prompt: Prompt negatif (defaut: liste Wan officielle)
            cfg: CFG scale (defaut: 6.0 pour Wan)
            save_prefix: Prefixe pour le fichier de sortie
            timeout: Timeout en secondes (defaut: 300s)

        Returns:
            Resultat de la generation (historique ComfyUI)
        """
        if seed is None:
            seed = random.randint(0, 2**32 - 1)

        # WORKFLOW WAN 2.1 T2V 1.3B - Based on text_to_video_wan.json
        workflow = {
            # Chargement du modele UNE
            "37": {
                "class_type": "UNETLoader",
                "inputs": {
                    "unet_name": "wan2.1_t2v_1.3B_fp16.safetensors",
                    "weight_dtype": "default"
                }
            },
            # Chargement CLIP (text encoder)
            "38": {
                "class_type": "CLIPLoader",
                "inputs": {
                    "clip_name": "umt5_xxl_fp8_e4m3fn_scaled.safetensors",
                    "type": "wan",
                    "device": "default"
                }
            },
            # Chargement VAE
            "39": {
                "class_type": "VAELoader",
                "inputs": {
                    "vae_name": "wan_2.1_vae.safetensors"
                }
            },
            # Latent video vide
            "40": {
                "class_type": "EmptyHunyuanLatentVideo",
                "inputs": {
                    "width": width,
                    "height": height,
                    "frame_limit": num_frames,
                    "batch_size": 1
                }
            },
            # Encodage prompt positif
            "6": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": ["38", 0],
                    "text": prompt
                }
            },
            # Encodage prompt negatif
            "7": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": ["38", 0],
                    "text": negative_prompt
                }
            },
            # ModelSamplingSD3 (shift=8 pour Wan)
            "48": {
                "class_type": "ModelSamplingSD3",
                "inputs": {
                    "model": ["37", 0],
                    "shift": 8
                }
            },
            # KSampler
            "3": {
                "class_type": "KSampler",
                "inputs": {
                    "model": ["48", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["40", 0],
                    "seed": seed,
                    "steps": steps,
                    "cfg": cfg,
                    "sampler_name": "uni_pc",
                    "scheduler": "simple",
                    "denoise": 1.0
                }
            },
            # VAE Decode
            "8": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": ["3", 0],
                    "vae": ["39", 0]
                }
            },
            # CreateVideo
            "49": {
                "class_type": "CreateVideo",
                "inputs": {
                    "images": ["8", 0],
                    "fps": 16,
                    "loop_count": 1,
                    "filename_prefix": save_prefix,
                    "format": "video/h264-mp4",
                    "save_output": True,
                    "videopreview": {"hidden": False}
                }
            },
            # SaveVideo
            "50": {
                "class_type": "SaveVideo",
                "inputs": {
                    "video": ["49", 0],
                    "fps": 16,
                    "filename_prefix": save_prefix,
                    "save_output": True
                }
            }
        }

        # Enqueue et attendre la completion
        prompt_id = self.queue_prompt(workflow)
        result = self.wait_for_completion(prompt_id, timeout=timeout)

        return result

    def generate_text2video_hunyuan(
        self,
        prompt: str,
        width: int = 1280,
        height: int = 720,
        num_frames: int = 33,
        steps: int = 30,
        seed: Optional[int] = None,
        negative_prompt: str = "bad quality, low quality, blurry, distortion, artifacts",
        cfg: float = 7.0,
        save_prefix: str = "hunyuan_t2v",
        timeout: int = 300,
    ) -> Dict[str, Any]:
        """
        Genere une video a partir d'un prompt texte avec HunyuanVideo 1.5.

        Modele HunyuanVideo T2V 720p - ~12 GB VRAM requis
        Architecture: DualCLIP + UNET avec sampling standard

        Modeles requis:
          - diffusion_models/hunyuan_video_t2v_720p_bf16.safetensors (~6GB)
          - text_encoders/clip_l.safetensors (~475MB)
          - text_encoders/llava_llama3_fp8_scaled.safetensors (~4GB)
          - vae/hunyuan_vae.safetensors (~360MB)

        Args:
            prompt: Prompt textuel
            width: Largeur video (defaut: 1280, 720p)
            height: Hauteur video (defaut: 720)
            num_frames: Nombre de frames (defaut: 33 pour HunyuanVideo)
            steps: Nombre de steps (defaut: 30)
            seed: Seed aleatoire (None = aleatoire)
            negative_prompt: Prompt negatif
            cfg: CFG scale (defaut: 7.0)
            save_prefix: Prefixe de sauvegarde
            timeout: Timeout en secondes

        Returns:
            Resultat de la generation (historique ComfyUI)
        """
        if seed is None:
            seed = random.randint(0, 2**32 - 1)

        # WORKFLOW HUNYUANVIDEO T2V - Simplifie (basé sur structure standard)
        workflow = {
            # DualCLIP Loader (clip_l + llava_llama3)
            "11": {
                "class_type": "DualCLIPLoader",
                "inputs": {
                    "clip_name1": "clip_l.safetensors",
                    "clip_name2": "llava_llama3_fp8_scaled.safetensors",
                    "type": "hunyuan_video",
                    "device": "default"
                }
            },
            # UNET Loader
            "12": {
                "class_type": "UNETLoader",
                "inputs": {
                    "unet_name": "hunyuan_video_t2v_720p_bf16.safetensors",
                    "weight_dtype": "default"
                }
            },
            # Empty Hunyuan Latent Video
            "40": {
                "class_type": "EmptyHunyuanLatentVideo",
                "inputs": {
                    "width": width,
                    "height": height,
                    "frame_limit": num_frames,
                    "batch_size": 1
                }
            },
            # Positive Prompt
            "6": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": ["11", 0],
                    "text": prompt
                }
            },
            # Negative Prompt
            "7": {
                "class_type": "CLIPTextEncode",
                "inputs": {
                    "clip": ["11", 0],
                    "text": negative_prompt
                }
            },
            # KSampler (standard pour HunyuanVideo)
            "3": {
                "class_type": "KSampler",
                "inputs": {
                    "model": ["12", 0],
                    "positive": ["6", 0],
                    "negative": ["7", 0],
                    "latent_image": ["40", 0],
                    "seed": seed,
                    "steps": steps,
                    "cfg": cfg,
                    "sampler_name": "euler",
                    "scheduler": "simple",
                    "denoise": 1.0
                }
            },
            # VAE Decode (utiliser VAE du checkpoint)
            "8": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": ["3", 0],
                    "vae": ["12", 2]  # VAE depuis CheckpointLoader
                }
            },
            # CreateVideo
            "49": {
                "class_type": "CreateVideo",
                "inputs": {
                    "images": ["8", 0],
                    "fps": 24,
                    "loop_count": 1,
                    "filename_prefix": save_prefix,
                    "format": "video/h264-mp4",
                    "save_output": True
                }
            },
            # SaveVideo
            "50": {
                "class_type": "SaveVideo",
                "inputs": {
                    "video": ["49", 0],
                    "fps": 24,
                    "filename_prefix": save_prefix,
                    "save_output": True
                }
            }
        }

        prompt_id = self.queue_prompt(workflow)
        result = self.wait_for_completion(prompt_id, timeout=timeout)

        return result


def load_from_env(env_path: Optional[Path] = None) -> ComfyUIClient:
    """
    Charge un client ComfyUI depuis un fichier .env.

    Args:
        env_path: Chemin vers le fichier .env (None = cherche dans répertoire courant)

    Returns:
        Client ComfyUI configuré

    Raises:
        ValueError: Si les variables d'environnement requises sont manquantes
    """
    if env_path is None:
        # Chercher .env dans le répertoire courant et parents
        current = Path.cwd()
        for parent in [current] + list(current.parents):
            candidate = parent / ".env"
            if candidate.exists():
                env_path = candidate
                break

    if env_path is None or not env_path.exists():
        raise ValueError(
            f"Fichier .env non trouvé. Cherché dans: {Path.cwd()} et parents"
        )

    # Charger les variables d'environnement
    env_vars = {}
    with open(env_path) as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                key, _, value = line.partition("=")
                env_vars[key.strip()] = value.strip().strip('"').strip("'")

    # Récupérer l'URL et le token
    server_url = env_vars.get("COMFYUI_API_URL")
    api_token = env_vars.get("COMFYUI_API_TOKEN")

    # Tenter de récupérer le token depuis le fichier .secrets/qwen-api-user.token
    # On cherche le répertoire .secrets à la racine du projet (en remontant depuis env_path)
    if env_path:
        project_root = env_path.parent
        # Remonter jusqu'à trouver .secrets ou atteindre la racine
        for _ in range(5): # Max 5 niveaux
            secrets_file = project_root / ".secrets" / "qwen-api-user.token"
            if secrets_file.exists():
                try:
                    file_token = secrets_file.read_text(encoding='utf-8').strip()
                    if file_token:
                        print(f"✅ Token chargé depuis {secrets_file}")
                        api_token = file_token
                        break
                except Exception as e:
                    print(f"⚠️ Erreur lecture token fichier: {e}")
            
            if project_root.parent == project_root: # Racine atteinte
                break
            project_root = project_root.parent

    if not server_url:
        raise ValueError("COMFYUI_API_URL manquant dans .env")

    if not api_token:
        print(
            "⚠️  COMFYUI_API_TOKEN manquant dans .env - authentification désactivée"
        )

    return ComfyUIClient(server_url, api_token)

def create_client(config: Optional[ComfyUIConfig] = None) -> ComfyUIClient:
    """
    Crée un client ComfyUI avec configuration optionnelle.
    
    Args:
        config: Configuration ComfyUI (None = charge depuis .env)
    
    Returns:
        Client ComfyUI configuré
    """
    if config is None:
        # Charger depuis .env
        return load_from_env()
    
    return ComfyUIClient(
        base_url=config.base_url,
        api_token=config.api_token
    )