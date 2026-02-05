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