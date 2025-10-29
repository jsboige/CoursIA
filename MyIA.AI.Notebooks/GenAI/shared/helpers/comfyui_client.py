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
        cfg: float = 7.0,
        save_prefix: str = "qwen_t2i",
    ) -> Dict[str, Any]:
        """
        Génère une image à partir d'un prompt texte.
        Workflow WanBridge validé historiquement (Phase 12C).
        
        Architecture: Custom node ComfyUI-QwenImageWanBridge + modèle Diffusers
        Source: docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md

        Args:
            prompt: Prompt textuel
            width: Largeur de l'image (défaut: 1024, aligné 32px)
            height: Hauteur de l'image (défaut: 1024, aligné 32px)
            num_inference_steps: Nombre de steps de débruitage (deprecated, use steps)
            steps: Nombre de steps de débruitage (défaut: 20)
            seed: Seed aléatoire (None = aléatoire)
            negative_prompt: Prompt négatif (défaut: "blurry, low quality, watermark")
            cfg: Classifier-Free Guidance scale (défaut: 7.0)
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
            inference_steps = 20  # Valeur optimale pour Qwen (doc Phase 12C)
        
        if seed is None:
            seed = random.randint(0, 2**32 - 1)

        # WORKFLOW WANBRIDGE VALIDÉ HISTORIQUEMENT - Méthode WanBridge simple
        # Source: docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md
        # Architecture: Custom node ComfyUI-QwenImageWanBridge + modèle Diffusers
        workflow = {
            "1": {
                "class_type": "QwenVLCLIPLoader",
                "inputs": {
                    "model_path": "Qwen-Image-Edit-2509-FP8"  # Chemin relatif au répertoire checkpoints/
                }
            },
            "2": {
                "class_type": "TextEncodeQwenImageEdit",
                "inputs": {
                    "text": prompt,
                    "clip": ["1", 0]
                }
            },
            "4": {
                "class_type": "QwenVLEmptyLatent",
                "inputs": {
                    "width": width,
                    "height": height,
                    "batch_size": 1
                }
            },
            "5": {
                "class_type": "QwenImageSamplerNode",
                "inputs": {
                    "seed": seed,
                    "steps": inference_steps,
                    "cfg": cfg,
                    "positive": ["2", 0],
                    "latent": ["4", 0]
                }
            },
            "6": {
                "class_type": "VAEDecode",
                "inputs": {
                    "samples": ["5", 0],
                    "vae": ["1", 1]  # CORRECTION: Index 1 = VAE, pas 2
                }
            },
            "7": {
                "class_type": "SaveImage",
                "inputs": {
                    "filename_prefix": save_prefix,
                    "images": ["6", 0]  # CORRECTION: VAEDecode a une seule sortie (index 0)
                }
            }
        }

        # Enqueue et attendre la complétion
        prompt_id = self.queue_prompt(workflow)
        result = self.wait_for_completion(prompt_id)

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
        server_url=config.base_url,
        api_token=config.api_token
    )