"""
ComfyUI API Client - Bridge vers infrastructure locale
Auteur: Phase 13A - Implémentation Bridge
Date: 2025-10-16
Référence: Architecture Phase 12C
"""

import os
import time
import json
import requests
import logging
from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from enum import Enum


# Configuration Logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class ImageGenMode(Enum):
    """Modes de génération disponibles"""
    LOCAL = "local"   # ComfyUI + Qwen local
    CLOUD = "cloud"   # OpenRouter APIs


@dataclass
class ComfyUIConfig:
    """Configuration client ComfyUI"""
    base_url: str = "http://localhost:8188"  # Port production (Phase 12A)
    timeout: int = 120  # Timeout génération (secondes)
    poll_interval: int = 2  # Intervalle polling (secondes)
    
    def test_connection(self) -> bool:
        """Teste connexion au service ComfyUI"""
        try:
            response = requests.get(
                f"{self.base_url}/system_stats",
                timeout=10
            )
            if response.status_code == 200:
                logger.info("✅ ComfyUI accessible")
                return True
            else:
                logger.error(f"❌ ComfyUI status code: {response.status_code}")
                return False
        except requests.exceptions.ConnectionError as e:
            logger.error(f"❌ Connexion échouée: {e}")
            return False
        except Exception as e:
            logger.error(f"❌ Erreur inattendue: {e}")
            return False
    
    def get_system_stats(self) -> Optional[Dict[str, Any]]:
        """Récupère statistiques système ComfyUI"""
        try:
            response = requests.get(f"{self.base_url}/system_stats", timeout=10)
            response.raise_for_status()
            return response.json()
        except Exception as e:
            logger.error(f"❌ Erreur stats système: {e}")
            return None


class ComfyUIClient:
    """Client Python pour ComfyUI API - Production Ready"""
    
    def __init__(self, config: Optional[ComfyUIConfig] = None):
        """
        Initialise client ComfyUI
        
        Args:
            config: Configuration personnalisée (optionnel)
        """
        self.config = config or ComfyUIConfig()
        self.base_url = self.config.base_url
        logger.info(f"🎨 ComfyUI Client initialisé: {self.base_url}")
    
    def queue_prompt(self, workflow: Dict[str, Any]) -> Optional[str]:
        """
        Envoie workflow ComfyUI et retourne prompt_id
        
        Args:
            workflow: Dictionnaire workflow ComfyUI (format JSON)
            
        Returns:
            str: prompt_id si succès, None sinon
        """
        try:
            response = requests.post(
                f"{self.base_url}/prompt",
                json={"prompt": workflow},
                timeout=self.config.timeout
            )
            response.raise_for_status()
            data = response.json()
            prompt_id = data.get("prompt_id")
            
            if prompt_id:
                logger.info(f"✅ Workflow queued: {prompt_id}")
                return prompt_id
            else:
                logger.error("❌ Pas de prompt_id dans réponse")
                return None
                
        except requests.exceptions.Timeout:
            logger.error("❌ Timeout lors du queue_prompt")
            return None
        except Exception as e:
            logger.error(f"❌ Erreur queue_prompt: {e}")
            return None
    
    def wait_for_completion(
        self, 
        prompt_id: str,
        verbose: bool = True
    ) -> bool:
        """
        Attend complétion génération (polling)
        
        Args:
            prompt_id: ID du prompt à surveiller
            verbose: Afficher logs progression
            
        Returns:
            bool: True si succès, False sinon
        """
        elapsed = 0
        
        while elapsed < self.config.timeout:
            try:
                response = requests.get(
                    f"{self.base_url}/history/{prompt_id}",
                    timeout=10
                )
                response.raise_for_status()
                history = response.json()
                
                if prompt_id in history:
                    status = history[prompt_id].get("status", {})
                    
                    # Vérifier complétion
                    if status.get("completed"):
                        logger.info(f"✅ Génération complétée: {prompt_id}")
                        return True
                    
                    # Vérifier erreur
                    if status.get("status_str") == "error":
                        messages = status.get("messages", [])
                        logger.error(f"❌ Erreur génération: {messages}")
                        return False
                
                # Attendre avant prochain poll
                time.sleep(self.config.poll_interval)
                elapsed += self.config.poll_interval
                
                if verbose and elapsed % 10 == 0:
                    logger.info(f"⏳ Attente... {elapsed}s / {self.config.timeout}s")
                
            except Exception as e:
                logger.error(f"❌ Erreur polling: {e}")
                return False
        
        logger.error(f"⏱️ Timeout après {self.config.timeout}s")
        return False
    
    def get_image(self, prompt_id: str, filename: str) -> Optional[bytes]:
        """
        Récupère image générée
        
        Args:
            prompt_id: ID du prompt
            filename: Nom fichier image
            
        Returns:
            bytes: Données image si succès, None sinon
        """
        try:
            response = requests.get(
                f"{self.base_url}/view",
                params={
                    "filename": filename,
                    "subfolder": "",
                    "type": "output"
                },
                timeout=30
            )
            response.raise_for_status()
            return response.content
        except Exception as e:
            logger.error(f"❌ Erreur récupération image: {e}")
            return None
    
    def generate_text2image(
        self,
        prompt: str,
        negative_prompt: str = "blurry, low quality, distorted",
        width: int = 512,
        height: int = 512,
        steps: int = 20,
        cfg: float = 7.0,
        seed: int = -1,
        save_prefix: str = "notebook_gen"
    ) -> Optional[str]:
        """
        Génère image avec workflow Qwen basique
        
        Args:
            prompt: Prompt texte génération
            negative_prompt: Prompt négatif (ce qu'on ne veut pas)
            width: Largeur image (pixels)
            height: Hauteur image (pixels)
            steps: Nombre steps diffusion
            cfg: CFG scale (guidage prompt)
            seed: Seed random (-1 = aléatoire)
            save_prefix: Préfixe fichier sauvegarde
            
        Returns:
            str: prompt_id si succès, None sinon
        """
        # Workflow JSON Qwen basique (référence Phase 12C)
        workflow = {
            "1": {
                "inputs": {
                    "model_path": "Qwen-Image-Edit-2509-FP8"
                },
                "class_type": "QwenVLCLIPLoader"
            },
            "2": {
                "inputs": {
                    "text": prompt,
                    "clip": ["1", 0]
                },
                "class_type": "TextEncodeQwenImageEdit"
            },
            "3": {
                "inputs": {
                    "text": negative_prompt,
                    "clip": ["1", 0]
                },
                "class_type": "TextEncodeQwenImageEdit"
            },
            "4": {
                "inputs": {
                    "width": width,
                    "height": height,
                    "batch_size": 1
                },
                "class_type": "EmptyLatentImage"
            },
            "5": {
                "inputs": {
                    "seed": seed if seed >= 0 else int(time.time() * 1000),
                    "steps": steps,
                    "cfg": cfg,
                    "sampler_name": "euler_ancestral",
                    "scheduler": "normal",
                    "denoise": 1.0,
                    "transformer": ["1", 1],
                    "positive": ["2", 0],
                    "negative": ["3", 0],
                    "latent_image": ["4", 0]
                },
                "class_type": "QwenImageSamplerNode"
            },
            "6": {
                "inputs": {
                    "samples": ["5", 0],
                    "vae": ["1", 2]
                },
                "class_type": "VAEDecodeQwen"
            },
            "7": {
                "inputs": {
                    "filename_prefix": save_prefix,
                    "images": ["6", 0]
                },
                "class_type": "SaveImage"
            }
        }
        
        logger.info(f"🎨 Génération: '{prompt[:50]}...'")
        logger.info(f"   Résolution: {width}x{height}, Steps: {steps}, CFG: {cfg}")
        
        prompt_id = self.queue_prompt(workflow)
        
        if prompt_id and self.wait_for_completion(prompt_id):
            logger.info(f"✅ Génération réussie: {prompt_id}")
            return prompt_id
        else:
            logger.error("❌ Génération échouée")
            return None


# Fonctions Helper pour notebooks

def create_client(
    base_url: str = "http://localhost:8188"
) -> ComfyUIClient:
    """
    Crée et teste client ComfyUI
    
    Args:
        base_url: URL base ComfyUI
        
    Returns:
        ComfyUIClient: Client initialisé et validé
        
    Raises:
        ConnectionError: Si connexion échoue
    """
    config = ComfyUIConfig(base_url=base_url)
    
    if not config.test_connection():
        raise ConnectionError(
            f"❌ Impossible de se connecter à ComfyUI sur {base_url}. "
            f"Vérifier que le service est démarré (Phase 12A)."
        )
    
    # Afficher stats système
    stats = config.get_system_stats()
    if stats:
        system = stats.get("system", {})
        logger.info(f"🖥️  GPU: {system.get('gpu_name', 'N/A')}")
        logger.info(f"💾 VRAM: {system.get('vram_total', 'N/A')} MB")
    
    return ComfyUIClient(config)


def quick_generate(
    prompt: str,
    client: Optional[ComfyUIClient] = None,
    **kwargs
) -> Optional[str]:
    """
    Génération rapide text-to-image (wrapper simplifié)
    
    Args:
        prompt: Prompt texte
        client: Client ComfyUI (créé automatiquement si None)
        **kwargs: Paramètres optionnels (width, height, steps, etc.)
        
    Returns:
        str: prompt_id si succès, None sinon
    """
    if client is None:
        client = create_client()
    
    return client.generate_text2image(prompt, **kwargs)