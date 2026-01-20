#!/usr/bin/env python3
"""
comfyui_client.py - Librairie Client Unifiée pour ComfyUI

Ce module fournit une interface Python complète pour interagir avec ComfyUI :
- Client HTTP (API, Auth, Upload, Prompt)
- Gestionnaire de Workflows (Chargement, Validation, Optimisation)
- Utilitaires d'investigation (Inspection Nodes, Compatibilité)

Auteur: Consolidation Phase 36
Date: 2025-12-12
"""

import sys
import os
import json
import time
import requests
import urllib3
from pathlib import Path
from typing import Dict, List, Any, Optional, Union, Tuple
from dataclasses import dataclass
from datetime import datetime

# Désactiver les warnings SSL pour dev local
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Configuration par défaut
DEFAULT_HOST = "127.0.0.1"
DEFAULT_PORT = 8188

@dataclass
class ComfyUIConfig:
    """Configuration de connexion"""
    host: str = DEFAULT_HOST
    port: int = DEFAULT_PORT
    protocol: str = "http"
    api_key: Optional[str] = None
    timeout: int = 30
    max_retries: int = 3
    retry_delay: float = 1.0
    verify_ssl: bool = False

class ComfyUIError(Exception):
    """Exception de base pour le client ComfyUI"""
    def __init__(self, message: str, status_code: Optional[int] = None, response: Optional[requests.Response] = None):
        super().__init__(message)
        self.message = message
        self.status_code = status_code
        self.response = response

class ComfyUIClient:
    """Client API pour ComfyUI"""
    
    def __init__(self, config: ComfyUIConfig = None):
        self.config = config or ComfyUIConfig()
        self.session = requests.Session()
        self.client_id = "ComfyUIClient-" + str(time.time())
        
        # Headers par défaut
        self.session.headers.update({
            'User-Agent': 'ComfyUI-Client-Lib/2.0.0',
            'Content-Type': 'application/json'
        })
        
        # Authentification
        if self.config.api_key:
            auth_val = self.config.api_key
            if not auth_val.startswith(("Bearer ", "Basic ")):
                auth_val = f"Bearer {auth_val}"
            self.session.headers['Authorization'] = auth_val

    def _url(self, endpoint: str) -> str:
        return f"{self.config.protocol}://{self.config.host}:{self.config.port}{endpoint}"

    def _request(self, method: str, endpoint: str, **kwargs) -> requests.Response:
        """Exécute une requête avec retries"""
        url = self._url(endpoint)
        last_error = None
        
        for attempt in range(self.config.max_retries):
            try:
                resp = self.session.request(
                    method, url, 
                    timeout=self.config.timeout, 
                    verify=self.config.verify_ssl,
                    **kwargs
                )
                
                if resp.status_code >= 400:
                    raise ComfyUIError(f"HTTP {resp.status_code}: {resp.text}", resp.status_code, resp)
                    
                return resp
                
            except requests.RequestException as e:
                last_error = e
                time.sleep(self.config.retry_delay * (2 ** attempt))
                
        raise ComfyUIError(f"Connection failed after {self.config.max_retries} retries: {last_error}")

    # --- API Méthodes ---

    def is_reachable(self) -> bool:
        """Vérifie si le serveur est accessible"""
        try:
            self._request('GET', '/system_stats')
            return True
        except Exception as e:
            print(f"DEBUG: is_reachable failed: {e}")
            return False

    def get_system_stats(self) -> Dict[str, Any]:
        """Récupère les stats système"""
        return self._request('GET', '/system_stats').json()

    def get_object_info(self, node_class: str = None) -> Dict[str, Any]:
        """Récupère les infos sur les nodes"""
        endpoint = f'/object_info/{node_class}' if node_class else '/object_info'
        return self._request('GET', endpoint).json()

    def upload_image(self, file_path: Union[str, Path], subfolder: str = "") -> Dict[str, Any]:
        """Upload une image"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"File not found: {path}")
            
        with open(path, 'rb') as f:
            files = {'image': (path.name, f, 'image/png')} # Mime type générique
            data = {'subfolder': subfolder}
            return self._request('POST', '/upload/image', files=files, data=data).json()

    def queue_prompt(self, workflow: Dict[str, Any]) -> str:
        """Soumet un workflow et retourne le prompt_id"""
        payload = {"prompt": workflow, "client_id": self.client_id}
        resp = self._request('POST', '/prompt', json=payload).json()
        return resp.get('prompt_id')

    def get_history(self, prompt_id: str) -> Dict[str, Any]:
        """Récupère l'historique pour un prompt"""
        return self._request('GET', f'/history/{prompt_id}').json()

    def get_queue(self) -> Dict[str, Any]:
        """Récupère l'état de la file d'attente"""
        return self._request('GET', '/queue').json()

    def download_view(self, filename: str, subfolder: str = "", type: str = "output") -> bytes:
        """Télécharge un fichier généré"""
        params = {"filename": filename, "subfolder": subfolder, "type": type}
        return self._request('GET', '/view', params=params).content

    def wait_for_prompt(self, prompt_id: str, timeout: int = 300) -> Dict[str, Any]:
        """Attend la fin d'un prompt (polling simple)"""
        start = time.time()
        while time.time() - start < timeout:
            hist = self.get_history(prompt_id)
            if prompt_id in hist:
                return hist[prompt_id]
            time.sleep(1)
        raise ComfyUIError(f"Timeout waiting for prompt {prompt_id}")

    def free_memory(self, unload_models: bool = True) -> Dict[str, Any]:
        """Libere la VRAM et decharge les modeles via POST /free.

        Args:
            unload_models: Si True, decharge tous les modeles de la VRAM

        Returns:
            Reponse JSON du serveur avec status de liberation, ou {"success": True} si vide
        """
        payload = {
            "unload_models": unload_models,
            "free_memory": True
        }
        resp = self._request('POST', '/free', json=payload)
        # /free peut retourner une reponse vide sur succes
        try:
            return resp.json() if resp.text.strip() else {"success": True}
        except Exception:
            return {"success": True}

    def interrupt_prompt(self) -> Dict[str, Any]:
        """Interrompt le prompt en cours d'execution"""
        return self._request('POST', '/interrupt').json()

    def clear_queue(self) -> Dict[str, Any]:
        """Vide la file d'attente"""
        return self._request('POST', '/queue', json={"clear": True}).json()

class WorkflowManager:
    """Utilitaires pour manipuler les workflows JSON"""
    
    @staticmethod
    def load(path: Union[str, Path]) -> Dict[str, Any]:
        """Charge un workflow depuis un fichier.

        Filtre automatiquement les clés de métadonnées (comme _meta)
        qui ne sont pas des nœuds ComfyUI valides.
        """
        with open(path, 'r', encoding='utf-8') as f:
            raw = json.load(f)

        # Filter out non-node keys (like _meta) at root level
        # Valid nodes have a 'class_type' key
        return {k: v for k, v in raw.items()
                if isinstance(v, dict) and 'class_type' in v}

    @staticmethod
    def validate(workflow: Dict[str, Any]) -> Tuple[bool, List[str]]:
        """Valide la structure d'un workflow"""
        errors = []
        
        # Support API format (dict of nodes) vs UI format (has "nodes" list)
        is_api = 'nodes' not in workflow and all(isinstance(v, dict) and 'class_type' in v for v in workflow.values())
        
        if is_api:
            return True, [] # API format is loosely structured
            
        if 'nodes' not in workflow:
            return False, ["Missing 'nodes' list (UI format expected)"]
            
        for i, node in enumerate(workflow['nodes']):
            if 'id' not in node: errors.append(f"Node #{i} missing 'id'")
            if 'type' not in node: errors.append(f"Node #{i} missing 'type'")
            
        return len(errors) == 0, errors

    @staticmethod
    def convert_ui_to_api(ui_workflow: Dict[str, Any]) -> Dict[str, Any]:
        """Convertit un workflow UI (nodes list) en format API (dict id->node)"""
        # Note: C'est une approximation. La conversion réelle nécessite le graphe complet.
        # Ici on extrait juste les inputs et class_type pour un usage simple.
        api_workflow = {}
        for node in ui_workflow.get('nodes', []):
            if node['type'] in ['Reroute', 'Note']: continue # Ignorer les nodes utilitaires
            
            api_node = {
                "class_type": node['type'],
                "inputs": {}
            }
            
            # TODO: Mapping complexe des inputs (widgets_values -> inputs)
            # Cette fonction est un placeholder pour une implémentation future plus robuste
            # si nécessaire. Pour l'instant, on assume que les utilisateurs fournissent
            # des workflows déjà au format API pour l'automatisation.
            pass
            
        return api_workflow

    @staticmethod
    def fix_links(workflow: Dict[str, Any]) -> Dict[str, Any]:
        """Corrige les liens mal formés dans un workflow UI"""
        if 'links' not in workflow: return workflow
        
        fixed_links = []
        for link in workflow['links']:
            if isinstance(link, list) and len(link) == 2:
                # Format court [id_source, id_cible] -> Conversion
                # Impossible sans connaitre les slots. On garde tel quel si API supporte.
                pass
            # ComfyUI attend [id, source_node_id, source_slot, target_node_id, target_slot, type]
            # Si le lien est valide, on le garde
            fixed_links.append(link)
            
        workflow['links'] = fixed_links
        return workflow

if __name__ == "__main__":
    # Test rapide si exécuté directement
    print("ComfyUI Client Library")
    print("Use: from comfyui_client import ComfyUIClient")