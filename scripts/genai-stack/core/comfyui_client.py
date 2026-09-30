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
import uuid
import logging
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
    
    def __init__(self, config: Optional[ComfyUIConfig] = None) -> None:
        self.config = config or ComfyUIConfig()
        self.session = requests.Session()
        self.client_id = f"ComfyUIClient-{uuid.uuid4().hex[:12]}"
        
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
            logging.debug("is_reachable failed: %s", e)
            return False

    def get_system_stats(self) -> Dict[str, Any]:
        """Récupère les stats système"""
        return self._request('GET', '/system_stats').json()

    def get_object_info(self, node_class: Optional[str] = None) -> Dict[str, Any]:
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

    # Noeuds de commentaire : presents dans le format UI, inexistants en API.
    NOTE_TYPES = ('Note', 'MarkdownNote')
    # Aiguillage purement frontend (`Reroute` est absent de `/object_info` sur
    # les instances ou il n'est pas un noeud serveur) : il ne transporte rien,
    # donc on remonte a sa source au lieu de le filtrer -- le filtrer perdrait
    # le lien qu'il portait.
    REROUTE_TYPES = ('Reroute',)
    # Widgets dont le frontend emet DEUX valeurs : la valeur et le mode de
    # regeneration associe (ex. `seed` suivi de `control_after_generate`).
    SEED_WIDGETS = ('seed', 'noise_seed')
    # Types rendus par un widget ; tout le reste est un lien. `COMBO` est le
    # type des listes de choix depuis 0.37 (les options vivent dans le dict qui
    # suit, la ou les versions anterieures mettaient la liste en premier).
    WIDGET_TYPES = ('INT', 'FLOAT', 'STRING', 'BOOLEAN', 'COMBO')

    @staticmethod
    def widget_names(class_type: str, object_info: Dict[str, Any]) -> List[str]:
        """Noms des entrees rendues par un widget, dans l'ordre du noeud.

        Un type `list` (COMBO) ou primitif est un widget ; un nom de type de
        noeud (MODEL, IMAGE, ...) est un lien et n'a pas de valeur de widget.
        """
        spec = (object_info.get(class_type) or {}).get('input') or {}
        names: List[str] = []
        for section in ('required', 'optional'):
            for name, definition in (spec.get(section) or {}).items():
                if not isinstance(definition, (list, tuple)) or not definition:
                    continue
                kind = definition[0]
                if isinstance(kind, list) or kind in WorkflowManager.WIDGET_TYPES:
                    names.append(name)
        return names

    @staticmethod
    def frontend_only_widgets(class_type: str, object_info: Dict[str, Any]) -> int:
        """Nombre de valeurs de widget que seul le frontend connait.

        `LoadImage` en porte une : le bouton d'upload, que le serveur ne declare
        pas comme entree mais dont `object_info` donne la cle (`image_upload`).
        Elle est stockee en FIN de `widgets_values` et n'a pas d'equivalent API.
        """
        spec = (object_info.get(class_type) or {}).get('input') or {}
        count = 0
        for section in ('required', 'optional'):
            for definition in (spec.get(section) or {}).values():
                if isinstance(definition, (list, tuple)) and len(definition) > 1 \
                        and isinstance(definition[1], dict) and 'image_upload' in definition[1]:
                    count += 1
        return count

    @staticmethod
    def resolve_source(node_id: Any, slot: Any, by_id: Dict[Any, Any],
                       sources: Dict[Any, Any], seen: Optional[set] = None) -> Any:
        """Remonte une chaine de `Reroute` jusqu'au noeud qui produit vraiment."""
        seen = set() if seen is None else seen
        node = by_id.get(node_id)
        if not node or node.get('type') not in WorkflowManager.REROUTE_TYPES or node_id in seen:
            return node_id, slot
        seen.add(node_id)
        for entry in node.get('inputs') or []:
            source = sources.get(entry.get('link'))
            if source and source[0] is not None:
                return WorkflowManager.resolve_source(source[0], source[1],
                                                       by_id, sources, seen)
        return node_id, slot

    @staticmethod
    def convert_ui_to_api(ui_workflow: Dict[str, Any],
                          object_info: Dict[str, Any]) -> Dict[str, Any]:
        """Convertit un workflow UI (liste `nodes`) en format API (dict id->node).

        `object_info` (reponse de `GET /object_info`) est requis : c'est lui qui
        donne l'ordre des widgets par classe de noeud. Sans lui, l'appariement
        `widgets_values` <-> noms d'entrees serait devine.

        Leve `ValueError` des qu'un noeud ne s'apparie pas exactement : un
        graphe silencieusement mal apparie produirait une image fausse.
        """
        # id de lien -> (id du noeud source, slot de sortie source)
        sources: Dict[Any, Any] = {}
        for link in ui_workflow.get('links') or []:
            if isinstance(link, list) and len(link) >= 5:
                sources[link[0]] = (link[1], link[2])
            elif isinstance(link, dict):
                sources[link.get('id')] = (link.get('origin_id'), link.get('origin_slot'))

        by_id = {n.get('id'): n for n in ui_workflow.get('nodes') or []}

        api_workflow: Dict[str, Any] = {}
        for node in ui_workflow.get('nodes') or []:
            class_type = node.get('type')
            if class_type in WorkflowManager.NOTE_TYPES \
                    or class_type in WorkflowManager.REROUTE_TYPES:
                continue
            if node.get('mode') in (2, 4):  # muet / bypasse
                continue

            inputs: Dict[str, Any] = {}
            linked: Dict[str, Any] = {}
            for slot in node.get('inputs') or []:
                source = sources.get(slot.get('link'))
                if not source or source[0] is None:
                    continue
                origin = WorkflowManager.resolve_source(source[0], source[1],
                                                        by_id, sources)
                linked[slot['name']] = [str(origin[0]), origin[1]]

            # `widgets_values` est positionnel sur TOUS les widgets du noeud, y
            # compris ceux qu'un lien court-circuite (le frontend conserve la
            # derniere valeur saisie). L'appariement se fait donc sans filtrer,
            # et les liens ecrasent ensuite la valeur restee en place.
            names = WorkflowManager.widget_names(class_type, object_info)
            values = list(node.get('widgets_values') or [])

            # Un combo dynamique (`COMFY_DYNAMICCOMBO_V3`, ex. `resize_type` de
            # ResizeImageMaskNode) ouvre des sous-widgets dont le nombre depend
            # de la valeur choisie : `/object_info` ne les declare pas, et ils
            # s'intercalent AU MILIEU des autres widgets. Rien ne permet de les
            # apparier sans les deviner : on refuse au lieu de produire un
            # graphe faux.
            spec = (object_info.get(class_type) or {}).get('input') or {}
            for section in ('required', 'optional'):
                for name, definition in (spec.get(section) or {}).items():
                    if isinstance(definition, (list, tuple)) and definition \
                            and definition[0] == 'COMFY_DYNAMICCOMBO_V3':
                        raise ValueError(
                            f"{class_type} (id {node.get('id')}) : combo dynamique "
                            f"`{name}` — ses sous-widgets ne sont pas declares par "
                            f"/object_info et ne peuvent pas etre apparies")

            ignored = WorkflowManager.frontend_only_widgets(class_type, object_info)
            if len(values) == len(names) + ignored:
                values = values[:len(names)]

            extra_seed = len(values) - len(names)
            expanded: List[str] = []
            for name in names:
                expanded.append(name)
                if name in WorkflowManager.SEED_WIDGETS and extra_seed > 0:
                    expanded.append('control_after_generate')
                    extra_seed -= 1
            names = expanded

            if len(values) != len(names):
                raise ValueError(
                    f"{class_type} (id {node.get('id')}) : {len(values)} widgets_values "
                    f"pour {len(names)} entrees de widget {names}")

            inputs.update(dict(zip(names, values)))
            inputs.update(linked)
            api_workflow[str(node['id'])] = {"class_type": class_type, "inputs": inputs}

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