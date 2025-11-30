#!/usr/bin/env python3
"""
ComfyUI Client Helper - Utilitaire complet pour investigations ComfyUI

Ce script consolide toutes les fonctionnalités d'interaction avec ComfyUI
en un seul outil réutilisable et extensible.

Auteur: Consolidation d'outils ComfyUI existants
Date: 2025-10-29
Version: 1.0.0

Scripts remplacés:
- inspect-qwen-*.py (inspection de nodes)
- test-qwen-*.py (tests de compatibilité)
- fix-qwen-workflow.py (réparation de workflows)
- validate-qwen-solution.py (validation de solutions)
- diagnostic-qwen-complete.py (diagnostics complets)

Usage:
    python comfyui-client-helper.py [mode] [options]

Modes disponibles:
    client      - Mode client interactif pour workflows
    batch       - Mode batch pour exécution automatisée
    debug       - Mode debug avec logs détaillés
    investigate  - Mode investigation des nodes et serveur
    help        - Affiche l'aide complète
"""

import sys
import os
import json
import time
import argparse
import subprocess
import tempfile
import requests
import urllib3
from pathlib import Path
from typing import Dict, List, Any, Optional, Union, Tuple
from dataclasses import dataclass
from datetime import datetime

# Désactiver les warnings SSL pour les environnements de développement
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


@dataclass
class ComfyUIConfig:
    """Configuration pour la connexion ComfyUI"""
    host: str = "localhost"
    port: int = 8188
    protocol: str = "http"
    api_key: Optional[str] = None
    timeout: int = 30
    max_retries: int = 3
    retry_delay: float = 1.0
    verify_ssl: bool = True


class ComfyUIError(Exception):
    """Exception de base pour les erreurs ComfyUI"""
    def __init__(self, message: str, status_code: Optional[int] = None, response: Optional[requests.Response] = None):
        super().__init__(message)
        self.message = message
        self.status_code = status_code
        self.response = response


class ComfyUIClient:
    """Client HTTP complet pour ComfyUI avec gestion des sessions et erreurs"""
    
    def __init__(self, config: ComfyUIConfig):
        self.config = config
        self.session = requests.Session()
        self.client_id = None
        self.prompt_id = None
        
        # Configuration de la session
        self.session.headers.update({
            'User-Agent': 'ComfyUI-Client-Helper/1.0.0',
            'Content-Type': 'application/json'
        })
        
        if config.api_key:
            # Si le token commence déjà par "Bearer " ou "Basic ", ne pas l'ajouter
            if config.api_key.startswith("Bearer ") or config.api_key.startswith("Basic "):
                self.session.headers['Authorization'] = config.api_key
            else:
                # Par défaut, essayer Bearer, mais si ça échoue, on pourrait avoir besoin de Basic
                # Pour l'instant on garde Bearer par défaut pour compatibilité
                self.session.headers['Authorization'] = f'Bearer {config.api_key}'
            
            # DEBUG: Afficher le header d'autorisation (masqué)
            auth_header = self.session.headers['Authorization']
            masked_auth = auth_header[:15] + "..." + auth_header[-5:] if len(auth_header) > 20 else "***"
            print(f"🔑 Auth Header configuré: {masked_auth}")
    
    def _get_base_url(self) -> str:
        """Retourne l'URL de base de l'API ComfyUI"""
        return f"{self.config.protocol}://{self.config.host}:{self.config.port}"
    
    def _make_request(self, method: str, endpoint: str, **kwargs) -> requests.Response:
        """Effectue une requête HTTP avec gestion des erreurs et retries"""
        url = f"{self._get_base_url()}{endpoint}"
        
        for attempt in range(self.config.max_retries):
            try:
                response = self.session.request(
                    method=method,
                    url=url,
                    timeout=self.config.timeout,
                    verify=self.config.verify_ssl,
                    **kwargs
                )
                
                # Gestion des erreurs HTTP
                if response.status_code == 400:
                    raise ComfyUIError(f"Requête invalide: {response.text}", 400, response)
                elif response.status_code == 401:
                    raise ComfyUIError(f"Non autorisé: vérifiez votre API key", 401, response)
                elif response.status_code == 403:
                    raise ComfyUIError(f"Accès interdit", 403, response)
                elif response.status_code == 404:
                    raise ComfyUIError(f"Ressource non trouvée: {endpoint}", 404, response)
                elif response.status_code == 429:
                    raise ComfyUIError(f"Trop de requêtes - retry après délai", 429, response)
                elif response.status_code >= 500:
                    raise ComfyUIError(f"Erreur serveur ComfyUI: {response.text}", response.status_code, response)
                elif response.status_code not in [200, 201]:
                    raise ComfyUIError(f"Erreur HTTP {response.status_code}: {response.text}", response.status_code, response)
                
                return response
                
            except requests.exceptions.Timeout:
                if attempt < self.config.max_retries - 1:
                    print(f"⏱️ Timeout (tentative {attempt + 1}/{self.config.max_retries}), retry...")
                    time.sleep(self.config.retry_delay * (2 ** attempt))
                    continue
                raise ComfyUIError(f"Timeout après {self.config.max_retries} tentatives")
                
            except requests.exceptions.ConnectionError as e:
                if attempt < self.config.max_retries - 1:
                    print(f"🔌 Connexion échouée (tentative {attempt + 1}/{self.config.max_retries}), retry...")
                    time.sleep(self.config.retry_delay * (2 ** attempt))
                    continue
                raise ComfyUIError(f"Connexion impossible après {self.config.max_retries} tentatives: {e}")
                
            except requests.exceptions.RequestException as e:
                raise ComfyUIError(f"Erreur requête HTTP: {e}")
        
        raise ComfyUIError(f"Échec après {self.config.max_retries} tentatives")
    
    def test_connectivity(self) -> bool:
        """Test la connectivité avec le serveur ComfyUI"""
        try:
            response = self._make_request('GET', '/system_stats')
            print(f"✅ Connectivité OK: Serveur ComfyUI accessible")
            return True
        except ComfyUIError as e:
            print(f"❌ Connectivité échouée: {e.message}")
            return False
    
    def get_server_info(self) -> Dict[str, Any]:
        """Récupère les informations du serveur ComfyUI"""
        try:
            response = self._make_request('GET', '/system_stats')
            return response.json()
        except ComfyUIError as e:
            print(f"❌ Impossible récupérer infos serveur: {e.message}")
            return {}
    
    def get_system_stats(self) -> Dict[str, Any]:
        """Récupère les statistiques système de ComfyUI"""
        try:
            response = self._make_request('GET', '/system_stats')
            return response.json()
        except ComfyUIError as e:
            print(f"❌ Impossible récupérer stats système: {e.message}")
            return {}
    
    def get_object_info(self, node_class: str = None) -> Dict[str, Any]:
        """Récupère les informations des objets/nodes disponibles"""
        try:
            if node_class:
                response = self._make_request('GET', f'/object_info/{node_class}')
                return response.json()
            else:
                response = self._make_request('GET', '/object_info')
                return response.json()
        except ComfyUIError as e:
            print(f"❌ Impossible récupérer infos node {node_class}: {e.message}")
            return {}
    
    def upload_file(self, file_path: str, file_type: str = "input") -> Optional[str]:
        """Upload un fichier vers ComfyUI et retourne le nom du fichier uploadé"""
        try:
            with open(file_path, 'rb') as f:
                files = {
                    file_type: (os.path.basename(file_path), f, 'application/octet-stream')
                }
                response = self._make_request('POST', '/upload', files=files)
                
                result = response.json()
                if 'name' in result:
                    print(f"✅ Fichier uploadé: {result['name']}")
                    return result['name']
                else:
                    print(f"❌ Upload échoué: {result}")
                    return None
                    
        except Exception as e:
            print(f"❌ Erreur upload fichier {file_path}: {e}")
            return None
    
    def submit_workflow(self, workflow: Dict[str, Any], files: Optional[List[str]] = None) -> Optional[str]:
        """Soumet un workflow ComfyUI et retourne le prompt_id"""
        try:
            # Upload des fichiers si nécessaire
            uploaded_files = []
            if files:
                for file_path in files:
                    uploaded_name = self.upload_file(file_path)
                    if uploaded_name:
                        uploaded_files.append(uploaded_name)
            
            # Préparation du payload
            payload = {
                'prompt': workflow,
                'client_id': self.client_id
            }
            
            response = self._make_request('POST', '/prompt', json=payload)
            result = response.json()
            
            if 'prompt_id' in result:
                self.prompt_id = result['prompt_id']
                print(f"✅ Workflow soumis: {self.prompt_id}")
                return self.prompt_id
            else:
                print(f"❌ Soumission échouée: {result}")
                return None
                
        except ComfyUIError as e:
            print(f"❌ Erreur soumission workflow: {e.message}")
            return None
    
    def get_queue_status(self) -> Dict[str, Any]:
        """Récupère le statut de la file d'attente"""
        try:
            response = self._make_request('GET', '/queue')
            return response.json()
        except ComfyUIError as e:
            print(f"❌ Erreur récupération queue: {e.message}")
            return {}
    
    def get_history(self, prompt_id: Optional[str] = None) -> Dict[str, Any]:
        """Récupère l'historique des exécutions"""
        try:
            if prompt_id:
                response = self._make_request('GET', f'/history/{prompt_id}')
            else:
                response = self._make_request('GET', '/history')
            return response.json()
        except ComfyUIError as e:
            print(f"❌ Erreur récupération historique: {e.message}")
            return {}
    
    def get_result(self, prompt_id: str, wait_completion: bool = True, timeout: int = 300) -> Optional[Dict[str, Any]]:
        """Récupère le résultat d'un workflow avec suivi de progression"""
        start_time = time.time()
        
        while wait_completion and time.time() - start_time < timeout:
            try:
                history = self.get_history(prompt_id)
                
                if prompt_id in history:
                    result = history[prompt_id]
                    
                    # Vérifier le statut
                    if result.get('status', {}).get('completed', False):
                        outputs = result.get('outputs', {})
                        print(f"✅ Workflow complété: {len(outputs)} outputs")
                        return result
                    else:
                        # Afficher la progression
                        queue_info = self.get_queue_status()
                        running = queue_info.get('queue_running', [])
                        if running:
                            print(f"⏳ En cours... (temps écoulé: {int(time.time() - start_time)}s)")
                        time.sleep(2)
                        continue
                
                time.sleep(1)
                
            except ComfyUIError as e:
                print(f"❌ Erreur récupération résultat: {e.message}")
                return None
        
        if wait_completion:
            print(f"⏱️ Timeout après {timeout}s pour le prompt {prompt_id}")
        
        # Retourner le dernier état connu
        history = self.get_history(prompt_id)
        if prompt_id in history:
            return history[prompt_id]
        
        return None
    
    def download_result(self, prompt_id: str, output_dir: str = "./output") -> bool:
        """Télécharge les résultats (images, métadonnées) d'un workflow"""
        try:
            result = self.get_result(prompt_id, wait_completion=False)
            if not result:
                return False
            
            outputs = result.get('outputs', {})
            if not outputs:
                print("❌ Aucun output à télécharger")
                return False
            
            # Créer le répertoire de sortie
            Path(output_dir).mkdir(parents=True, exist_ok=True)
            
            downloaded_count = 0
            for node_id, node_outputs in outputs.items():
                # Les outputs peuvent être un dict ou une liste de dicts
                if isinstance(node_outputs, dict):
                    items_to_process = node_outputs.items()
                elif isinstance(node_outputs, list):
                    # Si c'est une liste, on suppose que ce sont des images
                    items_to_process = [("images", item) for item in node_outputs]
                else:
                    print(f"⚠️ Format d'output inconnu pour le node {node_id}: {type(node_outputs)}")
                    continue

                # Si items_to_process est une liste de tuples (cas liste), on itère directement
                # Si c'est une liste de dicts (cas liste d'images), on doit adapter
                
                final_items = []
                if isinstance(node_outputs, list):
                    # C'est une liste d'objets (probablement des images)
                    for item in node_outputs:
                        final_items.append(("image", item))
                elif isinstance(node_outputs, dict):
                    # C'est un dictionnaire clé-valeur
                    for k, v in node_outputs.items():
                        # Si la valeur est une liste (ex: images: [{...}]), on l'aplatit
                        if isinstance(v, list):
                            for item in v:
                                final_items.append((k, item))
                        else:
                            final_items.append((k, v))
                
                for output_name, output_data in final_items:
                    # DEBUG: Afficher les données de sortie pour diagnostic
                    print(f"🔍 Analyse output: {output_name} -> {output_data}")
                    
                    # Vérification plus souple pour les images
                    is_image = False
                    if isinstance(output_data, dict):
                        # Cas standard: type='image' ou extension d'image dans filename
                        # Note: ComfyUI retourne parfois type='output' pour les images sauvegardées
                        if output_data.get('type') in ['image', 'output', 'temp']:
                            is_image = True
                            print(f"   ✅ Identifié comme image via type='{output_data.get('type')}'")
                        elif 'filename' in output_data:
                            ext = os.path.splitext(output_data['filename'])[1].lower()
                            if ext in ['.png', '.jpg', '.jpeg', '.webp']:
                                is_image = True
                                print(f"   ✅ Identifié comme image via extension='{ext}'")
                        else:
                            print(f"   ⚠️ Non identifié comme image (type={output_data.get('type')}, filename={output_data.get('filename')})")
                    else:
                        print(f"   ⚠️ Données invalides (pas un dict): {type(output_data)}")
                    
                    if is_image and 'filename' in output_data:
                        # Télécharger l'image
                        image_url = f"{self._get_base_url()}/view?filename={output_data['filename']}"
                        if 'subfolder' in output_data and output_data['subfolder']:
                            image_url += f"&subfolder={output_data['subfolder']}"
                        if 'type' in output_data and output_data['type']:
                            image_url += f"&type={output_data['type']}"
                            
                        print(f"⬇️ Téléchargement depuis: {image_url}")
                        img_response = self.session.get(image_url, stream=True)
                        
                        if img_response.status_code == 200:
                            img_path = Path(output_dir) / output_data['filename']
                            with open(img_path, 'wb') as f:
                                for chunk in img_response.iter_content(chunk_size=8192):
                                    f.write(chunk)
                            print(f"✅ Image téléchargée: {img_path}")
                            downloaded_count += 1
                        else:
                            print(f"❌ Erreur téléchargement (HTTP {img_response.status_code}): {img_response.text[:100]}")
                        
                        # Télécharger les métadonnées
                        metadata = {k: v for k, v in output_data.items() if k != 'filename'}
                        if metadata:
                            metadata_path = Path(output_dir) / f"{output_data['filename']}.json"
                            with open(metadata_path, 'w') as f:
                                json.dump(metadata, f, indent=2)
                            print(f"✅ Métadonnées sauvegardées: {metadata_path}")
            
            print(f"✅ Téléchargement terminé: {downloaded_count} fichiers")
            return True
            
        except Exception as e:
            print(f"❌ Erreur téléchargement résultat: {e}")
            return False


class WorkflowManager:
    """Gestionnaire de workflows JSON pour ComfyUI"""
    
    @staticmethod
    def load_workflow(file_path: str) -> Optional[Dict[str, Any]]:
        """Charge et valide un workflow JSON"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                workflow = json.load(f)
            
            # Validation basique
            if not isinstance(workflow, dict):
                print(f"❌ Workflow invalide: doit être un dictionnaire")
                return None
            
            if 'nodes' not in workflow:
                print(f"❌ Workflow invalide: section 'nodes' manquante")
                return None
            
            print(f"✅ Workflow chargé: {len(workflow.get('nodes', []))} nodes")
            return workflow
            
        except json.JSONDecodeError as e:
            print(f"❌ Erreur JSON dans {file_path}: {e}")
            return None
        except Exception as e:
            print(f"❌ Erreur chargement workflow {file_path}: {e}")
            return None
    
    @staticmethod
    def validate_workflow(workflow: Dict[str, Any]) -> Tuple[bool, List[str]]:
        """Valide la structure d'un workflow et retourne les erreurs"""
        errors = []
        
        # Validation des sections requises
        required_sections = ['nodes', 'links', 'groups', 'config', 'extra', 'version']
        for section in required_sections:
            if section not in workflow:
                errors.append(f"Section '{section}' manquante")
        
        # Validation des nodes
        nodes = workflow.get('nodes', [])
        for i, node in enumerate(nodes):
            if not isinstance(node, dict):
                errors.append(f"Node {i}: doit être un dictionnaire")
                continue
            
            if 'id' not in node:
                errors.append(f"Node {i}: ID manquant")
            
            if 'type' not in node:
                errors.append(f"Node {i}: type manquant")
        
        # Validation des liens
        links = workflow.get('links', [])
        for i, link in enumerate(links):
            if not isinstance(link, list) or len(link) != 4:
                errors.append(f"Link {i}: format invalide (doit être [source_id, source_slot, target_id, target_slot])")
        
        is_valid = len(errors) == 0
        if is_valid:
            print("✅ Workflow valide")
        else:
            print(f"❌ Workflow invalide: {len(errors)} erreurs")
            for error in errors:
                print(f"  - {error}")
        
        return is_valid, errors
    
    @staticmethod
    def optimize_workflow(workflow: Dict[str, Any]) -> Dict[str, Any]:
        """Optimise un workflow pour de meilleures performances"""
        optimized = workflow.copy()
        
        # Supprimer les nodes déconnectés
        nodes = optimized.get('nodes', [])
        links = optimized.get('links', [])
        connected_node_ids = set()
        
        for link in links:
            connected_node_ids.add(link[0])  # source node
            connected_node_ids.add(link[2])  # target node
        
        # Filtrer les nodes connectés
        optimized['nodes'] = [
            node for node in nodes 
            if node.get('id') in connected_node_ids
        ]
        
        removed_count = len(nodes) - len(optimized['nodes'])
        if removed_count > 0:
            print(f"✅ Workflow optimisé: {removed_count} nodes déconnectés supprimés")
        
        return optimized


class InvestigationUtils:
    """Utilitaires d'investigation pour ComfyUI"""
    
    def __init__(self, client: ComfyUIClient, container_name: str = "comfyui-qwen"):
        self.client = client
        self.container_name = container_name
    
    def run_docker_command(self, command: str) -> Tuple[str, str, int]:
        """Exécute une commande dans le container Docker"""
        try:
            full_command = f"docker exec {self.container_name} bash -c '{command}'"
            result = subprocess.run(full_command, shell=True, capture_output=True, text=True)
            return result.stdout, result.stderr, result.returncode
        except Exception as e:
            return "", str(e), 1
    
    def inspect_nodes(self, node_pattern: str = "*") -> Dict[str, Any]:
        """Inspection des nodes disponibles dans le container"""
        print(f"🔍 Inspection des nodes: {node_pattern}")
        
        # Script Python pour l'inspection
        python_script = f'''
import sys
import os
import json
import importlib.util
import inspect
import glob

# Ajouter ComfyUI au sys.path
sys.path.insert(0, "/workspace/ComfyUI")

def inspect_node_file(file_path):
    """Inspecte un fichier de node individuel"""
    try:
        spec = importlib.util.spec_from_file_location("temp_node", file_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        # Extraire les classes
        classes = []
        for name, obj in vars(module).items():
            if inspect.isclass(obj) and hasattr(obj, 'RETURN_TYPES'):
                class_info = {{
                    'name': name,
                    'return_types': getattr(obj, 'RETURN_TYPES', None),
                    'return_names': getattr(obj, 'RETURN_NAMES', None),
                    'function': getattr(obj, 'FUNCTION', None),
                    'category': getattr(obj, 'CATEGORY', 'custom'),
                    'output_node': getattr(obj, 'OUTPUT_NODE', False),
                    'description': getattr(obj, 'DESCRIPTION', '')
                }}
                classes.append(class_info)
        
        return classes
    except Exception as e:
        return [{{'error': str(e)}}]

# Scanner les fichiers de nodes
results = {{}}
node_files = glob.glob("/workspace/ComfyUI/custom_nodes/**/{node_pattern}.py", recursive=True)
node_files.extend(glob.glob("/workspace/ComfyUI/custom_nodes/**/nodes/{node_pattern}.py", recursive=True))

for file_path in node_files:
    node_name = os.path.basename(file_path).replace('.py', '')
    results[node_name] = inspect_node_file(file_path)

print(json.dumps(results, indent=2, default=str))
'''
        
        # Créer et exécuter le script
        create_cmd = f"cat > /tmp/inspect_nodes.py << 'EOF'\n{python_script}\nEOF"
        stdout, stderr, code = self.run_docker_command(create_cmd)
        
        if code != 0:
            print(f"❌ Erreur création script: {stderr}")
            return {}
        
        exec_cmd = "source /workspace/ComfyUI/venv/bin/activate && python /tmp/inspect_nodes.py"
        stdout, stderr, code = self.run_docker_command(exec_cmd)
        
        # Nettoyer
        self.run_docker_command("rm -f /tmp/inspect_nodes.py")
        
        if code != 0:
            print(f"❌ Erreur exécution inspection: {stderr}")
            return {}
        
        try:
            result = json.loads(stdout)
            print(f"✅ Inspection terminée: {len(result)} nodes analysés")
            return result
        except json.JSONDecodeError:
            print(f"❌ Erreur parsing résultat: {stdout}")
            return {}
    
    def test_node_compatibility(self, node_class: str, test_inputs: Dict[str, Any]) -> Dict[str, Any]:
        """Test la compatibilité d'un node avec des inputs spécifiques"""
        print(f"🧪 Test de compatibilité: {node_class}")
        
        python_script = f'''
import sys
import json
sys.path.insert(0, "/workspace/ComfyUI")

try:
    # Import dynamique du node
    spec = importlib.util.spec_from_file_location("test_node", "/workspace/ComfyUI/custom_nodes/{node_class}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    
    # Trouver la classe principale
    node_class_obj = None
    for name, obj in vars(module).items():
        if inspect.isclass(obj) and hasattr(obj, 'RETURN_TYPES'):
            node_class_obj = obj
            break
    
    if not node_class_obj:
        print(json.dumps({{"error": "Classe de node non trouvée"}}))
        sys.exit(1)
    
    # Test d'instanciation avec les inputs fournis
    test_inputs = {json.dumps(test_inputs)}
    
    try:
        # Créer une instance factice
        if hasattr(node_class_obj, 'FUNCTION'):
            function_name = node_class_obj.FUNCTION
            if hasattr(node_class_obj, function_name):
                function = getattr(node_class_obj, function_name)
                
                # Appel avec des inputs factices
                result = function(**test_inputs)
                
                print(json.dumps({{
                    "success": True,
                    "node_class": f"{node_class}",
                    "return_types": getattr(node_class_obj, 'RETURN_TYPES', None),
                    "test_result": str(type(result)),
                    "test_inputs": test_inputs
                }}, default=str))
            else:
                print(json.dumps({"error": f"Fonction {function_name} non trouvée"}))
        else:
            print(json.dumps({{"error": "Attribut FUNCTION non défini"}}))
            
except Exception as e:
    print(json.dumps({{"error": str(e), "traceback": str(e.__class__.__name__)}}))
'''
        
        # Exécuter le test
        create_cmd = f"cat > /tmp/test_compatibility.py << 'EOF'\n{python_script}\nEOF"
        stdout, stderr, code = self.run_docker_command(create_cmd)
        
        if code != 0:
            return {"error": f"Création script échouée: {stderr}"}
        
        exec_cmd = "source /workspace/ComfyUI/venv/bin/activate && python /tmp/test_compatibility.py"
        stdout, stderr, code = self.run_docker_command(exec_cmd)
        
        # Nettoyer
        self.run_docker_command("rm -f /tmp/test_compatibility.py")
        
        if code != 0:
            return {"error": f"Test échoué: {stderr}"}
        
        try:
            return json.loads(stdout)
        except json.JSONDecodeError:
            return {"error": f"Résultat invalide: {stdout}"}
    
    def monitor_resources(self) -> Dict[str, Any]:
        """Monitore les ressources du serveur ComfyUI"""
        print("📊 Monitoring des ressources serveur...")
        
        try:
            # Stats système via API
            system_stats = self.client.get_server_info()
            
            # Stats Docker
            docker_stats_cmd = f"docker stats {self.container_name} --no-stream --format json"
            stdout, stderr, code = self.run_docker_command(docker_stats_cmd)
            
            docker_stats = {}
            if code == 0:
                try:
                    stats = json.loads(stdout)
                    if stats:
                        docker_stats = stats[0] if isinstance(stats, list) else stats
                except json.JSONDecodeError:
                    pass
            
            # Combinaison des stats
            resource_info = {
                'timestamp': datetime.now().isoformat(),
                'system_stats': system_stats,
                'docker_stats': docker_stats,
                'connectivity': self.client.test_connectivity()
            }
            
            print(f"✅ Monitoring terminé")
            return resource_info
            
        except Exception as e:
            return {"error": f"Monitoring échoué: {e}"}
    
    def debug_workflow_error(self, workflow: Dict[str, Any], error_details: str) -> Dict[str, Any]:
        """Debug des erreurs de workflow avec analyse détaillée"""
        print("🐛 Debug d'erreur de workflow...")
        
        debug_info = {
            'timestamp': datetime.now().isoformat(),
            'workflow_summary': {
                'node_count': len(workflow.get('nodes', [])),
                'link_count': len(workflow.get('links', [])),
                'has_errors': any('error' in str(node).lower() for node in workflow.get('nodes', []))
            },
            'error_details': error_details,
            'analysis': {}
        }
        
        # Analyse des erreurs communes
        nodes = workflow.get('nodes', [])
        error_nodes = []
        
        for i, node in enumerate(nodes):
            node_str = str(node)
            if 'error' in node_str.lower():
                error_nodes.append({
                    'index': i,
                    'id': node.get('id', 'unknown'),
                    'type': node.get('type', 'unknown'),
                    'error_indicators': []
                })
                
                # Chercher des indicateurs d'erreur
                if 'inputs' in node and not node['inputs']:
                    error_nodes[-1]['error_indicators'].append('inputs vides')
                
                if 'outputs' in node and not node['outputs']:
                    error_nodes[-1]['error_indicators'].append('outputs vides')
                
                missing_fields = []
                for field in ['id', 'type', 'pos']:
                    if field not in node:
                        missing_fields.append(field)
                if missing_fields:
                    error_nodes[-1]['error_indicators'].append(f'champs manquants: {missing_fields}')
        
        debug_info['analysis']['error_nodes'] = error_nodes
        
        # Recommandations
        recommendations = []
        if error_nodes:
            recommendations.append("Vérifier les connexions entre nodes")
            recommendations.append("Valider les types de données inputs/outputs")
        
        if len(nodes) == 0:
            recommendations.append("Ajouter des nodes au workflow")
        
        debug_info['analysis']['recommendations'] = recommendations
        
        print(f"✅ Debug terminé: {len(error_nodes)} erreurs identifiées")
        return debug_info


class PluginSystem:
    """Système de plugins pour l'extensibilité"""
    
    def __init__(self):
        self.plugins = {}
        self.plugin_dirs = []
    
    def load_plugins(self, plugin_dir: str = "./plugins"):
        """Charge les plugins depuis un répertoire"""
        plugin_path = Path(plugin_dir)
        if not plugin_path.exists():
            plugin_path.mkdir(parents=True, exist_ok=True)
            return
        
        for plugin_file in plugin_path.glob("*.py"):
            if plugin_file.name.startswith("__"):
                continue
            
            try:
                plugin_name = plugin_file.stem
                spec = importlib.util.spec_from_file_location(plugin_name, str(plugin_file))
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)
                
                if hasattr(module, 'register_plugin'):
                    module.register_plugin(self)
                    print(f"✅ Plugin chargé: {plugin_name}")
                
            except Exception as e:
                print(f"❌ Erreur chargement plugin {plugin_file}: {e}")
    
    def register_plugin(self, plugin_name: str, plugin_class):
        """Enregistre un plugin"""
        self.plugins[plugin_name] = plugin_class
    
    def get_plugin(self, plugin_name: str):
        """Récupère un plugin spécifique"""
        return self.plugins.get(plugin_name)
    
    def list_plugins(self) -> List[str]:
        """Liste tous les plugins chargés"""
        return list(self.plugins.keys())


class ComfyUIHelperCLI:
    """Interface en ligne de commande pour ComfyUI Client Helper"""
    
    def __init__(self):
        self.config = ComfyUIConfig()
        self.client = None
        self.investigation = None
        self.plugin_system = PluginSystem()
        
        # Charger les plugins
        self.plugin_system.load_plugins()
    
    def setup_parser(self) -> argparse.ArgumentParser:
        """Configure le parser d'arguments"""
        parser = argparse.ArgumentParser(
            description="ComfyUI Client Helper - Utilitaire complet pour investigations ComfyUI",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog="""
Exemples:
  # Mode client interactif
  python comfyui-client-helper.py client --host localhost --port 8188
  
  # Mode batch avec workflow
  python comfyui-client-helper.py batch --workflow workflow.json --output ./results
  
  # Mode investigation
  python comfyui-client-helper.py investigate --nodes "*Qwen*" --container comfyui-qwen
  
  # Mode debug
  python comfyui-client-helper.py debug --workflow workflow.json --verbose
            """
        )
        
        # Arguments globaux
        parser.add_argument('--host', default='localhost', help='Hôte ComfyUI (défaut: localhost)')
        parser.add_argument('--port', type=int, default=8188, help='Port ComfyUI (défaut: 8188)')
        parser.add_argument('--protocol', choices=['http', 'https'], default='http', help='Protocole (défaut: http)')
        parser.add_argument('--api-key', help='Clé API ComfyUI')
        parser.add_argument('--timeout', type=int, default=30, help='Timeout en secondes (défaut: 30)')
        parser.add_argument('--no-ssl-verify', action='store_true', help='Désactiver la vérification SSL')
        
        # Sous-commandes
        subparsers = parser.add_subparsers(dest='mode', help='Mode d\'exécution')
        
        # Mode client
        client_parser = subparsers.add_parser('client', help='Mode client interactif')
        client_parser.add_argument('--workflow', help='Fichier workflow à charger')
        client_parser.add_argument('--output', default='./output', help='Répertoire de sortie')
        
        # Mode batch
        batch_parser = subparsers.add_parser('batch', help='Mode batch pour exécution automatisée')
        batch_parser.add_argument('--workflow', required=True, help='Fichier workflow à exécuter')
        batch_parser.add_argument('--output', default='./output', help='Répertoire de sortie')
        batch_parser.add_argument('--files', nargs='*', help='Fichiers à uploader')
        
        # Mode investigate
        investigate_parser = subparsers.add_parser('investigate', help='Mode investigation des nodes et serveur')
        investigate_parser.add_argument('--nodes', default='*', help='Pattern des nodes à inspecter')
        investigate_parser.add_argument('--container', default='comfyui-qwen', help='Nom du container Docker')
        investigate_parser.add_argument('--test-compatibility', help='Test de compatibilité d\'un node spécifique')
        investigate_parser.add_argument('--monitor', action='store_true', help='Monitorer les ressources serveur')
        
        # Mode debug
        debug_parser = subparsers.add_parser('debug', help='Mode debug avec logs détaillés')
        debug_parser.add_argument('--workflow', required=True, help='Fichier workflow à debugger')
        debug_parser.add_argument('--verbose', action='store_true', help='Logs détaillés')
        debug_parser.add_argument('--fix', action='store_true', help='Tenter de réparer automatiquement')
        
        # Mode help
        help_parser = subparsers.add_parser('help', help='Affiche l\'aide complète')
        
        return parser
    
    def run_client_mode(self, args):
        """Mode client interactif"""
        print("🖥️  Mode Client Interactif ComfyUI")
        print("=" * 50)
        
        # Initialiser le client
        self.client = ComfyUIClient(self.config)
        
        if not self.client.test_connectivity():
            print("❌ Connexion au serveur ComfyUI échouée")
            return
        
        print("✅ Connecté au serveur ComfyUI")
        
        # Charger le workflow si spécifié
        workflow = None
        if args.workflow:
            workflow = WorkflowManager.load_workflow(args.workflow)
            if not workflow:
                print(f"❌ Impossible charger le workflow: {args.workflow}")
                return
            
            is_valid, errors = WorkflowManager.validate_workflow(workflow)
            if not is_valid:
                print("❌ Workflow invalide:")
                for error in errors:
                    print(f"  - {error}")
                return
            
            print(f"✅ Workflow chargé: {len(workflow.get('nodes', []))} nodes")
        
        # Interface interactive simple
        print("\nCommandes disponibles:")
        print("  submit    - Soumettre le workflow actuel")
        print("  status    - Vérifier le statut de la file d'attente")
        print("  result    - Récupérer le résultat")
        print("  download  - Télécharger les outputs")
        print("  info      - Infos serveur")
        print("  quit      - Quitter")
        
        while True:
            try:
                command = input("\nComfyUI> ").strip().lower()
                
                if command == 'quit' or command == 'exit':
                    print("👋 Au revoir!")
                    break
                elif command == 'submit' and workflow:
                    prompt_id = self.client.submit_workflow(workflow)
                    if prompt_id:
                        print(f"✅ Workflow soumis avec ID: {prompt_id}")
                elif command == 'status':
                    queue = self.client.get_queue_status()
                    running = len(queue.get('queue_running', []))
                    pending = len(queue.get('queue_pending', []))
                    print(f"📊 File: {running} en cours, {pending} en attente")
                elif command == 'result' and self.client.prompt_id:
                    result = self.client.get_result(self.client.prompt_id)
                    if result:
                        status = result.get('status', {}).get('completed', False)
                        print(f"📋 Statut: {'Complété' if status else 'En cours'}")
                elif command == 'download' and self.client.prompt_id:
                    success = self.client.download_result(self.client.prompt_id, args.output)
                    print(f"{'✅ Téléchargement réussi' if success else '❌ Téléchargement échoué'}")
                elif command == 'info':
                    info = self.client.get_server_info()
                    print(f"📊 Infos serveur: {json.dumps(info, indent=2)}")
                else:
                    print("❌ Commande inconnue ou workflow non chargé")
                    
            except KeyboardInterrupt:
                print("\n👋 Interruption utilisateur")
                break
            except Exception as e:
                print(f"❌ Erreur: {e}")
    
    def run_batch_mode(self, args):
        """Mode batch pour exécution automatisée"""
        print("🤖 Mode Batch ComfyUI")
        print("=" * 50)
        
        # Initialiser le client
        self.client = ComfyUIClient(self.config)
        
        if not self.client.test_connectivity():
            print("❌ Connexion au serveur ComfyUI échouée")
            return False
        
        # Charger et valider le workflow
        workflow = WorkflowManager.load_workflow(args.workflow)
        if not workflow:
            print(f"❌ Impossible charger le workflow: {args.workflow}")
            return False
        
        is_valid, errors = WorkflowManager.validate_workflow(workflow)
        if not is_valid:
            print("❌ Workflow invalide:")
            for error in errors:
                print(f"  - {error}")
            return False
        
        print(f"✅ Workflow chargé et validé: {len(workflow.get('nodes', []))} nodes")
        
        # Soumettre le workflow
        prompt_id = self.client.submit_workflow(workflow, args.files)
        if not prompt_id:
            print("❌ Soumission du workflow échouée")
            return False
        
        print(f"✅ Workflow soumis: {prompt_id}")
        
        # Attendre la complétion
        print("⏳ Attente de complétion...")
        result = self.client.get_result(prompt_id, wait_completion=True)
        
        if result and result.get('status', {}).get('completed', False):
            print("✅ Workflow complété avec succès")
            
            # Télécharger les résultats
            success = self.client.download_result(prompt_id, args.output)
            if success:
                print(f"✅ Résultats téléchargés dans: {args.output}")
                return True
            else:
                print("❌ Téléchargement des résultats échoué")
                return False
        else:
            print("❌ Workflow échoué ou timeout")
            return False
    
    def run_investigate_mode(self, args):
        """Mode investigation des nodes et serveur"""
        print("🔍 Mode Investigation ComfyUI")
        print("=" * 50)
        
        # Initialiser le client et l'investigation
        self.client = ComfyUIClient(self.config)
        self.investigation = InvestigationUtils(self.client, args.container)
        
        if not self.client.test_connectivity():
            print("❌ Connexion au serveur ComfyUI échouée")
            return
        
        print("✅ Connecté au serveur ComfyUI")
        
        # Inspection des nodes
        if args.nodes != '*':
            nodes_info = self.investigation.inspect_nodes(args.nodes)
            print(f"📋 Résultats inspection:")
            for node_name, info in nodes_info.items():
                if 'error' in info:
                    print(f"  ❌ {node_name}: {info['error']}")
                else:
                    print(f"  ✅ {node_name}: {len(info)} classes trouvées")
        
        # Test de compatibilité
        if args.test_compatibility:
            test_inputs = {
                "seed": 42,
                "steps": 20,
                "cfg": 7.0,
                "sampler_name": "euler_ancestral",
                "scheduler": "normal"
            }
            result = self.investigation.test_node_compatibility(args.test_compatibility, test_inputs)
            print(f"🧪 Résultat test compatibilité:")
            print(json.dumps(result, indent=2))
        
        # Monitoring des ressources
        if args.monitor:
            resources = self.investigation.monitor_resources()
            print(f"📊 Ressources:")
            print(json.dumps(resources, indent=2, default=str))
    
    def run_debug_mode(self, args):
        """Mode debug avec logs détaillés"""
        print("🐛 Mode Debug ComfyUI")
        print("=" * 50)
        
        # Charger le workflow
        workflow = WorkflowManager.load_workflow(args.workflow)
        if not workflow:
            print(f"❌ Impossible charger le workflow: {args.workflow}")
            return
        
        print(f"✅ Workflow chargé: {len(workflow.get('nodes', []))} nodes")
        
        # Initialiser l'investigation
        self.client = ComfyUIClient(self.config)
        self.investigation = InvestigationUtils(self.client)
        
        # Analyse du workflow
        is_valid, errors = WorkflowManager.validate_workflow(workflow)
        if not is_valid:
            print("❌ Erreurs de validation:")
            for error in errors:
                print(f"  - {error}")
        
        # Debug des erreurs
        error_details = f"Validation workflow: {len(errors)} erreurs trouvées"
        debug_info = self.investigation.debug_workflow_error(workflow, error_details)
        
        print(f"🐛 Analyse debug:")
        print(json.dumps(debug_info, indent=2, default=str))
        
        # Tentative de réparation automatique
        if args.fix:
            print("🔧 Tentative de réparation automatique...")
            
            # Optimiser le workflow
            optimized = WorkflowManager.optimize_workflow(workflow)
            
            # Sauvegarder le workflow réparé
            fixed_path = args.workflow.replace('.json', '_fixed.json')
            with open(fixed_path, 'w') as f:
                json.dump(optimized, f, indent=2)
            
            print(f"✅ Workflow réparé sauvegardé: {fixed_path}")
    
    def run_help_mode(self, args):
        """Mode help avec exemples"""
        print("📚 ComfyUI Client Helper - Aide Complète")
        print("=" * 60)
        
        help_text = """
## SCRIPTS REMPLACÉS

Ce script consolide et remplace efficacement les scripts d'interaction ComfyUI existants :

### Scripts de diagnostic et inspection
- inspect-qwen-*.py
  → Remplacé par: comfyui-client-helper.py investigate --nodes "*Qwen*"

### Scripts de test et validation
- test-qwen-*.py
  → Remplacé par: comfyui-client-helper.py investigate --test-compatibility <node>

### Scripts de réparation
- fix-qwen-workflow.py
  → Remplacé par: comfyui-client-helper.py debug --workflow <file> --fix

### Scripts de validation
- validate-qwen-solution.py
  → Remplacé par: comfyui-client-helper.py debug --workflow <file>

### Scripts de diagnostic complet
- diagnostic-qwen-complete.py
  → Remplacé par: comfyui-client-helper.py investigate --monitor

## EXEMPLES D'UTILISATION

### 1. Mode Client Interactif
```bash
# Démarrer le client interactif
python comfyui-client-helper.py client --host localhost --port 8188

# Avec workflow préchargé
python comfyui-client-helper.py client --workflow mon_workflow.json --output ./results
```

### 2. Mode Batch Automatisé
```bash
# Exécuter un workflow en batch
python comfyui-client-helper.py batch --workflow workflow.json --output ./results --files image1.jpg image2.png

# Traitement multiple de workflows
for workflow in workflows/*.json; do
    python comfyui-client-helper.py batch --workflow "$workflow" --output "./results/$(basename "$workflow" .json)"
done
```

### 3. Mode Investigation
```bash
# Inspecter tous les nodes Qwen
python comfyui-client-helper.py investigate --nodes "*Qwen*" --container comfyui-qwen

# Test de compatibilité spécifique
python comfyui-client-helper.py investigate --test-compatibility QwenImageSamplerNode

# Monitoring des ressources
python comfyui-client-helper.py investigate --monitor --container comfyui-qwen
```

### 4. Mode Debug
```bash
# Analyser un workflow avec erreurs
python comfyui-client-helper.py debug --workflow workflow_erreur.json --verbose

# Réparation automatique
python comfyui-client-helper.py debug --workflow workflow_casse.json --fix
```

### 5. Workflows Types pour Qwen

#### Workflow de base Qwen
```json
{
  "nodes": [
    {
      "id": 1,
      "type": "QwenImageSamplerNode",
      "inputs": {
        "seed": 42,
        "steps": 20,
        "cfg": 7.0,
        "sampler_name": "euler_ancestral",
        "scheduler": "normal",
        "transformer": ["1", 1],
        "positive": ["conditioning", 0],
        "negative": ["conditioning", 1],
        "latent_image": ["latent", 0]
      }
    }
  ],
  "links": [],
  "groups": [],
  "config": {},
  "extra": {},
  "version": 0.4
}
```

#### Workflow avec VAEDecode
```json
{
  "nodes": [
    {
      "id": 1,
      "type": "QwenImageSamplerNode",
      "inputs": {
        "seed": 42,
        "steps": 20,
        "cfg": 7.0,
        "sampler_name": "euler_ancestral",
        "scheduler": "normal",
        "transformer": ["1", 1],
        "positive": ["conditioning", 0],
        "negative": ["conditioning", 1],
        "latent_image": ["latent", 0]
      }
    },
    {
      "id": 2,
      "type": "VAEDecode",
      "inputs": {
        "samples": ["latent", 1]
      }
    }
  ],
  "links": [
    [1, 0, 2, 0]
  ],
  "groups": [],
  "config": {},
  "extra": {},
  "version": 0.4
}
"""

## RÉFÉRENCE API COMPLÈTE

### Endpoints principaux
# - GET  /system_stats          - Statistiques du serveur
# - GET  /object_info/{class}  - Informations sur un node
# - POST /prompt               - Soumettre un workflow
# - GET  /queue                - File d'attente
# - GET  /history/{prompt_id}  - Historique d'exécution
# - GET  /view?filename=X     - Télécharger un fichier
# - POST /upload               - Uploader un fichier

### Codes d'erreur
# - 200: Succès
# - 400: Requête invalide
# - 401: Non autorisé (API key)
# - 403: Accès interdit
# - 404: Ressource non trouvée
# - 429: Trop de requêtes
# - 500+: Erreur serveur

## CONFIGURATION

### Variables d'environnement
# ```bash
# export COMFYUI_HOST=localhost
# export COMFYUI_PORT=8188
# export COMFYUI_API_KEY=votre_clé_api
# export COMFYUI_PROTOCOL=http
# ```

### Fichier de configuration
# ```json
# {
#   "host": "localhost",
#   "port": 8188,
#   "protocol": "http",
#   "api_key": null,
#   "timeout": 30,
#   "max_retries":3,
#   "retry_delay": 1.0,
#   "verify_ssl": true
# }
# ```

## EXTENSIBILITÉ

### Créer un plugin
# plugins/mon_plugin.py

def register_plugin(plugin_system):
    # Register plugin in system
    plugin_system.register_plugin('mon_plugin', MonPlugin)

class MonPlugin:
    # Custom plugin example
    
    def __init__(self, client):
        self.client = client
    
    def custom_investigation(self, params):
        # Custom investigation method
        # Votre logique ici
        pass
    
    def custom_workflow_processor(self, workflow):
        # Custom workflow processing
        # Votre logique ici
        return workflow

# Exemple de code

### Utiliser un plugin
# ```python
# # Exemple de code Python
# # Le plugin est automatiquement chargé et disponible
# plugin = helper.plugin_system.get_plugin('mon_plugin')
# if plugin:
# #     instance = plugin(helper.client)
# #     instance.custom_investigation(params)
# # Fin de l'exemple
# ```
    def run(self, args=None):
        # Main entry point
        if args is None:
            parser = self.setup_parser()
            args = parser.parse_args()
        
        # Mettre à jour la configuration
        self.config.port = args.port
        self.config.protocol = args.protocol
        self.config.api_key = args.api_key
        self.config.timeout = args.timeout
        self.config.verify_ssl = not args.no_ssl_verify
        
        # Exécuter le mode approprié
        if args.mode == 'client':
            self.run_client_mode(args)
        elif args.mode == 'batch':
            self.run_batch_mode(args)
        elif args.mode == 'investigate':
            self.run_investigate_mode(args)
        elif args.mode == 'debug':
            self.run_debug_mode(args)
        elif args.mode == 'help':
            self.run_help_mode(args)
        else:
            print("❌ Mode inconnu. Utilisez 'help' pour l'aide.")
            self.run_help_mode(args)


def main():
    # Main entry point
    cli = ComfyUIHelperCLI()
    parser = cli.setup_parser()
    args = parser.parse_args()
    cli.run(args)


if __name__ == "__main__":
    main()