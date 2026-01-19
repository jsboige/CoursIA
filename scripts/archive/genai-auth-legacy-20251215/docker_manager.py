#!/usr/bin/env python3
"""
docker_manager.py - Gestionnaire Centralisé de l'Infrastructure Docker

Ce module consolide toutes les opérations liées aux conteneurs GenAI :
- Cycle de vie : Démarrage, Arrêt, Redémarrage
- Infrastructure : Vérification GPU/CUDA, Volumes, Réseaux
- Santé : Healthchecks, Monitoring Ressources, Logs
- Maintenance : Prune, Rebuild, Updates, Sync Credentials, Model Downloads

Auteur: Consolidation Phase 36
Date: 2025-12-12
"""

import os
import sys
import json
import time
import shutil
import logging
import argparse
import subprocess
import requests
import tempfile
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple
from datetime import datetime

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger("DockerManager")

# Constantes
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
DOCKER_CONFIG_DIR = PROJECT_ROOT / "docker-configurations"
SERVICES_DIR = DOCKER_CONFIG_DIR / "services"
SECRETS_DIR = PROJECT_ROOT / ".secrets"
CONFIG_FILE = PROJECT_ROOT / "scripts/genai-auth/config/models_config.json"

# Mapping des services connus
KNOWN_SERVICES = {
    "comfyui-qwen": {
        "compose_path": SERVICES_DIR / "comfyui-qwen",
        "container_name": "comfyui-qwen",
        "port": 8188
    },
    "forge-turbo": {
        "compose_path": SERVICES_DIR / "forge-turbo",
        "container_name": "forge-turbo",
        "port": 7865
    }
}

class DockerManager:
    """Gestionnaire unifié pour l'infrastructure Docker GenAI"""
    
    def __init__(self):
        self.docker_cmd = self._detect_docker_command()
        self.config = self._load_config()
        
    def _detect_docker_command(self) -> str:
        """Détecte la commande docker disponible (docker vs podman)"""
        try:
            subprocess.run(["docker", "--version"], check=True, capture_output=True)
            return "docker"
        except (subprocess.CalledProcessError, FileNotFoundError):
            logger.error("Docker n'est pas installé ou n'est pas dans le PATH.")
            raise RuntimeError("Docker required")

    def _load_config(self) -> Dict:
        """Charge la configuration des modèles et nodes"""
        if not CONFIG_FILE.exists():
            logger.warning(f"Fichier de configuration non trouvé: {CONFIG_FILE}")
            return {}
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"Erreur chargement config: {e}")
            return {}

    def _run_cmd(self, cmd: List[str], cwd: Path = None, capture: bool = True) -> subprocess.CompletedProcess:
        """Exécute une commande shell de manière sécurisée"""
        try:
            cwd_str = str(cwd) if cwd else None
            logger.debug(f"Running: {' '.join(cmd)} in {cwd_str or '.'}")
            
            result = subprocess.run(
                cmd,
                cwd=cwd_str,
                check=False,
                capture_output=capture,
                text=True,
                encoding='utf-8',
                errors='replace'
            )
            return result
        except Exception as e:
            logger.error(f"Erreur exécution commande: {e}")
            raise

    # =========================================================================
    # 1. CYCLE DE VIE (Start/Stop/Restart)
    # =========================================================================

    def start_service(self, service_name: str, build: bool = False, detach: bool = True) -> bool:
        """Démarre un service défini"""
        if service_name not in KNOWN_SERVICES:
            logger.error(f"Service inconnu: {service_name}")
            return False
            
        service_info = KNOWN_SERVICES[service_name]
        compose_dir = service_info["compose_path"]
        
        if not compose_dir.exists():
            logger.error(f"Répertoire compose introuvable: {compose_dir}")
            return False
            
        logger.info(f"🚀 Démarrage du service {service_name}...")
        
        cmd = [self.docker_cmd, "compose", "up"]
        if detach:
            cmd.append("-d")
        if build:
            cmd.append("--build")
            
        result = self._run_cmd(cmd, cwd=compose_dir, capture=False)
        
        if result.returncode == 0:
            logger.info(f"✅ Service {service_name} démarré.")
            return True
        else:
            logger.error(f"❌ Échec du démarrage de {service_name}.")
            return False

    def stop_service(self, service_name: str) -> bool:
        """Arrête un service défini"""
        if service_name not in KNOWN_SERVICES:
            return False
            
        service_info = KNOWN_SERVICES[service_name]
        logger.info(f"🛑 Arrêt du service {service_name}...")
        
        cmd = [self.docker_cmd, "compose", "stop"]
        result = self._run_cmd(cmd, cwd=service_info["compose_path"], capture=False)
        
        return result.returncode == 0

    def restart_service(self, service_name: str) -> bool:
        """Redémarre un service"""
        logger.info(f"🔄 Redémarrage du service {service_name}...")
        if self.stop_service(service_name):
            time.sleep(2) # Pause de grâce
            return self.start_service(service_name)
        return False

    def get_container_status(self, container_name: str) -> Dict[str, Any]:
        """Récupère le statut détaillé d'un conteneur"""
        cmd = [self.docker_cmd, "inspect", container_name]
        result = self._run_cmd(cmd)
        
        if result.returncode != 0:
            return {"status": "not_found", "running": False}
            
        try:
            data = json.loads(result.stdout)[0]
            state = data.get("State", {})
            return {
                "status": state.get("Status", "unknown"),
                "running": state.get("Running", False),
                "started_at": state.get("StartedAt"),
                "health": state.get("Health", {}).get("Status", "unknown")
            }
        except Exception:
            return {"status": "error", "running": False}

    # =========================================================================
    # 2. INFRASTRUCTURE & SANTÉ
    # =========================================================================

    def check_gpu_availability(self) -> Dict[str, Any]:
        """Vérifie la disponibilité et l'état du GPU via nvidia-smi"""
        try:
            result = self._run_cmd(["nvidia-smi", "--query-gpu=name,memory.total,memory.free,utilization.gpu", "--format=csv,noheader"])
            
            if result.returncode == 0:
                gpus = []
                for line in result.stdout.strip().split('\n'):
                    parts = line.split(',')
                    if len(parts) >= 4:
                        gpus.append({
                            "name": parts[0].strip(),
                            "memory_total": parts[1].strip(),
                            "memory_free": parts[2].strip(),
                            "utilization": parts[3].strip()
                        })
                return {"available": True, "count": len(gpus), "details": gpus}
            else:
                return {"available": False, "error": "nvidia-smi returned non-zero exit code"}
        except FileNotFoundError:
            return {"available": False, "error": "nvidia-smi not found"}

    def check_container_health(self, service_name: str, auth_headers: Dict[str, str] = None) -> bool:
        """Vérifie la santé applicative (HTTP Check)"""
        if service_name not in KNOWN_SERVICES:
            return False
            
        info = KNOWN_SERVICES[service_name]
        url = f"http://localhost:{info['port']}"
        
        if "comfyui" in service_name:
            url += "/system_stats"
        elif "forge" in service_name:
            url += "/sdapi/v1/options"
            
        try:
            resp = requests.get(url, headers=auth_headers, timeout=5)
            if resp.status_code == 200:
                return True
            else:
                logger.warning(f"Health check failed for {service_name}: HTTP {resp.status_code}")
                return False
        except Exception as e:
            logger.debug(f"Health check exception for {service_name}: {e}")
            return False

    def get_container_logs(self, container_name: str, tail: int = 50) -> str:
        """Récupère les logs d'un conteneur"""
        cmd = [self.docker_cmd, "logs", "--tail", str(tail), container_name]
        result = self._run_cmd(cmd)
        return result.stdout if result.returncode == 0 else result.stderr

    # =========================================================================
    # 3. MAINTENANCE & UTILS
    # =========================================================================

    def prune_system(self, volumes: bool = False) -> bool:
        """Nettoie les ressources Docker inutilisées"""
        logger.warning("🧹 Nettoyage du système Docker...")
        cmd = [self.docker_cmd, "system", "prune", "-f"]
        if volumes:
            cmd.append("--volumes")
            
        result = self._run_cmd(cmd, capture=False)
        return result.returncode == 0

    def update_container_file(self, container_name: str, file_path: str, content: str) -> bool:
        """Met à jour un fichier DANS un conteneur en cours d'exécution."""
        try:
            with tempfile.NamedTemporaryFile(mode='w', delete=False, encoding='utf-8') as tmp:
                tmp.write(content)
                temp_path = tmp.name
                
            cmd_cp = [self.docker_cmd, "cp", temp_path, f"{container_name}:{file_path}"]
            res_cp = self._run_cmd(cmd_cp)
            
            os.unlink(temp_path)
                
            if res_cp.returncode != 0:
                logger.error(f"Erreur copie fichier: {res_cp.stderr}")
                return False
                
            return True
        except Exception as e:
            logger.error(f"Exception update_container_file: {e}")
            return False

    def sync_credentials(self, container_name: str) -> bool:
        """
        Synchronise les credentials (.env.generated, tokens) vers le conteneur.
        Chemin cible: /workspace/ComfyUI/.secrets/
        """
        logger.info(f"🔐 Synchronisation des credentials pour {container_name}...")
        
        files_to_sync = [
            SECRETS_DIR / "qwen-api-user.token",
            SECRETS_DIR / ".env.generated"
        ]
        
        # Créer le dossier .secrets dans le conteneur
        target_dir = "/workspace/ComfyUI/.secrets"
        mkdir_cmd = [self.docker_cmd, "exec", container_name, "mkdir", "-p", target_dir]
        if self._run_cmd(mkdir_cmd).returncode != 0:
            logger.error("❌ Impossible de créer le dossier .secrets dans le conteneur.")
            return False

        all_ok = True
        for src_file in files_to_sync:
            if not src_file.exists():
                logger.warning(f"⚠️ Fichier secret manquant: {src_file}")
                continue
                
            file_name = src_file.name
            target_path = f"{target_dir}/{file_name}"
            
            logger.info(f"Copie de {file_name} -> {container_name}:{target_path}")
            
            # Utiliser subprocess directement pour docker cp
            cp_cmd = [self.docker_cmd, "cp", str(src_file), f"{container_name}:{target_path}"]
            res = self._run_cmd(cp_cmd)
            
            if res.returncode != 0:
                logger.error(f"❌ Échec copie {file_name}: {res.stderr}")
                all_ok = False
            else:
                # Fixer les permissions (600)
                chmod_cmd = [self.docker_cmd, "exec", container_name, "chmod", "600", target_path]
                self._run_cmd(chmod_cmd)
        
        if all_ok:
            logger.info("✅ Credentials synchronisés.")
        return all_ok

    def setup_infrastructure(self, container_name: str = "comfyui-qwen") -> bool:
        """
        Initialise l'infrastructure du conteneur (installation des nodes manquants et modèles).
        """
        logger.info(f"🔧 Initialisation de l'infrastructure pour {container_name}...")
        
        if not self.config:
            logger.error("❌ Configuration manquante.")
            return False
            
        # 0. Sync Credentials (CRITIQUE pour l'accès aux modèles et API)
        if not self.sync_credentials(container_name):
            logger.warning("⚠️ Problème synchronisation credentials. L'installation peut échouer.")

        # 1. Installation des dépendances de base ComfyUI
        logger.info("📦 Vérification des dépendances de base ComfyUI...")
        base_reqs = "/workspace/ComfyUI/requirements.txt"
        cmd_reqs = [self.docker_cmd, "exec", container_name, "pip", "install", "-r", base_reqs]
        self._run_cmd(cmd_reqs) # On ignore l'erreur si pip fail, on continue

        # 2. Installation de l'Authentification (Script Core)
        logger.info("🔐 Installation/Vérification de ComfyUI-Login...")
        auth_script = PROJECT_ROOT / "scripts/genai-auth/core/install_comfyui_with_auth.py"
        if auth_script.exists():
            try:
                # On utilise le même interpréteur Python
                res_auth = subprocess.run([sys.executable, str(auth_script)], capture_output=True, text=True, timeout=600)
                if res_auth.returncode == 0:
                    logger.info("✅ Authentification installée avec succès.")
                else:
                    logger.error(f"❌ Erreur installation Auth: {res_auth.stderr}")
                    # On ne bloque pas forcément tout si l'auth échoue mais c'est grave
            except Exception as e:
                logger.error(f"❌ Exception lors de l'appel au script d'auth: {e}")
        else:
            logger.warning(f"⚠️ Script d'installation auth introuvable: {auth_script}")

        # 3. Installation des Custom Nodes
        custom_nodes = self.config.get("custom_nodes", {}).get("critical", [])
        nodes_success = True
        if custom_nodes:
            logger.info("📦 Installation des Custom Nodes critiques...")
            for node in custom_nodes:
                logger.info(f"Traitement de {node['name']}...")
                if not self.install_custom_node_git(container_name, node['url'], node.get('install_deps', True)):
                    logger.error(f"❌ Échec installation {node['name']}")
                    nodes_success = False
                else:
                    logger.info(f"✅ {node['name']} prêt.")
        
        # 4. Téléchargement des Modèles
        models_success = self.download_models(container_name)
        
        success = nodes_success and models_success

        if success:
            logger.info("♻️ Redémarrage du conteneur pour prise en compte...")
            self.restart_service(container_name.replace("comfyui-qwen", "comfyui-qwen")) # Hack: service name ~ container name
            if self.wait_for_service(container_name.replace("comfyui-qwen", "comfyui-qwen")):
                
                # 4. Validation finale
                logger.info("🔍 Validation de l'installation...")
                val_res = self.validate_installation(container_name)
                if val_res["status"] == "success":
                    logger.info("✅ Service opérationnel et validé après setup.")
                else:
                    logger.warning(f"⚠️ Service démarré mais validation partielle: {val_res['message']}")
            else:
                logger.error("❌ Le service ne répond pas après le redémarrage.")
                success = False
            
        return success

    def wait_for_service(self, service_name: str, timeout: int = 60) -> bool:
        """Attend que le service soit accessible (HTTP 200/401/403)"""
        logger.info(f"⏳ Attente de disponibilité pour {service_name} ({timeout}s)...")
        start_time = time.time()
        
        # Récupérer token pour auth
        token = None
        token_file = SECRETS_DIR / "qwen-api-user.token"
        if token_file.exists():
            token = token_file.read_text().strip()
            
        headers = {"Authorization": f"Bearer {token}"} if token else None
        
        while time.time() - start_time < timeout:
            if self.check_container_health(service_name, headers):
                return True
            time.sleep(2)
            
        logger.error(f"❌ Timeout attente service {service_name}")
        return False

    def download_models(self, container_name: str) -> bool:
        """Télécharge les modèles requis (HuggingFace -> Host -> Container)"""
        qwen_models = self.config.get("qwen_models", {})
        if not qwen_models:
            return True
            
        logger.info("📥 Vérification des modèles...")
        
        # Vérifier token HF
        token_file = SECRETS_DIR / ".env.huggingface"
        token = None
        if token_file.exists():
            content = token_file.read_text(encoding='utf-8').strip()
            token = content.split("=", 1)[1].strip() if "=" in content else content
            
        try:
            from huggingface_hub import hf_hub_download
        except ImportError:
            logger.warning("⚠️ huggingface_hub non installé. Tentative d'installation...")
            subprocess.run([sys.executable, "-m", "pip", "install", "huggingface_hub"], check=False)
            try:
                from huggingface_hub import hf_hub_download
            except ImportError:
                logger.error("❌ Impossible d'utiliser huggingface_hub. Skip téléchargement.")
                return False

        all_ok = True
        temp_dir = PROJECT_ROOT / "temp_qwen_download"
        temp_dir.mkdir(exist_ok=True)

        for model_key, model_info in qwen_models.items():
            try:
                # Vérifier présence dans conteneur
                target_path = f"{model_info['container_dir']}{model_info['name']}"
                check_cmd = [self.docker_cmd, "exec", container_name, "test", "-f", target_path]
                if self._run_cmd(check_cmd).returncode == 0:
                    logger.info(f"✅ {model_info['name']} déjà présent.")
                    continue
                    
                logger.info(f"Téléchargement {model_info['name']} ({model_info['size_gb']} GB)...")
                
                local_file = hf_hub_download(
                    repo_id=model_info["repo"],
                    filename=model_info["filename"],
                    token=token,
                    local_dir=str(temp_dir),
                    local_dir_use_symlinks=False
                )
                
                # Copie vers conteneur
                logger.info(f"Transfert vers {container_name}:{target_path}...")
                
                # S'assurer que le dossier cible existe
                dir_cmd = [self.docker_cmd, "exec", container_name, "mkdir", "-p", str(Path(target_path).parent).replace("\\", "/")]
                self._run_cmd(dir_cmd)
                
                copy_cmd = [self.docker_cmd, "cp", local_file, f"{container_name}:{target_path}"]
                if self._run_cmd(copy_cmd).returncode != 0:
                    logger.error(f"❌ Échec copie {model_info['name']}")
                    all_ok = False
                else:
                    logger.info(f"✅ {model_info['name']} installé.")
                    
            except Exception as e:
                logger.error(f"❌ Erreur modèle {model_key}: {e}")
                all_ok = False
                
        # Nettoyage temporaire
        if temp_dir.exists():
            shutil.rmtree(temp_dir, ignore_errors=True)
            
        return all_ok

    def install_custom_node_git(self, container_name: str, repo_url: str, install_deps: bool = True) -> bool:
        """
        Installe un custom node ComfyUI depuis un dépôt Git.
        """
        try:
            logger.info(f"Installation de {repo_url} dans {container_name}...")
            
            # Script d'installation interne (Python exécuté dans le conteneur)
            install_script = f"""
import os
import sys
import subprocess
from pathlib import Path

# Chemins internes au conteneur
CUSTOM_NODES_DIR = Path("/workspace/ComfyUI/custom_nodes")
REPO_URL = "{repo_url}"
REPO_NAME = REPO_URL.split("/")[-1].replace(".git", "")
TARGET_DIR = CUSTOM_NODES_DIR / REPO_NAME

def install():
    print(f"Installation dans {{TARGET_DIR}}...")
    
    # 1. Clone / Pull
    if not TARGET_DIR.exists():
        print("Clonage du dépôt...")
        subprocess.run(["git", "clone", REPO_URL, str(TARGET_DIR)], check=True)
    else:
        print("Dépôt déjà présent, mise à jour...")
        subprocess.run(["git", "-C", str(TARGET_DIR), "pull"], check=True)
        
    # 2. Install Deps
    if {str(install_deps)}:
        print("Installation des dépendances...")
        req_file = TARGET_DIR / "requirements.txt"
        if req_file.exists():
            subprocess.run([sys.executable, "-m", "pip", "install", "-r", str(req_file)], check=True)
        else:
            print("Pas de requirements.txt trouvé.")
    
    print("✅ Installation terminée")

if __name__ == "__main__":
    try:
        install()
    except Exception as e:
        print(f"❌ Erreur: {{e}}")
        sys.exit(1)
"""
            # Exécuter le script via update_container_file + exec
            temp_script_path = "/tmp/install_node.py"
            if not self.update_container_file(container_name, temp_script_path, install_script):
                return False
                
            cmd = [self.docker_cmd, "exec", container_name, "python3", temp_script_path]
            res = self._run_cmd(cmd)
            
            if res.returncode == 0:
                logger.info("✅ Installation réussie.")
                return True
            else:
                logger.error(f"❌ Échec installation: {res.stdout} {res.stderr}")
                return False
                
        except Exception as e:
            logger.error(f"Exception install_custom_node_git: {e}")
            return False

    def validate_installation(self, container_name: str) -> Dict[str, Any]:
        """Vérifie que les nodes critiques sont bien chargés par ComfyUI."""
        expected_nodes = self.config.get("validation_nodes", {}).get("expected_qwen_nodes", [])
        if not expected_nodes:
            return {"status": "skipped", "message": "Aucun node attendu configuré"}
            
        token_file = SECRETS_DIR / "qwen-api-user.token"
        if not token_file.exists():
            return {"status": "error", "message": "Token manquant pour validation"}
            
        token = token_file.read_text().strip()
        port = KNOWN_SERVICES[container_name]["port"]
        url = f"http://localhost:{port}/object_info"
        
        try:
            resp = requests.get(url, headers={"Authorization": f"Bearer {token}"}, timeout=10)
            if resp.status_code != 200:
                return {"status": "error", "message": f"API Error: {resp.status_code}"}
                
            loaded_nodes = resp.json().keys()
            found_count = 0
            missing = []
            
            for node in expected_nodes:
                if node in loaded_nodes:
                    found_count += 1
                else:
                    missing.append(node)
                    
            if len(missing) == 0:
                return {"status": "success", "message": f"Tous les {found_count} nodes trouvés"}
            else:
                return {
                    "status": "warning", 
                    "message": f"{found_count}/{len(expected_nodes)} nodes trouvés. Manquants: {len(missing)}",
                    "missing": missing
                }
                
        except Exception as e:
            return {"status": "error", "message": str(e)}

# =========================================================================
# CLI
# =========================================================================

def main():
    parser = argparse.ArgumentParser(description="GenAI Docker Infrastructure Manager")
    subparsers = parser.add_subparsers(dest='command', help='Commandes disponibles')
    
    # Start
    cmd_start = subparsers.add_parser('start', help='Démarrer un service')
    cmd_start.add_argument('service', choices=list(KNOWN_SERVICES.keys()), help='Nom du service')
    cmd_start.add_argument('--build', action='store_true', help='Reconstruire l\'image')
    
    # Stop
    cmd_stop = subparsers.add_parser('stop', help='Arrêter un service')
    cmd_stop.add_argument('service', choices=list(KNOWN_SERVICES.keys()), help='Nom du service')
    
    # Restart
    cmd_restart = subparsers.add_parser('restart', help='Redémarrer un service')
    cmd_restart.add_argument('service', choices=list(KNOWN_SERVICES.keys()), help='Nom du service')
    
    # Status
    cmd_status = subparsers.add_parser('status', help='Afficher le statut')
    cmd_status.add_argument('service', choices=list(KNOWN_SERVICES.keys()), nargs='?', help='Service spécifique (optionnel)')
    
    # Setup
    cmd_setup = subparsers.add_parser('setup', help='Installer/Réparer (Nodes + Modèles)')
    cmd_setup.add_argument('service', choices=list(KNOWN_SERVICES.keys()), nargs='?', default='comfyui-qwen', help='Service cible')

    # Logs
    cmd_logs = subparsers.add_parser('logs', help='Afficher les logs')
    cmd_logs.add_argument('service', choices=list(KNOWN_SERVICES.keys()), help='Nom du service')
    cmd_logs.add_argument('--tail', type=int, default=50, help='Nombre de lignes')
    
    # Prune
    cmd_prune = subparsers.add_parser('prune', help='Nettoyer Docker')
    cmd_prune.add_argument('--volumes', action='store_true', help='Supprimer aussi les volumes')
    
    # Sync
    cmd_sync = subparsers.add_parser('sync', help='Synchroniser Credentials')
    cmd_sync.add_argument('service', choices=list(KNOWN_SERVICES.keys()), default='comfyui-qwen', nargs='?', help='Service cible')

    # Validate
    cmd_val = subparsers.add_parser('validate', help='Valider installation nodes')
    cmd_val.add_argument('service', choices=list(KNOWN_SERVICES.keys()), default='comfyui-qwen', nargs='?', help='Service cible')

    args = parser.parse_args()
    manager = DockerManager()
    
    if args.command == 'start':
        manager.start_service(args.service, build=args.build)
        
    elif args.command == 'stop':
        manager.stop_service(args.service)
        
    elif args.command == 'restart':
        manager.restart_service(args.service)

    elif args.command == 'setup':
        manager.setup_infrastructure(args.service)
        
    elif args.command == 'sync':
        container_name = KNOWN_SERVICES[args.service]["container_name"]
        manager.sync_credentials(container_name)

    elif args.command == 'validate':
        container_name = KNOWN_SERVICES[args.service]["container_name"]
        res = manager.validate_installation(container_name)
        print(json.dumps(res, indent=2))
        
    elif args.command == 'status':
        if args.service:
            services = [args.service]
        else:
            services = list(KNOWN_SERVICES.keys())
            
        print("\n📊 STATUT DES SERVICES")
        print("="*60)
        for svc in services:
            info = KNOWN_SERVICES[svc]
            container_status = manager.get_container_status(info["container_name"])
            app_health = manager.check_container_health(svc)
            
            status_icon = "🟢" if container_status["running"] else "🔴"
            health_icon = "✅" if app_health else "⚠️" if container_status["running"] else "⚪"
            
            print(f"{status_icon} {svc:<20} | Docker: {container_status['status']:<15} | App: {health_icon}")
            
        # GPU Status
        print("\n🎮 STATUT GPU")
        print("-" * 60)
        gpu_info = manager.check_gpu_availability()
        if gpu_info["available"]:
            for gpu in gpu_info["details"]:
                print(f"✅ {gpu['name']} | VRAM: {gpu['memory_free']} / {gpu['memory_total']} | Util: {gpu['utilization']}")
        else:
            print(f"❌ GPU non disponible: {gpu_info.get('error')}")
            
    elif args.command == 'logs':
        info = KNOWN_SERVICES[args.service]
        print(manager.get_container_logs(info["container_name"], args.tail))
        
    elif args.command == 'prune':
        manager.prune_system(volumes=args.volumes)
        
    else:
        parser.print_help()

if __name__ == "__main__":
    main()