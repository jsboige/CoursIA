#!/usr/bin/env python3
"""
docker_manager.py - Gestionnaire Infrastructure Docker GenAI (v2)

Services geres:
- comfyui-qwen : Edition d'images Qwen VL (port 8188)
- forge-turbo  : Stable Diffusion WebUI Forge (port 17861, API avec Gradio auth)
- vllm-zimage  : Z-Image Turbo via vLLM Omni (port 8001)

Usage:
    python docker_manager.py status
    python docker_manager.py start comfyui-qwen
    python docker_manager.py restart forge-turbo
    python docker_manager.py test
    python docker_manager.py logs vllm-zimage

Auteur: Consolidation Fevrier 2026
"""

import os
import sys
import json
import time
import argparse
import subprocess
import logging
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple

try:
    import requests
except ImportError:
    print("Installing requests...")
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "requests"])
    import requests

# Configuration logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger("DockerManager")

# Chemins
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent.parent
DOCKER_CONFIG_DIR = PROJECT_ROOT / "docker-configurations"
SERVICES_DIR = DOCKER_CONFIG_DIR / "services"
GENAI_DIR = PROJECT_ROOT / "MyIA.AI.Notebooks" / "GenAI"
ENV_FILE = GENAI_DIR / ".env"

# Services connus
SERVICES = {
    "comfyui-qwen": {
        "compose_dir": SERVICES_DIR / "comfyui-qwen",
        "container_name": "comfyui-qwen",
        "port": 8188,
        "health_endpoint": "/system_stats",
        "auth_type": "bearer",
        "auth_env_var": "COMFYUI_API_TOKEN",
        "gpu_id": 0,
        "vram_required": "20GB+",
        "remote_url": "https://qwen-image-edit.myia.io"
    },
    "forge-turbo": {
        "compose_dir": SERVICES_DIR / "forge-turbo",
        "container_name": "forge-turbo",
        "port": 17861,  # API port (pas 1111 qui est ServicePortal)
        "health_endpoint": "/sdapi/v1/options",
        "auth_type": "basic",
        "auth_env_vars": ["FORGE_USER", "FORGE_PASSWORD"],
        "gpu_id": 1,
        "vram_required": "8GB+",
        "remote_url": "https://turbo.stable-diffusion-webui-forge.myia.io"
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
        "generation_endpoint": "/v1/images/generations"
    }
}


def load_env() -> Dict[str, str]:
    """Charge les variables d'environnement depuis .env"""
    env_vars = {}
    if ENV_FILE.exists():
        with open(ENV_FILE, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    env_vars[key.strip()] = value.strip().strip('"').strip("'")
    return env_vars


def run_cmd(cmd: List[str], cwd: Path = None, capture: bool = True, timeout: int = 60) -> subprocess.CompletedProcess:
    """Execute une commande shell"""
    try:
        result = subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            capture_output=capture,
            text=True,
            encoding='utf-8',
            errors='replace',
            timeout=timeout
        )
        return result
    except subprocess.TimeoutExpired:
        logger.error(f"Timeout executing: {' '.join(cmd)}")
        return subprocess.CompletedProcess(cmd, 1, "", "Timeout")
    except Exception as e:
        logger.error(f"Error executing command: {e}")
        return subprocess.CompletedProcess(cmd, 1, "", str(e))


def get_docker_compose_cmd() -> List[str]:
    """Retourne la commande docker compose appropriee"""
    result = run_cmd(["docker", "compose", "version"])
    if result.returncode == 0:
        return ["docker", "compose"]
    return ["docker-compose"]


COMPOSE_CMD = get_docker_compose_cmd()


class DockerManager:
    """Gestionnaire des services Docker GenAI"""

    def __init__(self):
        self.env = load_env()

    def get_container_status(self, service_name: str) -> Dict[str, Any]:
        """Retourne le statut d'un conteneur"""
        if service_name not in SERVICES:
            return {"status": "unknown", "running": False, "error": "Service inconnu"}

        svc = SERVICES[service_name]
        result = run_cmd(["docker", "inspect", svc["container_name"]])

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

    def check_service_health(self, service_name: str, use_remote: bool = False) -> Tuple[bool, str]:
        """Verifie la sante HTTP d'un service"""
        if service_name not in SERVICES:
            return False, "Service inconnu"

        svc = SERVICES[service_name]

        if use_remote:
            base_url = svc["remote_url"]
        else:
            base_url = f"http://localhost:{svc['port']}"

        url = f"{base_url}{svc['health_endpoint']}"

        # Configurer l'authentification
        headers = {}
        auth = None

        if svc.get("auth_type") == "bearer":
            token = self.env.get(svc["auth_env_var"], "")
            if token:
                headers["Authorization"] = f"Bearer {token}"
        elif svc.get("auth_type") == "basic":
            user = self.env.get(svc["auth_env_vars"][0], "admin")
            password = self.env.get(svc["auth_env_vars"][1], "changeme")
            auth = (user, password)

        try:
            resp = requests.get(url, headers=headers, auth=auth, timeout=10)
            if resp.status_code == 200:
                return True, f"OK ({resp.status_code})"
            elif resp.status_code == 401:
                return False, f"Auth required ({resp.status_code})"
            else:
                return False, f"HTTP {resp.status_code}"
        except requests.exceptions.ConnectionError:
            return False, "Connection refused"
        except requests.exceptions.Timeout:
            return False, "Timeout"
        except Exception as e:
            return False, str(e)

    def start_service(self, service_name: str, build: bool = False) -> bool:
        """Demarre un service"""
        if service_name not in SERVICES:
            logger.error(f"Service inconnu: {service_name}")
            return False

        svc = SERVICES[service_name]
        compose_dir = svc["compose_dir"]

        if not compose_dir.exists():
            logger.error(f"Repertoire non trouve: {compose_dir}")
            return False

        logger.info(f"Demarrage de {service_name}...")

        cmd = COMPOSE_CMD + ["up", "-d"]
        if build:
            cmd.append("--build")

        result = run_cmd(cmd, cwd=compose_dir, capture=False, timeout=300)

        if result.returncode == 0:
            logger.info(f"{service_name} demarre")
            return True
        else:
            logger.error(f"Echec demarrage {service_name}")
            return False

    def stop_service(self, service_name: str) -> bool:
        """Arrete un service"""
        if service_name not in SERVICES:
            return False

        svc = SERVICES[service_name]
        logger.info(f"Arret de {service_name}...")

        result = run_cmd(COMPOSE_CMD + ["down"], cwd=svc["compose_dir"], capture=False, timeout=60)
        return result.returncode == 0

    def restart_service(self, service_name: str) -> bool:
        """Redemarre un service"""
        logger.info(f"Redemarrage de {service_name}...")
        self.stop_service(service_name)
        time.sleep(3)
        return self.start_service(service_name)

    def get_logs(self, service_name: str, tail: int = 50) -> str:
        """Recupere les logs d'un service"""
        if service_name not in SERVICES:
            return "Service inconnu"

        svc = SERVICES[service_name]
        result = run_cmd(["docker", "logs", "--tail", str(tail), svc["container_name"]])
        return result.stdout + result.stderr

    def check_gpu(self) -> Dict[str, Any]:
        """Verifie l'etat des GPUs"""
        result = run_cmd([
            "nvidia-smi",
            "--query-gpu=index,name,memory.total,memory.free,memory.used,utilization.gpu",
            "--format=csv,noheader,nounits"
        ])

        if result.returncode != 0:
            return {"available": False, "error": "nvidia-smi not found"}

        gpus = []
        for line in result.stdout.strip().split('\n'):
            if line:
                parts = [p.strip() for p in line.split(',')]
                if len(parts) >= 6:
                    gpus.append({
                        "index": int(parts[0]),
                        "name": parts[1],
                        "memory_total_mb": int(parts[2]),
                        "memory_free_mb": int(parts[3]),
                        "memory_used_mb": int(parts[4]),
                        "utilization_pct": int(parts[5])
                    })

        return {"available": True, "count": len(gpus), "gpus": gpus}

    def print_status(self, include_remote: bool = False):
        """Affiche le statut de tous les services"""
        print("\n" + "=" * 70)
        print("  STATUT DES SERVICES GENAI")
        print("=" * 70)

        for name, svc in SERVICES.items():
            container_status = self.get_container_status(name)
            is_running = container_status.get("running", False)

            # Test local
            local_ok, local_msg = self.check_service_health(name, use_remote=False)

            # Icones
            run_icon = "UP" if is_running else "DOWN"
            health_icon = "OK" if local_ok else "X"

            print(f"\n{name}")
            print(f"  Container : [{run_icon}] {container_status.get('status', 'unknown')}")
            print(f"  Local API : [{health_icon}] http://localhost:{svc['port']} - {local_msg}")
            print(f"  GPU       : {svc['gpu_id']} ({svc['vram_required']})")

            if include_remote:
                remote_ok, remote_msg = self.check_service_health(name, use_remote=True)
                remote_icon = "OK" if remote_ok else "X"
                print(f"  Remote    : [{remote_icon}] {svc['remote_url']} - {remote_msg}")

        # GPU Status
        print("\n" + "-" * 70)
        print("  GPUS")
        print("-" * 70)

        gpu_info = self.check_gpu()
        if gpu_info["available"]:
            for gpu in gpu_info["gpus"]:
                used_pct = gpu["memory_used_mb"] * 100 // gpu["memory_total_mb"]
                print(f"  [{gpu['index']}] {gpu['name']}")
                print(f"      VRAM: {gpu['memory_used_mb']}MB / {gpu['memory_total_mb']}MB ({used_pct}%)")
                print(f"      Util: {gpu['utilization_pct']}%")
        else:
            print(f"  GPU non disponible: {gpu_info.get('error')}")

        print("\n" + "=" * 70)

    def test_all_services(self, include_remote: bool = False):
        """Teste tous les services"""
        print("\n" + "=" * 70)
        print("  TEST DES SERVICES")
        print("=" * 70)

        results = {}

        for name in SERVICES:
            print(f"\nTest {name}...")

            # Local
            local_ok, local_msg = self.check_service_health(name, use_remote=False)
            print(f"  Local  : {'PASS' if local_ok else 'FAIL'} - {local_msg}")
            results[f"{name}_local"] = local_ok

            if include_remote:
                remote_ok, remote_msg = self.check_service_health(name, use_remote=True)
                print(f"  Remote : {'PASS' if remote_ok else 'FAIL'} - {remote_msg}")
                results[f"{name}_remote"] = remote_ok

        # Resume
        total = len(results)
        passed = sum(1 for v in results.values() if v)
        print(f"\n{'=' * 70}")
        print(f"  RESULTAT: {passed}/{total} tests passes")
        print("=" * 70)

        return all(results.values())


def main():
    parser = argparse.ArgumentParser(description="GenAI Docker Manager v2")
    subparsers = parser.add_subparsers(dest='command', help='Commandes')

    # status
    cmd_status = subparsers.add_parser('status', help='Afficher le statut')
    cmd_status.add_argument('--remote', action='store_true', help='Inclure test services remote')

    # start
    cmd_start = subparsers.add_parser('start', help='Demarrer un service')
    cmd_start.add_argument('service', choices=list(SERVICES.keys()) + ['all'], help='Service a demarrer')
    cmd_start.add_argument('--build', action='store_true', help='Rebuild image')

    # stop
    cmd_stop = subparsers.add_parser('stop', help='Arreter un service')
    cmd_stop.add_argument('service', choices=list(SERVICES.keys()) + ['all'], help='Service a arreter')

    # restart
    cmd_restart = subparsers.add_parser('restart', help='Redemarrer un service')
    cmd_restart.add_argument('service', choices=list(SERVICES.keys()) + ['all'], help='Service a redemarrer')

    # logs
    cmd_logs = subparsers.add_parser('logs', help='Afficher les logs')
    cmd_logs.add_argument('service', choices=list(SERVICES.keys()), help='Service')
    cmd_logs.add_argument('--tail', type=int, default=50, help='Nombre de lignes')

    # test
    cmd_test = subparsers.add_parser('test', help='Tester les services')
    cmd_test.add_argument('--remote', action='store_true', help='Inclure services remote')

    args = parser.parse_args()
    manager = DockerManager()

    if args.command == 'status':
        manager.print_status(include_remote=args.remote)

    elif args.command == 'start':
        if args.service == 'all':
            for svc in SERVICES:
                manager.start_service(svc, build=args.build)
        else:
            manager.start_service(args.service, build=args.build)

    elif args.command == 'stop':
        if args.service == 'all':
            for svc in SERVICES:
                manager.stop_service(svc)
        else:
            manager.stop_service(args.service)

    elif args.command == 'restart':
        if args.service == 'all':
            for svc in SERVICES:
                manager.restart_service(svc)
        else:
            manager.restart_service(args.service)

    elif args.command == 'logs':
        print(manager.get_logs(args.service, args.tail))

    elif args.command == 'test':
        success = manager.test_all_services(include_remote=args.remote)
        sys.exit(0 if success else 1)

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
