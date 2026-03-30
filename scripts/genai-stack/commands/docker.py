#!/usr/bin/env python3
"""
commands/docker.py - Gestion des services Docker GenAI

Sous-commandes :
    genai.py docker status [--remote]
    genai.py docker start <service|all> [--build]
    genai.py docker stop <service|all>
    genai.py docker restart <service|all>
    genai.py docker logs <service> [--tail N]
    genai.py docker test [--remote]
"""

import sys
import json
import time
import subprocess
import logging
from pathlib import Path
from typing import Dict, List, Any, Tuple

try:
    import requests
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "requests"])
    import requests

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import SERVICES, load_env

logger = logging.getLogger("DockerManager")


def _run_cmd(cmd: List[str], cwd: Path = None, capture: bool = True, timeout: int = 60) -> subprocess.CompletedProcess:
    """Execute une commande shell."""
    try:
        result = subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            capture_output=capture,
            text=True,
            encoding='utf-8',
            errors='replace',
            timeout=timeout,
        )
        return result
    except subprocess.TimeoutExpired:
        logger.error(f"Timeout: {' '.join(cmd)}")
        return subprocess.CompletedProcess(cmd, 1, "", "Timeout")
    except Exception as e:
        logger.error(f"Erreur commande: {e}")
        return subprocess.CompletedProcess(cmd, 1, "", str(e))


def _get_compose_cmd() -> List[str]:
    """Retourne la commande docker compose appropriee."""
    result = _run_cmd(["docker", "compose", "version"])
    if result.returncode == 0:
        return ["docker", "compose"]
    return ["docker-compose"]


COMPOSE_CMD = _get_compose_cmd()


class DockerManager:
    """Gestionnaire des services Docker GenAI."""

    def __init__(self):
        self.env = load_env()

    def get_container_status(self, service_name: str) -> Dict[str, Any]:
        """Retourne le statut d'un conteneur."""
        if service_name not in SERVICES:
            return {"status": "unknown", "running": False, "error": "Service inconnu"}

        svc = SERVICES[service_name]
        result = _run_cmd(["docker", "inspect", svc["container_name"]])

        if result.returncode != 0:
            return {"status": "not_found", "running": False}

        try:
            data = json.loads(result.stdout)[0]
            state = data.get("State", {})
            return {
                "status": state.get("Status", "unknown"),
                "running": state.get("Running", False),
                "started_at": state.get("StartedAt"),
                "health": state.get("Health", {}).get("Status", "unknown"),
            }
        except Exception:
            return {"status": "error", "running": False}

    def check_service_health(self, service_name: str, use_remote: bool = False) -> Tuple[bool, str]:
        """Verifie la sante HTTP d'un service."""
        if service_name not in SERVICES:
            return False, "Service inconnu"

        svc = SERVICES[service_name]
        base_url = svc["remote_url"] if use_remote else f"http://localhost:{svc['port']}"
        url = f"{base_url}{svc['health_endpoint']}"

        headers = {}
        auth = None
        if svc.get("auth_type") == "bearer":
            token = self.env.get(svc.get("auth_env_var", ""), "")
            if token:
                headers["Authorization"] = f"Bearer {token}"
        elif svc.get("auth_type") == "basic":
            user = self.env.get(svc.get("auth_env_vars", ["", ""])[0], "admin")
            password = self.env.get(svc.get("auth_env_vars", ["", ""])[1], "changeme")
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
        """Demarre un service."""
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

        result = _run_cmd(cmd, cwd=compose_dir, capture=False, timeout=300)
        if result.returncode == 0:
            logger.info(f"{service_name} demarre")
            return True
        logger.error(f"Echec demarrage {service_name}")
        return False

    def stop_service(self, service_name: str) -> bool:
        """Arrete un service."""
        if service_name not in SERVICES:
            return False
        svc = SERVICES[service_name]
        logger.info(f"Arret de {service_name}...")
        result = _run_cmd(COMPOSE_CMD + ["down"], cwd=svc["compose_dir"], capture=False, timeout=60)
        return result.returncode == 0

    def restart_service(self, service_name: str) -> bool:
        """Redemarre un service."""
        logger.info(f"Redemarrage de {service_name}...")
        self.stop_service(service_name)
        time.sleep(3)
        return self.start_service(service_name)

    def get_logs(self, service_name: str, tail: int = 50) -> str:
        """Recupere les logs d'un service."""
        if service_name not in SERVICES:
            return "Service inconnu"
        svc = SERVICES[service_name]
        result = _run_cmd(["docker", "logs", "--tail", str(tail), svc["container_name"]])
        return result.stdout + result.stderr

    def check_gpu(self) -> Dict[str, Any]:
        """Verifie l'etat des GPUs."""
        result = _run_cmd([
            "nvidia-smi",
            "--query-gpu=index,name,memory.total,memory.free,memory.used,utilization.gpu",
            "--format=csv,noheader,nounits",
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
                        "utilization_pct": int(parts[5]),
                    })
        return {"available": True, "count": len(gpus), "gpus": gpus}

    def print_status(self, include_remote: bool = False):
        """Affiche le statut de tous les services."""
        print("\n" + "=" * 70)
        print("  STATUT DES SERVICES GENAI")
        print("=" * 70)

        for name, svc in SERVICES.items():
            container_status = self.get_container_status(name)
            is_running = container_status.get("running", False)
            local_ok, local_msg = self.check_service_health(name, use_remote=False)

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

    def test_all_services(self, include_remote: bool = False) -> bool:
        """Teste tous les services."""
        print("\n" + "=" * 70)
        print("  TEST DES SERVICES")
        print("=" * 70)

        results = {}
        for name in SERVICES:
            print(f"\nTest {name}...")
            local_ok, local_msg = self.check_service_health(name, use_remote=False)
            print(f"  Local  : {'PASS' if local_ok else 'FAIL'} - {local_msg}")
            results[f"{name}_local"] = local_ok

            if include_remote:
                remote_ok, remote_msg = self.check_service_health(name, use_remote=True)
                print(f"  Remote : {'PASS' if remote_ok else 'FAIL'} - {remote_msg}")
                results[f"{name}_remote"] = remote_ok

        total = len(results)
        passed = sum(1 for v in results.values() if v)
        print(f"\n{'=' * 70}")
        print(f"  RESULTAT: {passed}/{total} tests passes")
        print("=" * 70)
        return all(results.values())


# --- CLI ---

def register(subparsers):
    """Enregistre la sous-commande docker."""
    parser = subparsers.add_parser('docker', help='Gestion services Docker')
    sub = parser.add_subparsers(dest='docker_action')

    p_status = sub.add_parser('status', help='Afficher le statut')
    p_status.add_argument('--remote', action='store_true')

    p_start = sub.add_parser('start', help='Demarrer un service')
    p_start.add_argument('service', choices=list(SERVICES.keys()) + ['all'])
    p_start.add_argument('--build', action='store_true')

    p_stop = sub.add_parser('stop', help='Arreter un service')
    p_stop.add_argument('service', choices=list(SERVICES.keys()) + ['all'])

    p_restart = sub.add_parser('restart', help='Redemarrer un service')
    p_restart.add_argument('service', choices=list(SERVICES.keys()) + ['all'])

    p_logs = sub.add_parser('logs', help='Afficher les logs')
    p_logs.add_argument('service', choices=list(SERVICES.keys()))
    p_logs.add_argument('--tail', type=int, default=50)

    p_test = sub.add_parser('test', help='Tester les services')
    p_test.add_argument('--remote', action='store_true')


def execute(args) -> int:
    """Execute la commande docker."""
    manager = DockerManager()
    action = getattr(args, 'docker_action', None)

    if action == 'status':
        manager.print_status(include_remote=args.remote)
        return 0

    elif action == 'start':
        if args.service == 'all':
            results = [manager.start_service(s, build=args.build) for s in SERVICES]
            return 0 if all(results) else 1
        return 0 if manager.start_service(args.service, build=args.build) else 1

    elif action == 'stop':
        if args.service == 'all':
            results = [manager.stop_service(s) for s in SERVICES]
            return 0 if all(results) else 1
        return 0 if manager.stop_service(args.service) else 1

    elif action == 'restart':
        if args.service == 'all':
            results = [manager.restart_service(s) for s in SERVICES]
            return 0 if all(results) else 1
        return 0 if manager.restart_service(args.service) else 1

    elif action == 'logs':
        print(manager.get_logs(args.service, args.tail))
        return 0

    elif action == 'test':
        ok = manager.test_all_services(include_remote=args.remote)
        return 0 if ok else 1

    else:
        manager.print_status()
        return 0


def main():
    """Point d'entree standalone (retrocompatibilite docker_manager.py)."""
    import argparse
    logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
    parser = argparse.ArgumentParser(description="GenAI Docker Manager")
    sub = parser.add_subparsers(dest='docker_action')

    p_status = sub.add_parser('status')
    p_status.add_argument('--remote', action='store_true')

    p_start = sub.add_parser('start')
    p_start.add_argument('service', choices=list(SERVICES.keys()) + ['all'])
    p_start.add_argument('--build', action='store_true')

    p_stop = sub.add_parser('stop')
    p_stop.add_argument('service', choices=list(SERVICES.keys()) + ['all'])

    p_restart = sub.add_parser('restart')
    p_restart.add_argument('service', choices=list(SERVICES.keys()) + ['all'])

    p_logs = sub.add_parser('logs')
    p_logs.add_argument('service', choices=list(SERVICES.keys()))
    p_logs.add_argument('--tail', type=int, default=50)

    p_test = sub.add_parser('test')
    p_test.add_argument('--remote', action='store_true')

    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
