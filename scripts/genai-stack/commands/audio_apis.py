#!/usr/bin/env python3
"""
commands/audio_apis.py - Gestion des containers d'APIs Audio

Sous-commandes:
    genai.py audio-apis status           # Statut de tous les services audio
    genai.py audio-apis start <service>  # Demarrer un service (avec gestion GPU)
    genai.py audio-apis stop <service>   # Arreter un service
    genai.py audio-apis switch <service> # Switch GPU: stop autres, start service
    genai.py audio-apis test <service>   # Tester un service (health + endpoint)
    genai.py audio-apis build <service>  # Construire l'image Docker
    genai.py audio-apis logs <service>   # Voir les logs

Services disponibles: whisper-api, tts-api, musicgen-api, demucs-api
"""

import subprocess
import sys
import time
import json
import logging
from pathlib import Path
from typing import Dict, List, Optional, Tuple

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import SERVICES, SERVICES_DIR

logger = logging.getLogger("AudioAPIs")

# Services audio API
AUDIO_API_SERVICES = ["whisper-api", "tts-api", "musicgen-api", "demucs-api", "funasr-api"]

# GPU allocation map
GPU_ALLOCATION = {
    "whisper-api": 0,   # RTX 3080 Ti (16GB)
    "demucs-api": 0,    # RTX 3080 Ti (16GB)
    "tts-api": 1,       # RTX 3090 (24GB)
    "musicgen-api": 1,  # RTX 3090 (24GB)
}

# Conflits GPU (services sur le meme GPU)
GPU_CONFLICTS = {
    0: ["comfyui-qwen", "comfyui-video", "whisper-webui", "vllm-zimage", "whisper-api", "demucs-api"],
    1: ["forge-turbo", "tts-api", "musicgen-api"],
}


def get_container_status(container_name: str) -> str:
    """Retourne le statut d'un container Docker."""
    result = subprocess.run(
        ["docker", "inspect", container_name, "--format", "{{.State.Status}}"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return "not_found"
    return result.stdout.strip()


def get_all_audio_status() -> Dict[str, Dict]:
    """Retourne le statut de tous les services audio API."""
    status = {}
    for svc in AUDIO_API_SERVICES:
        if svc not in SERVICES:
            status[svc] = {"status": "not_configured", "error": "Service non configure"}
            continue

        cfg = SERVICES[svc]
        container = cfg["container_name"]
        svc_status = get_container_status(container)

        info = {
            "status": svc_status,
            "container": container,
            "port": cfg["port"],
            "gpu": GPU_ALLOCATION.get(svc, "?"),
            "remote_url": cfg.get("remote_url", ""),
            "health_url": f"http://localhost:{cfg['port']}{cfg['health_endpoint']}",
        }

        # Tester health endpoint si running
        if svc_status == "running":
            try:
                import requests
                resp = requests.get(info["health_url"], timeout=5)
                info["health"] = "ok" if resp.status_code == 200 else f"http_{resp.status_code}"
            except Exception as e:
                info["health"] = f"error: {str(e)[:50]}"
        else:
            info["health"] = "n/a"

        status[svc] = info

    return status


def print_status_table():
    """Affiche le statut de tous les services audio."""
    status = get_all_audio_status()

    print("\n" + "=" * 90)
    print("  STATUT DES APIs AUDIO")
    print("=" * 90)

    print(f"\n{'Service':<15} | {'Container':<18} | {'Status':<12} | {'Health':<10} | {'GPU':<4} | {'Port':<6}")
    print("-" * 90)

    for svc, info in status.items():
        status_str = info.get("status", "?")
        health_str = info.get("health", "?")
        gpu_str = str(info.get("gpu", "?"))
        port_str = str(info.get("port", "?"))

        # Color coding
        if status_str == "running" and health_str == "ok":
            marker = "[OK]"
        elif status_str == "running":
            marker = "[??]"
        elif status_str == "exited":
            marker = "[--]"
        else:
            marker = "[NA]"

        print(f"{marker} {svc:<13} | {info['container']:<18} | {status_str:<12} | {health_str:<10} | {gpu_str:<4} | {port_str:<6}")

    print("\n" + "-" * 90)
    print("  Remote URLs:")
    for svc, info in status.items():
        if info.get("remote_url"):
            print(f"    {svc}: {info['remote_url']}")

    print("=" * 90 + "\n")


def get_running_on_gpu(gpu_id: int) -> List[str]:
    """Liste les services running sur un GPU donne."""
    running = []
    for svc in GPU_CONFLICTS.get(gpu_id, []):
        if svc in SERVICES:
            container = SERVICES[svc]["container_name"]
            if get_container_status(container) == "running":
                running.append(svc)
    return running


def stop_service(service_name: str) -> bool:
    """Arrete un service Docker."""
    if service_name not in SERVICES:
        print(f"Erreur: service '{service_name}' inconnu")
        return False

    cfg = SERVICES[service_name]
    container = cfg["container_name"]
    compose_dir = cfg["compose_dir"]

    print(f"Arret de {service_name}...")

    if get_container_status(container) != "running":
        print(f"  Deja arrete")
        return True

    result = subprocess.run(
        ["docker-compose", "down"],
        cwd=str(compose_dir),
        capture_output=True, text=True
    )

    if result.returncode == 0:
        print(f"  OK")
        return True
    else:
        print(f"  ERREUR: {result.stderr}")
        return False


def start_service(service_name: str, wait_health: bool = True) -> bool:
    """Demarre un service Docker."""
    if service_name not in SERVICES:
        print(f"Erreur: service '{service_name}' inconnu")
        return False

    cfg = SERVICES[service_name]
    container = cfg["container_name"]
    compose_dir = cfg["compose_dir"]

    print(f"Demarrage de {service_name}...")

    if get_container_status(container) == "running":
        print(f"  Deja en cours")
        return True

    # Verifier que le repertoire existe
    if not compose_dir.exists():
        print(f"  ERREUR: Repertoire non trouve: {compose_dir}")
        return False

    result = subprocess.run(
        ["docker-compose", "up", "-d"],
        cwd=str(compose_dir),
        capture_output=True, text=True
    )

    if result.returncode != 0:
        print(f"  ERREUR: {result.stderr}")
        return False

    print(f"  Container demarre")

    if wait_health:
        print(f"  Attente health check...", end=" ", flush=True)
        health_url = f"http://localhost:{cfg['port']}{cfg['health_endpoint']}"

        for i in range(30):  # 30 * 2s = 60s max
            time.sleep(2)
            try:
                import requests
                resp = requests.get(health_url, timeout=5)
                if resp.status_code == 200:
                    print("OK")
                    return True
            except:
                pass
            print(".", end="", flush=True)

        print(" TIMEOUT")
        return False

    return True


def switch_to_service(service_name: str) -> bool:
    """Switch GPU: arrete les conflits, demarre le service."""
    if service_name not in AUDIO_API_SERVICES:
        print(f"Erreur: '{service_name}' n'est pas un service audio API")
        print(f"Services disponibles: {', '.join(AUDIO_API_SERVICES)}")
        return False

    gpu_id = GPU_ALLOCATION.get(service_name)
    if gpu_id is None:
        print(f"Erreur: pas d'allocation GPU pour {service_name}")
        return False

    print(f"\n{'='*70}")
    print(f"  SWITCH GPU {gpu_id} -> {service_name}")
    print(f"{'='*70}\n")

    # Identifier les conflits
    conflicts = get_running_on_gpu(gpu_id)
    # Exclure le service cible
    conflicts = [c for c in conflicts if c != service_name]

    if conflicts:
        print(f"Services a arreter sur GPU {gpu_id}: {', '.join(conflicts)}")
        for svc in conflicts:
            stop_service(svc)
        print(f"\nAttente liberation VRAM (5s)...")
        time.sleep(5)

    # Demarrer le service
    success = start_service(service_name, wait_health=True)

    # Afficher resume GPU
    print(f"\nResume GPU:")
    import subprocess
    result = subprocess.run(
        ["nvidia-smi", "--query-gpu=index,name,memory.used,memory.free", "--format=csv,noheader"],
        capture_output=True, text=True
    )
    if result.returncode == 0:
        for line in result.stdout.strip().split("\n"):
            print(f"  {line}")

    print(f"\n{'='*70}")
    if success:
        print(f"  Service {service_name} actif sur https://{SERVICES[service_name].get('remote_url', 'localhost')}")
    else:
        print(f"  ECHEC du demarrage")
    print(f"{'='*70}\n")

    return success


def test_service(service_name: str) -> bool:
    """Teste un service (health + endpoint fonctionnel)."""
    if service_name not in SERVICES:
        print(f"Erreur: service '{service_name}' inconnu")
        return False

    cfg = SERVICES[service_name]
    port = cfg["port"]
    health_url = f"http://localhost:{port}{cfg['health_endpoint']}"

    print(f"\nTest de {service_name}:")
    print(f"  Health endpoint: {health_url}")

    # Health check
    try:
        import requests
        resp = requests.get(health_url, timeout=10)
        print(f"  Health: HTTP {resp.status_code}")

        if resp.status_code != 200:
            print(f"  Reponse: {resp.text[:200]}")
            return False

        # Parser la reponse
        try:
            data = resp.json()
            print(f"  Details: {json.dumps(data, indent=4)[:300]}")
        except:
            print(f"  Reponse (text): {resp.text[:200]}")

    except Exception as e:
        print(f"  ERREUR: {e}")
        return False

    # Test fonctionnel selon le service
    if service_name == "whisper-api":
        print(f"\n  Test transcription (endpoint /v1/models)...")
        try:
            resp = requests.get(f"http://localhost:{port}/v1/models", timeout=10)
            print(f"  Models: {resp.status_code} - {resp.text[:100]}")
        except Exception as e:
            print(f"  ERREUR: {e}")

    elif service_name == "tts-api":
        print(f"\n  Test TTS (endpoint /v1/voices)...")
        try:
            resp = requests.get(f"http://localhost:{port}/v1/voices", timeout=10)
            print(f"  Voices: {resp.status_code} - {resp.text[:100]}")
        except Exception as e:
            print(f"  ERREUR: {e}")

    elif service_name == "musicgen-api":
        print(f"\n  Test MusicGen (endpoint /v1/models)...")
        try:
            resp = requests.get(f"http://localhost:{port}/v1/models", timeout=10)
            print(f"  Models: {resp.status_code} - {resp.text[:100]}")
        except Exception as e:
            print(f"  ERREUR: {e}")

    elif service_name == "demucs-api":
        print(f"\n  Test Demucs (endpoint /v1/stems)...")
        try:
            resp = requests.get(f"http://localhost:{port}/v1/stems", timeout=10)
            print(f"  Stems: {resp.status_code} - {resp.text[:100]}")
        except Exception as e:
            print(f"  ERREUR: {e}")

    return True


# ============================================================================
# E2E Tests — real generation/transcription/separation
# ============================================================================

def _get_auth_headers(service_name: str = None) -> dict:
    """Load API key from .env file (service-specific key or generic)."""
    from pathlib import Path
    env_file = Path(__file__).resolve().parent.parent.parent.parent / "MyIA.AI.Notebooks" / "GenAI" / ".env"
    api_key = None
    if env_file.exists():
        # Try service-specific key first (e.g. MUSICGEN_API_KEY)
        env_vars = {}
        for line in env_file.read_text().splitlines():
            if "=" in line and not line.strip().startswith("#"):
                k, v = line.split("=", 1)
                env_vars[k.strip()] = v.strip().strip("'\"")
        if service_name:
            svc_key = service_name.replace("-", "_").upper() + "_API_KEY"
            api_key = env_vars.get(svc_key)
        if not api_key:
            api_key = env_vars.get("VLLM_API_KEY")  # shared fallback
    headers = {"Content-Type": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
    return headers


def e2e_test_service(service_name: str, timeout: int = 120) -> dict:
    """Run end-to-end test hitting real generation endpoints."""
    import requests

    result = {"service": service_name, "status": "SKIP", "detail": "", "size_bytes": 0, "time_s": 0.0}
    headers = _get_auth_headers(service_name)

    if service_name not in SERVICES:
        result["detail"] = f"Unknown service"
        return result

    port = SERVICES[service_name]["port"]
    base = f"http://localhost:{port}"

    try:
        if service_name == "whisper-api":
            t0 = time.time()
            resp = requests.post(
                f"{base}/v1/audio/transcriptions",
                headers={k: v for k, v in headers.items() if k != "Content-Type"},
                files={"file": ("test.wav", _make_silence_wav(), "audio/wav")},
                data={"language": "en"},
                timeout=timeout,
            )
            result["time_s"] = time.time() - t0
            result["status"] = "OK" if resp.status_code == 200 else f"HTTP_{resp.status_code}"
            result["size_bytes"] = len(resp.content)
            result["detail"] = resp.text[:200]

        elif service_name == "tts-api":
            t0 = time.time()
            resp = requests.post(
                f"{base}/v1/audio/speech",
                headers=headers,
                json={"input": "Hello, this is a test.", "voice": "af_bella"},
                timeout=timeout,
            )
            result["time_s"] = time.time() - t0
            result["status"] = "OK" if resp.status_code == 200 else f"HTTP_{resp.status_code}"
            result["size_bytes"] = len(resp.content)
            result["detail"] = f"audio/{resp.headers.get('Content-Type', '?')}"

        elif service_name == "musicgen-api":
            t0 = time.time()
            resp = requests.post(
                f"{base}/v1/generate",
                headers=headers,
                json={"prompt": "short piano note", "duration": 2},
                timeout=timeout,
            )
            result["time_s"] = time.time() - t0
            result["status"] = "OK" if resp.status_code == 200 else f"HTTP_{resp.status_code}"
            result["size_bytes"] = len(resp.content)
            result["detail"] = resp.headers.get("X-Duration", "?") + "s audio"

        elif service_name == "demucs-api":
            t0 = time.time()
            resp = requests.post(
                f"{base}/v1/separate/vocals",
                headers={k: v for k, v in headers.items() if k != "Content-Type"},
                files={"file": ("test.wav", _make_silence_wav(), "audio/wav")},
                timeout=timeout,
            )
            result["time_s"] = time.time() - t0
            result["status"] = "OK" if resp.status_code == 200 else f"HTTP_{resp.status_code}"
            result["size_bytes"] = len(resp.content)
            result["detail"] = resp.headers.get("X-Stem", "?")

        elif service_name == "funasr-api":
            t0 = time.time()
            resp = requests.post(
                f"{base}/v1/audio/transcriptions",
                headers={k: v for k, v in headers.items() if k != "Content-Type"},
                files={"file": ("test.wav", _make_silence_wav(), "audio/wav")},
                timeout=timeout,
            )
            result["time_s"] = time.time() - t0
            result["status"] = "OK" if resp.status_code == 200 else f"HTTP_{resp.status_code}"
            result["size_bytes"] = len(resp.content)
            result["detail"] = resp.text[:200]

    except requests.exceptions.Timeout:
        result["status"] = "TIMEOUT"
        result["detail"] = f">{timeout}s"
    except Exception as e:
        result["status"] = "ERROR"
        result["detail"] = str(e)[:100]

    return result


def _make_silence_wav() -> bytes:
    """Generate a minimal valid WAV file (1s silence, 16kHz mono)."""
    import struct, io
    sample_rate = 16000
    duration = 1
    num_samples = sample_rate * duration
    buf = io.BytesIO()
    # WAV header
    buf.write(b'RIFF')
    data_size = num_samples * 2  # 16-bit
    buf.write(struct.pack('<I', 36 + data_size))  # file size - 8
    buf.write(b'WAVE')
    buf.write(b'fmt ')
    buf.write(struct.pack('<I', 16))  # chunk size
    buf.write(struct.pack('<H', 1))   # PCM
    buf.write(struct.pack('<H', 1))   # mono
    buf.write(struct.pack('<I', sample_rate))
    buf.write(struct.pack('<I', sample_rate * 2))  # byte rate
    buf.write(struct.pack('<H', 2))   # block align
    buf.write(struct.pack('<H', 16))  # bits per sample
    buf.write(b'data')
    buf.write(struct.pack('<I', data_size))
    buf.write(b'\x00' * data_size)
    return buf.getvalue()


def e2e_test_all(services: List[str] = None, timeout: int = 120) -> List[dict]:
    """Run E2E tests on all (or specified) audio services."""
    if services is None:
        services = AUDIO_API_SERVICES

    results = []
    print(f"\n{'='*80}")
    print(f"  E2E SERVICE TESTS (timeout: {timeout}s)")
    print(f"{'='*80}\n")

    for svc in services:
        print(f"  Testing {svc}...", end=" ", flush=True)
        r = e2e_test_service(svc, timeout=timeout)
        results.append(r)
        marker = "[OK]" if r["status"] == "OK" else "[FAIL]"
        size_str = f"{r['size_bytes']/1024:.1f}KB" if r["size_bytes"] else "-"
        print(f"{marker} {r['status']} | {size_str} | {r['time_s']:.1f}s | {r['detail'][:60]}")

    ok = sum(1 for r in results if r["status"] == "OK")
    print(f"\n  Results: {ok}/{len(results)} passed")
    print(f"{'='*80}\n")
    return results


def build_service(service_name: str) -> bool:
    """Construit l'image Docker d'un service."""
    if service_name not in SERVICES:
        print(f"Erreur: service '{service_name}' inconnu")
        return False

    cfg = SERVICES[service_name]
    compose_dir = cfg["compose_dir"]

    if not compose_dir.exists():
        print(f"Erreur: repertoire non trouve: {compose_dir}")
        return False

    print(f"Construction de {service_name}...")
    print(f"  Repertoire: {compose_dir}")

    result = subprocess.run(
        ["docker-compose", "build", "--no-cache"],
        cwd=str(compose_dir),
        capture_output=False,  # Afficher la sortie en direct
        text=True
    )

    if result.returncode == 0:
        print(f"\n  Build OK")
        return True
    else:
        print(f"\n  Build ECHEC")
        return False


def show_logs(service_name: str, tail: int = 50):
    """Affiche les logs d'un service."""
    if service_name not in SERVICES:
        print(f"Erreur: service '{service_name}' inconnu")
        return

    cfg = SERVICES[service_name]
    container = cfg["container_name"]

    subprocess.run(
        ["docker", "logs", container, "--tail", str(tail), "-f"],
    )


# ============================================================================
# CLI
# ============================================================================

def register(subparsers):
    """Enregistre la sous-commande audio-apis."""
    parser = subparsers.add_parser('audio-apis', help='Gestion des containers d\'APIs Audio')
    sub = parser.add_subparsers(dest='audio_action')

    # status
    sub.add_parser('status', help='Statut de tous les services audio')

    # start
    p_start = sub.add_parser('start', help='Demarrer un service')
    p_start.add_argument('service', choices=AUDIO_API_SERVICES, help='Service a demarrer')

    # stop
    p_stop = sub.add_parser('stop', help='Arreter un service')
    p_stop.add_argument('service', choices=AUDIO_API_SERVICES, help='Service a arreter')

    # switch
    p_switch = sub.add_parser('switch', help='Switch GPU: arreter conflits, demarrer service')
    p_switch.add_argument('service', choices=AUDIO_API_SERVICES, help='Service cible')

    # test
    p_test = sub.add_parser('test', help='Tester un service (health + endpoint)')
    p_test.add_argument('service', choices=AUDIO_API_SERVICES, help='Service a tester')

    # build
    p_build = sub.add_parser('build', help='Construire l\'image Docker')
    p_build.add_argument('service', choices=AUDIO_API_SERVICES, help='Service a construire')
    p_build.add_argument('--no-cache', action='store_true', help='Build sans cache')

    # logs
    p_logs = sub.add_parser('logs', help='Voir les logs')
    p_logs.add_argument('service', choices=AUDIO_API_SERVICES, help='Service')
    p_logs.add_argument('--tail', type=int, default=50, help='Nombre de lignes')

    # e2e
    p_e2e = sub.add_parser('e2e', help='End-to-end test (real generation endpoints)')
    p_e2e.add_argument('service', nargs='?', choices=AUDIO_API_SERVICES, help='Service (default: all)')
    p_e2e.add_argument('--timeout', type=int, default=120, help='Timeout per test (seconds)')
    p_e2e.add_argument('--quick', action='store_true', help='Skip services that are not running')


def execute(args) -> int:
    """Execute la commande audio-apis."""
    action = getattr(args, 'audio_action', None)

    if action is None or action == 'status':
        print_status_table()
        return 0

    service = getattr(args, 'service', None)

    if action == 'start':
        return 0 if start_service(service) else 1

    elif action == 'stop':
        return 0 if stop_service(service) else 1

    elif action == 'switch':
        return 0 if switch_to_service(service) else 1

    elif action == 'test':
        return 0 if test_service(service) else 1

    elif action == 'build':
        return 0 if build_service(service) else 1

    elif action == 'logs':
        show_logs(service, tail=getattr(args, 'tail', 50))
        return 0

    elif action == 'e2e':
        svc = getattr(args, 'service', None)
        if svc:
            results = [e2e_test_service(svc, timeout=args.timeout)]
        else:
            results = e2e_test_all(timeout=args.timeout)
        return 0 if all(r["status"] == "OK" for r in results) else 1

    return 1


def main():
    """Point d'entree standalone."""
    import argparse
    parser = argparse.ArgumentParser(description="Gestion des APIs Audio")
    sub = parser.add_subparsers(dest='action')

    sub.add_parser('status')
    p_start = sub.add_parser('start')
    p_start.add_argument('service', choices=AUDIO_API_SERVICES)
    p_stop = sub.add_parser('stop')
    p_stop.add_argument('service', choices=AUDIO_API_SERVICES)
    p_switch = sub.add_parser('switch')
    p_switch.add_argument('service', choices=AUDIO_API_SERVICES)
    p_test = sub.add_parser('test')
    p_test.add_argument('service', choices=AUDIO_API_SERVICES)
    p_build = sub.add_parser('build')
    p_build.add_argument('service', choices=AUDIO_API_SERVICES)
    p_logs = sub.add_parser('logs')
    p_logs.add_argument('service', choices=AUDIO_API_SERVICES)
    p_e2e = sub.add_parser('e2e')
    p_e2e.add_argument('service', nargs='?', choices=AUDIO_API_SERVICES)
    p_e2e.add_argument('--timeout', type=int, default=120)

    args = parser.parse_args()

    if args.action is None or args.action == 'status':
        print_status_table()
    elif args.action == 'start':
        start_service(args.service)
    elif args.action == 'stop':
        stop_service(args.service)
    elif args.action == 'switch':
        switch_to_service(args.service)
    elif args.action == 'test':
        test_service(args.service)
    elif args.action == 'build':
        build_service(args.service)
    elif args.action == 'logs':
        show_logs(args.service)
    elif args.action == 'e2e':
        svc = args.service
        if svc:
            results = [e2e_test_service(svc, timeout=args.timeout)]
        else:
            results = e2e_test_all(timeout=args.timeout)
        sys.exit(0 if all(r["status"] == "OK" for r in results) else 1)


if __name__ == "__main__":
    main()
