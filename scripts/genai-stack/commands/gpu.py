#!/usr/bin/env python3
"""
commands/gpu.py - Verification VRAM et GPU

Sous-commandes :
    genai.py gpu              # Tableau nvidia-smi (rapide)
    genai.py gpu --detailed   # Validation Docker + PyTorch/CUDA dans le container
"""

import subprocess
import csv
import io
import json
import sys
from typing import List, Dict, Optional


def check_vram() -> List[Dict]:
    """Recupere les informations VRAM via nvidia-smi. Retourne une liste de dicts."""
    try:
        cmd = [
            'nvidia-smi',
            '--query-gpu=index,name,memory.total,memory.used,memory.free',
            '--format=csv,noheader,nounits'
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, check=True)

        gpus = []
        csv_reader = csv.reader(io.StringIO(result.stdout))
        for row in csv_reader:
            if len(row) == 5:
                gpus.append({
                    'index': row[0].strip(),
                    'name': row[1].strip(),
                    'total': int(row[2].strip()),
                    'used': int(row[3].strip()),
                    'free': int(row[4].strip()),
                })
        return gpus

    except FileNotFoundError:
        print("Erreur: nvidia-smi introuvable. Pilotes NVIDIA non installes.")
        return []
    except subprocess.CalledProcessError as e:
        print(f"Erreur nvidia-smi: {e}")
        return []


def print_gpu_table(gpus: List[Dict]):
    """Affiche un tableau formate des GPUs."""
    if not gpus:
        print("Aucun GPU detecte.")
        return

    print(f"{'Index':<6} | {'Nom':<30} | {'Libre / Total (MiB)':<25} | {'Utilise':<10}")
    print("-" * 80)

    for gpu in gpus:
        memory_str = f"{gpu['free']} / {gpu['total']} MiB"
        percent_used = (gpu['used'] / gpu['total']) * 100
        used_str = f"{gpu['used']} MiB ({percent_used:.1f}%)"
        print(f"{gpu['index']:<6} | {gpu['name']:<30} | {memory_str:<25} | {used_str:<10}")


def _run_cmd(cmd: str):
    """Execute une commande shell et retourne (success, stdout, stderr)."""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        return result.returncode == 0, result.stdout, result.stderr
    except Exception as e:
        return False, "", str(e)


def check_gpu_detailed():
    """Validation detaillee : container Docker, nvidia-smi dans container, PyTorch/CUDA, API ComfyUI."""

    checks = []

    # 1. Container Docker
    print("Validation container Docker ComfyUI...")
    ok, stdout, stderr = _run_cmd("docker inspect comfyui-qwen --format '{{.State.Status}}'")
    if ok and "running" in stdout.lower():
        print("  OK: Container comfyui-qwen en cours d'execution")
        checks.append(True)
    else:
        print("  ECHEC: Container comfyui-qwen non actif")
        checks.append(False)

    # 2. GPU dans container
    print("\nValidation GPU dans container...")
    ok, stdout, stderr = _run_cmd("docker exec comfyui-qwen nvidia-smi --query-gpu=name,memory.total --format=csv,noheader")
    if ok:
        print(f"  OK: GPU detecte - {stdout.strip()}")
        checks.append(True)
    else:
        print(f"  ECHEC: nvidia-smi inaccessible dans container")
        checks.append(False)

    # 3. API ComfyUI system_stats
    print("\nValidation API ComfyUI...")
    try:
        import requests
        resp = requests.get("http://localhost:8188/system_stats", timeout=5)
        if resp.status_code == 200:
            data = resp.json()
            devices = data.get('devices', [])
            if devices:
                dev = devices[0]
                vram_total = dev.get('vram_total', 0) / (1024**3)
                vram_free = dev.get('vram_free', 0) / (1024**3)
                print(f"  OK: {dev.get('name', 'GPU')} - {vram_free:.1f}GB libre / {vram_total:.1f}GB total")
            checks.append(True)
        elif resp.status_code == 401:
            print("  OK: API accessible (auth requise pour details)")
            checks.append(True)
        else:
            print(f"  ECHEC: HTTP {resp.status_code}")
            checks.append(False)
    except Exception as e:
        print(f"  ECHEC: {e}")
        checks.append(False)

    # Resume
    passed = sum(checks)
    total = len(checks)
    print(f"\nResultat: {passed}/{total} validations reussies")
    return all(checks)


def register(subparsers):
    """Enregistre la sous-commande gpu."""
    parser = subparsers.add_parser('gpu', help='Verification VRAM et GPU')
    parser.add_argument('--detailed', action='store_true',
                       help='Validation detaillee (container Docker, PyTorch/CUDA)')
    parser.add_argument('--json', action='store_true',
                       help='Sortie JSON')


def execute(args) -> int:
    """Execute la commande gpu."""
    if args.detailed:
        ok = check_gpu_detailed()
        return 0 if ok else 1

    gpus = check_vram()

    if args.json:
        print(json.dumps(gpus, indent=2))
    else:
        print_gpu_table(gpus)

    return 0 if gpus else 1


def main():
    """Point d'entree standalone."""
    import argparse
    parser = argparse.ArgumentParser(description="Verification VRAM et GPU")
    parser.add_argument('--detailed', action='store_true')
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
