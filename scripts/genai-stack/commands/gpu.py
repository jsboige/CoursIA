#!/usr/bin/env python3
"""
commands/gpu.py - Verification VRAM, GPU et gestion des profils GPU

Sous-commandes :
    genai.py gpu                       # Tableau nvidia-smi (rapide)
    genai.py gpu --detailed            # Validation Docker + PyTorch/CUDA
    genai.py gpu profile list          # Lister les profils GPU
    genai.py gpu profile apply <name>  # Appliquer un profil (stop/start services)
    genai.py gpu profile current       # Detecter le profil actuel
    genai.py gpu check-fit <vram_mb>   # Verifier si un modele tient en VRAM
    genai.py gpu schedule <group>      # Appliquer le profil pour un groupe de notebooks
    genai.py gpu lock on               # Poser le verrou de clocks GPU (undervolt lock)
    genai.py gpu lock off              # Retirer le verrou de clocks GPU
    genai.py gpu lock status           # Afficher les clocks GPU courantes/max
    genai.py gpu lock register         # Planifier la tache au demarrage ([INTERACTIVE-ONLY])
"""

import subprocess
import csv
import io
import json
import os
import re
import sys
import time
from datetime import datetime
import logging
from pathlib import Path
from typing import List, Dict, Optional

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from config import SERVICES, GPU_PROFILES, GROUP_GPU_PROFILE

logger = logging.getLogger("GPUManager")


# ============================================================================
# Fonctions GPU de base (existantes)
# ============================================================================

def check_vram() -> List[Dict]:
    """Recupere les informations VRAM via nvidia-smi. Retourne une liste de dicts."""
    try:
        cmd = [
            'nvidia-smi',
            '--query-gpu=index,name,memory.total,memory.used,memory.free',
            '--format=csv,noheader,nounits'
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", check=True)

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
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, encoding="utf-8", errors="replace")
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


# ============================================================================
# Gestion des profils GPU
# ============================================================================

def _get_docker_manager():
    """Retourne une instance de DockerManager (import lazy pour eviter les cycles)."""
    from commands.docker import DockerManager
    return DockerManager()


def _get_running_services() -> List[str]:
    """Detecte les services actuellement en cours d'execution."""
    running = []
    for name, svc in SERVICES.items():
        result = subprocess.run(
            ["docker", "inspect", svc["container_name"], "--format", "{{.State.Running}}"],
            capture_output=True, text=True, encoding="utf-8", errors="replace"
        )
        if result.returncode == 0 and "true" in result.stdout.lower():
            running.append(name)
    return running


def profile_list():
    """Affiche tous les profils GPU disponibles."""
    print("\n" + "=" * 70)
    print("  PROFILS GPU DISPONIBLES")
    print("=" * 70)

    for name, profile in GPU_PROFILES.items():
        print(f"\n  [{name}]")
        print(f"    Description : {profile['description']}")
        if profile['services_up']:
            print(f"    Demarrer    : {', '.join(profile['services_up'])}")
        if profile['services_down']:
            print(f"    Arreter     : {', '.join(profile['services_down'])}")
        print(f"    GPU 0 (3090): {profile.get('gpu_0_usage', 'non specifie')}")
        print(f"    GPU 1 (3080): {profile.get('gpu_1_usage', 'non specifie')}")

    print(f"\n{'=' * 70}")
    print(f"  {len(GPU_PROFILES)} profils disponibles")
    print(f"  Usage: genai.py gpu profile apply <nom_profil>")
    print(f"{'=' * 70}\n")


def profile_current() -> Optional[str]:
    """Detecte le profil GPU actuel en fonction des services en cours."""
    running = _get_running_services()

    print("\n" + "=" * 70)
    print("  PROFIL GPU ACTUEL")
    print("=" * 70)

    print(f"\n  Services actifs: {', '.join(running) if running else 'aucun'}")

    # Trouver le profil le plus proche
    best_match = None
    best_score = -1

    for name, profile in GPU_PROFILES.items():
        score = 0
        expected_up = set(profile['services_up'])
        expected_down = set(profile['services_down'])
        running_set = set(running)

        # Points pour les services up qui sont effectivement running
        for svc in expected_up:
            if svc in running_set:
                score += 2
            else:
                score -= 3  # penalite si un service requis n'est pas la

        # Points pour les services down qui sont effectivement arretes
        for svc in expected_down:
            if svc not in running_set:
                score += 1
            else:
                score -= 2  # penalite si un service devrait etre arrete

        if score > best_score:
            best_score = score
            best_match = name

    if best_match:
        profile = GPU_PROFILES[best_match]
        print(f"\n  Profil detecte : {best_match}")
        print(f"  Description    : {profile['description']}")
        print(f"  Score match    : {best_score}")

        # Verifier la conformite
        expected_up = set(profile['services_up'])
        expected_down = set(profile['services_down'])
        running_set = set(running)

        missing_up = expected_up - running_set
        unexpected_up = expected_down & running_set

        if missing_up:
            print(f"  Manquants      : {', '.join(missing_up)}")
        if unexpected_up:
            print(f"  A arreter      : {', '.join(unexpected_up)}")
        if not missing_up and not unexpected_up:
            print(f"  Conformite     : OK")
    else:
        print(f"\n  Aucun profil correspondant detecte")

    # GPU info
    gpus = check_vram()
    if gpus:
        print(f"\n  VRAM :")
        for gpu in gpus:
            print(f"    GPU {gpu['index']} ({gpu['name']}): {gpu['free']}MB libre / {gpu['total']}MB")

    print(f"\n{'=' * 70}\n")
    return best_match


def profile_apply(profile_name: str, wait_health: bool = True) -> bool:
    """Applique un profil GPU : arrete les services_down, demarre les services_up.

    Args:
        profile_name: Nom du profil a appliquer
        wait_health: Attendre que les services demarres soient en bonne sante

    Returns:
        True si le profil a ete applique avec succes
    """
    if profile_name not in GPU_PROFILES:
        print(f"Erreur: profil '{profile_name}' inconnu.")
        print(f"Profils disponibles: {', '.join(GPU_PROFILES.keys())}")
        return False

    profile = GPU_PROFILES[profile_name]
    print(f"\n{'=' * 70}")
    print(f"  APPLICATION DU PROFIL GPU: {profile_name}")
    print(f"  {profile['description']}")
    print(f"{'=' * 70}")

    manager = _get_docker_manager()
    success = True

    # 1. Arreter les services_down
    services_down = profile.get('services_down', [])
    if services_down:
        print(f"\n  Arret des services...")
        for svc in services_down:
            if svc not in SERVICES:
                print(f"    [{svc}] Service non configure, ignore")
                continue
            # Verifier si le service tourne avant de l'arreter
            running = _get_running_services()
            if svc in running:
                print(f"    [{svc}] Arret...", end=" ", flush=True)
                if manager.stop_service(svc):
                    print("OK")
                else:
                    print("ECHEC")
                    success = False
            else:
                print(f"    [{svc}] Deja arrete")

    # 2. Attendre que la VRAM se libere
    if services_down:
        print(f"\n  Attente liberation VRAM (5s)...")
        time.sleep(5)

    # 3. Demarrer les services_up
    services_up = profile.get('services_up', [])
    if services_up:
        print(f"\n  Demarrage des services...")
        for svc in services_up:
            if svc not in SERVICES:
                print(f"    [{svc}] Service non configure, ignore")
                continue
            running = _get_running_services()
            if svc in running:
                print(f"    [{svc}] Deja actif")
            else:
                print(f"    [{svc}] Demarrage...", end=" ", flush=True)
                if manager.start_service(svc):
                    print("OK")
                else:
                    print("ECHEC")
                    success = False

    # 4. Verifier la sante si demande
    if wait_health and services_up:
        print(f"\n  Verification de la sante des services...")
        for svc in services_up:
            if svc not in SERVICES:
                continue
            max_retries = 10
            for attempt in range(max_retries):
                healthy, msg = manager.check_service_health(svc)
                if healthy:
                    print(f"    [{svc}] Sain ({msg})")
                    break
                if attempt < max_retries - 1:
                    time.sleep(10)
            else:
                print(f"    [{svc}] Non sain apres {max_retries} tentatives ({msg})")
                success = False

    # Resume VRAM
    gpus = check_vram()
    if gpus:
        print(f"\n  VRAM apres application :")
        for gpu in gpus:
            print(f"    GPU {gpu['index']} ({gpu['name']}): {gpu['free']}MB libre / {gpu['total']}MB")

    status = "OK" if success else "PARTIEL"
    print(f"\n  Resultat: {status}")
    print(f"{'=' * 70}\n")
    return success


def check_fit(vram_mb: int, gpu_index: Optional[int] = None) -> bool:
    """Verifie si un modele de vram_mb MiB peut tenir sur un GPU.

    Args:
        vram_mb: VRAM requise en MiB
        gpu_index: Index nvidia-smi du GPU (None = tous)

    Returns:
        True si le modele peut tenir
    """
    gpus = check_vram()
    if not gpus:
        print("Aucun GPU detecte.")
        return False

    print(f"\nVerification de compatibilite VRAM ({vram_mb} MiB requis):")
    fits = False

    for gpu in gpus:
        idx = int(gpu['index'])
        if gpu_index is not None and idx != gpu_index:
            continue

        free = gpu['free']
        ok = free >= vram_mb
        status = "OK" if ok else "INSUFFISANT"
        print(f"  GPU {idx} ({gpu['name']}): {free} MiB libre - {status}")
        if ok:
            fits = True

    if not fits:
        print(f"\n  Aucun GPU compatible. Liberez de la VRAM avec:")
        print(f"    genai.py gpu profile apply video_local_heavy")
    return fits


def schedule_group(group_name: str) -> bool:
    """Determine et applique le profil GPU pour un groupe de notebooks.

    Args:
        group_name: Nom du groupe (ex: audio_api, video_diffusion_heavy)

    Returns:
        True si le profil a ete applique avec succes
    """
    if group_name not in GROUP_GPU_PROFILE:
        print(f"Erreur: groupe '{group_name}' inconnu.")
        print(f"Groupes disponibles: {', '.join(sorted(GROUP_GPU_PROFILE.keys()))}")
        return False

    profile_name = GROUP_GPU_PROFILE[group_name]
    print(f"Groupe '{group_name}' -> profil GPU '{profile_name}'")
    return profile_apply(profile_name)


# ============================================================================
# Verrou de clocks GPU (undervolt lock) - persistant au demarrage
# ============================================================================

GPU_LOCK_MIN_MHZ = 210
GPU_LOCK_MAX_MHZ = 1800
GPU_LOCK_CLOCKS = f"{GPU_LOCK_MIN_MHZ},{GPU_LOCK_MAX_MHZ}"


def _gpu_lock_log_path() -> Path:
    """Chemin absolu du journal du verrou GPU (user-scope, hors repo)."""
    base = os.environ.get("LOCALAPPDATA") or os.environ.get("XDG_STATE_HOME") or str(Path.home() / ".local" / "state")
    log_dir = Path(base) / "myia"
    log_dir.mkdir(parents=True, exist_ok=True)
    return log_dir / "gpu_lock.log"


def _gpu_lock_journal(action: str, state: str, detail: str) -> str:
    """Ajoute une ligne horodatee au journal du verrou GPU. Retourne la ligne."""
    ts = datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    line = f"[{ts}] {action} -> {state} | {detail}"
    try:
        with open(_gpu_lock_log_path(), "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError as e:
        logger.warning("gpu-lock: journal inecrivable: %s", e)
    print(line)
    return line


def _parse_mhz(value: str) -> Optional[int]:
    """Extrait une valeur entiere en MHz ('1230 MHz' -> 1230, sinon None)."""
    m = re.search(r"(\d+)\s*MHz", value, re.IGNORECASE)
    return int(m.group(1)) if m else None


def _parse_clocks_stdout(stdout: str) -> tuple:
    """Extrait (courant_mhz, max_mhz) du Graphics depuis `nvidia-smi -q -d CLOCK`."""
    current = None
    max_clock = None
    section = None
    for line in stdout.splitlines():
        s = line.strip()
        if not s:
            continue
        if ":" not in s:
            # En-tete de section (libelle indente sans deux-points), ex: "Clocks", "Max Clocks".
            section = s
            continue
        label, _, value = s.partition(":")
        label = label.strip()
        value = value.strip()
        if label == "Graphics":
            mhz = _parse_mhz(value)
            if mhz is None:
                continue
            if section == "Clocks":
                current = mhz
            elif section == "Max Clocks":
                max_clock = mhz
    return current, max_clock


def _print_lock_status(current: Optional[int], max_clock: Optional[int]):
    """Affiche les clocks Graphics courantes et max."""
    cur_txt = f"{current} MHz" if current is not None else "indisponible"
    max_txt = f"{max_clock} MHz" if max_clock is not None else "indisponible"
    print("  Clocks Graphics (courant) :", cur_txt)
    print("  Max Clocks Graphics (max)  :", max_txt)


def gpu_lock_status() -> Optional[Dict[str, Optional[int]]]:
    """Lit `nvidia-smi -q -d CLOCK` et retourne {'current_mhz': int|None, 'max_mhz': int|None}."""
    ok, stdout, stderr = _run_cmd("nvidia-smi -q -d CLOCK")
    if not ok:
        print("[gpu-lock] ECHEC: nvidia-smi -q -d CLOCK a retourne un code non nul:")
        print("  " + (stderr.strip() or stdout.strip() or "rc != 0"))
        return None
    current, max_clock = _parse_clocks_stdout(stdout)
    _print_lock_status(current, max_clock)
    return {"current_mhz": current, "max_mhz": max_clock}


def _verify_lock(enable: bool, current: Optional[int], max_clock: Optional[int]) -> str:
    """Verdict du verrou : OK / ECHEC / INDETERMINE selon les clocks observees."""
    if enable:
        # Verrou pose : la butee max appliquee ne doit pas depasser la butee configuree.
        if max_clock is not None:
            return "OK" if max_clock <= GPU_LOCK_MAX_MHZ else "ECHEC"
        return "INDETERMINE"
    # off : la limite max doit redevenir libre (au-dela de la butee).
    if max_clock is not None:
        return "OK" if max_clock > GPU_LOCK_MAX_MHZ else "ECHEC"
    return "INDETERMINE"


def gpu_lock_apply(enable: bool, clocks: str = GPU_LOCK_CLOCKS) -> bool:
    """Applique (enable=True, `nvidia-smi -lgc`) ou retire (False, `nvidia-smi -rgc`) le verrou.

    Journalise la commande, le rc et la verification dans _gpu_lock_log_path().
    Retourne True si la commande a reussi (le verdict de verification est journalise + affiche).
    """
    if enable:
        cmd = f"nvidia-smi -lgc {clocks}"
        action = f"lock-on {clocks}"
    else:
        cmd = "nvidia-smi -rgc"
        action = "lock-off"
    ok, stdout, stderr = _run_cmd(cmd)
    if not ok:
        _gpu_lock_journal(action, "ECHEC", "cmd=%s rc!=0: %s" % (cmd, (stderr.strip() or stdout.strip())[:200]))
        print(f"[gpu-lock] ECHEC: {cmd}")
        print("  " + (stderr.strip() or stdout.strip()))
        return False
    status = gpu_lock_status()
    if status is None:
        _gpu_lock_journal(action, "INDETERMINE", "cmd=%s verif: nvidia-smi -q -d CLOCK invalide" % cmd)
        return True
    current = status["current_mhz"]
    max_clock = status["max_mhz"]
    verdict = _verify_lock(enable, current, max_clock)
    _gpu_lock_journal(action, verdict, "cmd=%s || courant=%sMHz max=%sMHz" % (cmd, current, max_clock))
    print("  Verification:", verdict)
    print("  Journal   :", _gpu_lock_log_path())
    return True


def gpu_lock_register() -> None:
    """Affiche (sans l'executer) la commande de planification de la tache au demarrage.

    La planification touche UAC (elevation) => [INTERACTIVE-ONLY] : ce dry-run ne fait
    que preparer la commande a recoller dans une invite Administrateur.
    """
    genai_py = _script_dir / "genai.py"
    print("=" * 70)
    print("  PLANIFICATION TACHE AUTO - VERROU CLOCKS AU DEMARRAGE")
    print("  [INTERACTIVE-ONLY] : execution requiert une invite Administrateur (UAC)")
    print("  Aucune action n'a ete effectuee (dry-run).")
    print("=" * 70)
    print()
    print("  Version boot (onstart, SYSTEM, privilege HIGHEST) :")
    inner = '\\"python\\" \\"%s\\" gpu lock on' % genai_py
    print('    schtasks /create /tn "MyIA_GPUUndervoltClockLock" /tr "%s" /sc onstart /ru SYSTEM /rl HIGHEST /f' % inner)
    print()
    print("  Alternative logon (onlogon, utilisateur connecte) :")
    print('    schtasks /create /tn "MyIA_GPUUndervoltClockLock" /tr "%s" /sc onlogon /rl HIGHEST /f' % inner)
    print()
    print("  Pour supprimer la tache plus tard :")
    print('    schtasks /delete /tn "MyIA_GPUUndervoltClockLock" /f')
    print()
    print("  NOTE : adapter le chemin python si besoin (ex: full path python.exe / py -3.11).")
    print("  La tache journalise dans", _gpu_lock_log_path())


# ============================================================================
# CLI
# ============================================================================

def register(subparsers):
    """Enregistre la sous-commande gpu."""
    parser = subparsers.add_parser('gpu', help='Verification VRAM, GPU et profils')
    sub = parser.add_subparsers(dest='gpu_action')

    # gpu (sans sous-commande) : tableau nvidia-smi
    parser.add_argument('--detailed', action='store_true',
                       help='Validation detaillee (container Docker, PyTorch/CUDA)')
    parser.add_argument('--json', action='store_true',
                       help='Sortie JSON')

    # gpu profile
    p_profile = sub.add_parser('profile', help='Gestion des profils GPU')
    profile_sub = p_profile.add_subparsers(dest='profile_action')

    profile_sub.add_parser('list', help='Lister les profils disponibles')
    profile_sub.add_parser('current', help='Detecter le profil actuel')

    p_apply = profile_sub.add_parser('apply', help='Appliquer un profil')
    p_apply.add_argument('name', choices=list(GPU_PROFILES.keys()),
                        help='Nom du profil a appliquer')
    p_apply.add_argument('--no-wait', action='store_true',
                        help='Ne pas attendre la sante des services')

    # gpu check-fit
    p_fit = sub.add_parser('check-fit', help='Verifier si un modele tient en VRAM')
    p_fit.add_argument('vram_mb', type=int, help='VRAM requise en MiB')
    p_fit.add_argument('--gpu', type=int, default=None,
                      help='Index nvidia-smi du GPU cible')

    # gpu schedule
    p_schedule = sub.add_parser('schedule', help='Appliquer le profil GPU pour un groupe')
    p_schedule.add_argument('group', choices=list(GROUP_GPU_PROFILE.keys()),
                           help='Groupe de notebooks')

    # gpu lock
    p_lock = sub.add_parser('lock', help='Verrou de clocks GPU (undervolt, persistant au boot)')
    lock_sub = p_lock.add_subparsers(dest='lock_action')
    p_lock_on = lock_sub.add_parser('on', help='Appliquer le verrou (nvidia-smi -lgc)')
    p_lock_on.add_argument('--clocks', default=GPU_LOCK_CLOCKS,
                          help='Plage MIN,MAX en MHz (defaut: 210,1800)')
    lock_sub.add_parser('off', help='Retirer le verrou (nvidia-smi -rgc)')
    lock_sub.add_parser('status', help='Afficher l etat des clocks GPU')
    lock_sub.add_parser('register', help='Planifier la tache au demarrage ([INTERACTIVE-ONLY])')


def execute(args) -> int:
    """Execute la commande gpu."""
    action = getattr(args, 'gpu_action', None)

    if action == 'profile':
        profile_action = getattr(args, 'profile_action', None)
        if profile_action == 'list':
            profile_list()
            return 0
        elif profile_action == 'current':
            profile_current()
            return 0
        elif profile_action == 'apply':
            wait = not getattr(args, 'no_wait', False)
            ok = profile_apply(args.name, wait_health=wait)
            return 0 if ok else 1
        else:
            profile_list()
            return 0

    elif action == 'check-fit':
        ok = check_fit(args.vram_mb, gpu_index=args.gpu)
        return 0 if ok else 1

    elif action == 'schedule':
        ok = schedule_group(args.group)
        return 0 if ok else 1

    elif action == 'lock':
        lock_action = getattr(args, 'lock_action', None)
        if lock_action == 'on':
            ok = gpu_lock_apply(True, clocks=args.clocks)
            return 0 if ok else 1
        elif lock_action == 'off':
            ok = gpu_lock_apply(False)
            return 0 if ok else 1
        elif lock_action == 'status':
            st = gpu_lock_status()
            return 0 if st is not None else 1
        else:  # lock (sans sous-commande) ou register
            gpu_lock_register()
            return 0

    # Commande gpu sans sous-commande : comportement original
    if getattr(args, 'detailed', False):
        ok = check_gpu_detailed()
        return 0 if ok else 1

    gpus = check_vram()

    if getattr(args, 'json', False):
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
