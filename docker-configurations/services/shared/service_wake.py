"""service_wake.py — Réveille à la demande les services GenAI idle-stoppés.

Contrepartie de `service_idle_monitor.py` : le monitor auto-STOPPE les services
après `idle_timeout` (20 min) pour libérer la VRAM GPU ; ce module auto-START le
service à la demande afin qu'un notebook/script obtienne un warm-up transparent
au lieu d'un HTTP 502 / connection-refused.

## Pourquoi wake-and-retry côté appelant (décision #2982)

Aucun des 16 services ne configure `idle_action=sleep` (grep vérifié 2026-06-14) :
ils font tous `docker stop`. Un container stoppé n'a AUCUN listener sur son port,
donc le wake-on-request DOIT originates de l'appelant (ou d'un proxy persistant).

- Un helper côté appelant est **low-blast** (additif, ne modifie pas le monitor
  en cours d'exécution) et fonctionne uniformément pour les 16 services.
- Un reverse-proxy (approche A de l'issue) serait **over-engineering** pour une
  stack dev/teaching : il faudrait un process persistant par service + de la
  config de routing.
- **Économie VRAM préservée** : les services s'auto-stoppent toujours après
  20 min d'inactivité ; le helper ne lance `docker start` qu'en cas de demande
  réelle.

## Usage (Python)

    from service_wake import ensure_service_up
    if ensure_service_up("musicgen-api", "http://localhost:8192/health"):
        # sûr pour POST http://localhost:8192/v1/generate
        ...

## Usage (CLI)

    python service_wake.py musicgen-api --health-url http://localhost:8192/health
"""

from __future__ import annotations

import argparse
import logging
import subprocess
import sys
import time
from typing import Optional

import requests

logger = logging.getLogger("service_wake")

# Marges calibrées sur po-2023 : musicgen lazy-load ~18s, modèles lourds jusqu'à ~2min.
DEFAULT_TIMEOUT = 180
DEFAULT_POLL_INTERVAL = 2
_HEALTH_PROBE_TIMEOUT = 5


def probe_health(
    health_url: str, api_key: Optional[str] = None, timeout: float = _HEALTH_PROBE_TIMEOUT
) -> bool:
    """GET health_url ; True si HTTP 200 (service UP et prêt)."""
    headers = {"Authorization": f"Bearer {api_key}"} if api_key else {}
    try:
        resp = requests.get(health_url, headers=headers, timeout=timeout)
        return resp.status_code == 200
    except requests.exceptions.RequestException:
        return False


def docker_start(container: str) -> bool:
    """`docker start <container>` ; True si la commande réussit (exit 0).

    Via subprocess (docker CLI universelle sur po-2023). Ne présume pas de l'état
    précédent : `docker start` est idempotente (noop si déjà démarré).
    """
    try:
        result = subprocess.run(
            ["docker", "start", container],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        if result.returncode != 0:
            logger.error(
                "docker start %s failed (exit %s): %s",
                container,
                result.returncode,
                result.stderr.strip(),
            )
            return False
        return True
    except (subprocess.SubprocessError, FileNotFoundError) as exc:
        logger.error("docker start %s error: %s", container, exc)
        return False


def ensure_service_up(
    container: str,
    health_url: str,
    api_key: Optional[str] = None,
    timeout: int = DEFAULT_TIMEOUT,
    poll_interval: int = DEFAULT_POLL_INTERVAL,
) -> bool:
    """S'assure que le service est UP et healthy ; le (re)démarre si besoin.

    Étapes :
      1. Fast-path : si `/health` répond 200, retour immédiat (service déjà actif).
      2. Sinon : `docker start <container>` puis poll de `/health` jusqu'à 200
         ou `timeout` écoulé.
      3. Retourne True si healthy dans le délai, False sinon (l'appelant gère
         l'erreur — pas d'exception pour laisser place à un fallback métier).

    Préserve l'économie VRAM : le monitor re-stoppera le service après
    `idle_timeout` s'il reste inactif.
    """
    if probe_health(health_url, api_key):
        logger.info("Service %s already healthy (fast-path)", container)
        return True

    logger.info("Service %s down/idle — issuing docker start", container)
    if not docker_start(container):
        return False

    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if probe_health(health_url, api_key):
            logger.info("Service %s healthy after warm-up", container)
            return True
        time.sleep(poll_interval)

    logger.error(
        "Service %s not healthy within %ss after docker start", container, timeout
    )
    return False


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Réveille un service GenAI idle-stoppé à la demande (#2982)."
    )
    parser.add_argument("container", help="Nom du container Docker (ex: musicgen-api)")
    parser.add_argument(
        "--health-url",
        required=True,
        help="URL de health (ex: http://localhost:8192/health)",
    )
    parser.add_argument(
        "--api-key",
        default=None,
        help="Clé API (Bearer) si le service a l'auth active (lus depuis .env sinon)",
    )
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="Logs détaillés (INFO+)"
    )
    args = parser.parse_args()

    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format="%(asctime)s [%(levelname)s] %(message)s",
    )

    ok = ensure_service_up(
        args.container,
        args.health_url,
        api_key=args.api_key,
        timeout=args.timeout,
        poll_interval=args.poll_interval,
    )
    if ok:
        print(f"OK: {args.container} is up at {args.health_url}")
        return 0
    # La cause précise (docker start failed vs warm-up timeout) est dans les logs.
    print(
        f"FAIL: {args.container} could not be brought up "
        f"(see logs above for docker start error or warm-up timeout of {args.timeout}s)",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
