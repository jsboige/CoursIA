#!/usr/bin/env python3
"""
genai_service.py - Client HTTP transparent pour services GenAI idle-monitores.

Contrepartie cote notebook de `service_wake.py` (#2982) : les 16 services GenAI
GPU sont auto-stoppes apres 20 min d'inactivite (liberation VRAM). Ce module
rend le **wake-on-demand transparent au niveau du code notebook** : un appel
`call_service("musicgen", "/v1/models")` reveille le service si besoin, attend
le warm-up, puis execute la requete HTTP. Le notebook n'a plus a connaitre
`service_wake.py` ni a gerer le 502 / connection-refused.

## Pourquoi un wrapper (approche wake-and-retry cote appelant)

- Aucun des 16 services ne configure `idle_action=sleep` (ils font `docker stop`).
  Un container stoppe n'a AUCUN listener sur son port -> le wake DOIT provenir
  de l'appelant (ou d'un proxy persistant, over-engineering pour une stack dev).
- Ce wrapper est **additif** : il ne modifie ni le monitor ni les services. Il
  reutilise `service_wake.ensure_service_up` (PR #2998, teste cold-start reel).
- **Economie VRAM preservee** : les services s'auto-stoppent toujours apres
  `idle_timeout` ; le wrapper ne lance `docker start` qu'en cas de demande reelle.

## Usage

    from helpers.genai_service import call_service

    # Drop-in pour requests.get("http://localhost:8192/v1/models")
    resp = call_service("musicgen", "/v1/models")
    models = resp.json()

    # POST avec payload + cle API
    resp = call_service("tts-kokoro", "/v1/audio/speech",
                        method="POST", json={"text": "bonjour"},
                        api_key=os.getenv("KOKORO_API_KEY"))

## Registre des services

Le registre mappe un nom court (notebook-friendly) au tuple
(container_docker, port_hote, chemin_health). Ports verifies via `docker inspect`
sur po-2023 + memoire `docker-infra-regrounded.md`.
"""

from __future__ import annotations

import logging
import os
import sys
from pathlib import Path
from typing import Any, Dict, Optional

import requests

logger = logging.getLogger("genai_service")

# Taille de fallback du registre : les services non listes necessitent un
# container+health explicites (call_service_generic ci-dessous).
DEFAULT_WAKE_TIMEOUT = 180
DEFAULT_POLL_INTERVAL = 2

# Registre des services GenAI : nom court -> (container, port, health_path).
# Ports verifies via `docker inspect` (containers UP) + memoire infra pour les
# services stoppes (demucs/kokoro/fish/qwen-asr/higgs non inspectables a froid).
SERVICE_REGISTRY: Dict[str, Dict[str, Any]] = {
    # Audio - TTS / STT / music / separation
    "musicgen":      {"container": "musicgen-api",    "port": 8192, "health": "/health"},
    "tts":           {"container": "tts-api",         "port": 8191, "health": "/health"},
    "tts-kokoro":    {"container": "tts-kokoro",      "port": 8191, "health": "/health"},
    "tts-fish":      {"container": "tts-fishaudio",   "port": 8197, "health": "/health"},
    "tts-gateway":   {"container": "tts-gateway",     "port": 8196, "health": "/health"},
    "higgs":         {"container": "higgs-tts",       "port": 8199, "health": "/health"},
    "whisper":       {"container": "whisper-api",     "port": 8190, "health": "/health"},
    "qwen-asr":      {"container": "qwen-asr-api",    "port": 8195, "health": "/health"},
    "demucs":        {"container": "demucs-api",      "port": 8193, "health": "/health"},
    # Image / Video
    "comfyui-qwen":  {"container": "comfyui-qwen",    "port": 8188, "health": "/system_stats"},
    "comfyui-video": {"container": "comfyui-video",   "port": 8189, "health": "/system_stats"},
    "forge":         {"container": "forge-turbo",     "port": 1111, "health": "/sdapi/v1/options"},
}


def _resolve_service(name: str) -> Dict[str, Any]:
    """Resout un nom court depuis le registre ; KeyError si inconnu."""
    if name not in SERVICE_REGISTRY:
        known = ", ".join(sorted(SERVICE_REGISTRY))
        raise KeyError(
            f"Service GenAI inconnu: {name!r}. Services enregistres: {known}. "
            f"Pour un service hors-registre, utiliser call_service_generic() "
            f"avec container+health explicites."
        )
    return SERVICE_REGISTRY[name]


def _import_ensure_service_up():
    """Importe ensure_service_up depuis service_wake (shared entre services).

    service_wake.py vit dans docker-configurations/services/shared/. On le rend
    importable en l'ajoutant au sys.path ; fallback gracieux si absent (les
    notebooks peuvent quand meme appeler des services deja UP, le wake sera juste
    saute avec un avertissement).
    """
    # Chemin 1 : service_wake a cote de ce module (shared/helpers/).
    here = Path(__file__).resolve().parent
    # Chemin 2 : docker-configurations/services/shared/ (emplacement canonique).
    repo_shared = here.parents[3] / "docker-configurations" / "services" / "shared"
    for candidate in (here, repo_shared):
        if (candidate / "service_wake.py").exists():
            sys.path.insert(0, str(candidate))
            try:
                from service_wake import ensure_service_up  # type: ignore
                return ensure_service_up
            except ImportError:
                continue
    logger.warning(
        "service_wake.py introuvable (cherche dans %s et %s). Le wake-on-demand "
        "est desactive : les services devront etre demarres manuellement.",
        here, repo_shared,
    )
    return None


def call_service_generic(
    container: str,
    port: int,
    path: str,
    method: str = "GET",
    health_path: str = "/health",
    api_key: Optional[str] = None,
    timeout: int = DEFAULT_WAKE_TIMEOUT,
    poll_interval: int = DEFAULT_POLL_INTERVAL,
    request_timeout: float = 30.0,
    **kwargs: Any,
) -> requests.Response:
    """Reveille si besoin puis execute une requete HTTP sur un service GenAI.

    Version "hors-registre" : container, port et health_path explicites. Pour
    les services connus, preferer `call_service()` (registre court).

    Args:
        container: Nom du container Docker (ex: "musicgen-api").
        port: Port hote expose (ex: 8192).
        path: Chemin de la requete (ex: "/v1/models").
        method: Methode HTTP ("GET", "POST", ...).
        health_path: Chemin du healthcheck (ex: "/health").
        api_key: Cle API (Bearer) si le service a l'auth active. Lu depuis .env
            via le nom "uppercase-container" si None (ex: MUSICGEN_API_API_KEY).
        timeout: Delai max de warm-up apres docker start (secondes).
        poll_interval: Intervalle de poll du healthcheck (secondes).
        request_timeout: Timeout de la requete HTTP finale (secondes).
        **kwargs: Args forwards a requests.request (json, data, headers, ...).

    Returns:
        requests.Response de la requete finale.

    Raises:
        RuntimeError: si le service ne peut etre reveille dans le delai.
    """
    base_url = f"http://localhost:{port}"
    health_url = f"{base_url}{health_path}"
    target_url = f"{base_url}{path}"

    # Cle API : explicite > .env derive du nom de container.
    if api_key is None:
        env_var = f"{container.upper().replace('-', '_')}_API_KEY"
        api_key = os.getenv(env_var)
    # Cas particulier : tts-gateway utilise TTS_GATEWAY_API_KEY (sans le _API).
    if api_key is None and "gateway" in container:
        api_key = os.getenv("TTS_GATEWAY_API_KEY")

    ensure_service_up = _import_ensure_service_up()
    if ensure_service_up is not None:
        if not ensure_service_up(
            container, health_url, api_key=api_key,
            timeout=timeout, poll_interval=poll_interval,
        ):
            raise RuntimeError(
                f"Service {container} non healthy apres {timeout}s de warm-up. "
                f"Verifiez `docker logs {container}`."
            )
    else:
        logger.warning("Wake desactive (service_wake absent) - requete directe.")

    headers = dict(kwargs.pop("headers", {}) or {})
    if api_key and "Authorization" not in headers:
        headers["Authorization"] = f"Bearer {api_key}"

    logger.info("%s %s (container=%s)", method, target_url, container)
    return requests.request(
        method, target_url, headers=headers, timeout=request_timeout, **kwargs
    )


def call_service(
    name: str,
    path: str,
    method: str = "GET",
    api_key: Optional[str] = None,
    **kwargs: Any,
) -> requests.Response:
    """Drop-in pour requests.get/post sur un service GenAI du registre.

    Reveille le service si idle-stopped, attend le warm-up, puis execute la
    requete. Le notebook n'a plus a gerer le 502 / connection-refused.

    Args:
        name: Nom court du service dans le registre (ex: "musicgen", "whisper").
        path: Chemin de la requete (ex: "/v1/models").
        method: Methode HTTP ("GET", "POST", ...).
        api_key: Cle API (Bearer). Si None, lu depuis .env.
        **kwargs: Args forwards a requests.request (json, data, ...).

    Returns:
        requests.Response de la requete finale.

    Example:
        >>> resp = call_service("musicgen", "/v1/models")
        >>> resp.status_code
        200
        >>> resp = call_service("tts-kokoro", "/v1/audio/speech",
        ...                     method="POST", json={"text": "bonjour"})
    """
    info = _resolve_service(name)
    return call_service_generic(
        container=info["container"],
        port=info["port"],
        path=path,
        method=method,
        health_path=info["health"],
        api_key=api_key,
        **kwargs,
    )


def list_services() -> Dict[str, Dict[str, Any]]:
    """Retourne une copie du registre des services connus (pour introspection)."""
    return dict(SERVICE_REGISTRY)


if __name__ == "__main__":
    # CLI minimal : `python genai_service.py musicgen /v1/models`
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    import argparse
    parser = argparse.ArgumentParser(description="Client GenAI avec wake-on-demand (#2982).")
    parser.add_argument("name", help="Nom court du service (ex: musicgen)")
    parser.add_argument("path", help="Chemin de la requete (ex: /v1/models)")
    parser.add_argument("-X", "--method", default="GET")
    args = parser.parse_args()
    r = call_service(args.name, args.path, method=args.method)
    print(f"{r.status_code} {args.method} {args.name}{args.path}")
    print(r.text[:500])
