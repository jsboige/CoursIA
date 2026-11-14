#!/usr/bin/env python3
"""Lance un notebook existant avec Jupyter Kernel Gateway (API notebook-http).

Le notebook porte le contrat HTTP au moyen des annotations Kernel Gateway. Cet
outil transmet le seed tel quel : il ne reconstitue ni ne réécrit ses routes.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import secrets
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any, Sequence

GATEWAY_MODULE = "kernel_gateway"
SWAGGER_PATH = "/_api/spec/swagger.json"
EXIT_PREFLIGHT = 2
EXIT_PROBE = 3


def preflight(notebook: Path) -> list[str]:
    """Vérifie le seed JSON et la dépendance avant le lancement du serveur."""
    problems: list[str] = []
    if not notebook.is_file():
        return [f"notebook introuvable : {notebook}"]
    try:
        with notebook.open(encoding="utf-8") as source:
            document = json.load(source)
        if not isinstance(document, dict) or not isinstance(document.get("cells"), list):
            problems.append(f"notebook invalide : objet Jupyter avec une liste cells attendu ({notebook})")
        elif not any(cell.get("cell_type") == "code" for cell in document["cells"] if isinstance(cell, dict)):
            problems.append(f"notebook sans cellule de code : {notebook}")
        else:
            metadata = document.get("metadata", {})
            kernelspec = metadata.get("kernelspec", {}) if isinstance(metadata, dict) else {}
            kernel_name = kernelspec.get("name") if isinstance(kernelspec, dict) else None
            if not isinstance(kernel_name, str) or not kernel_name.strip():
                problems.append(f"kernelspec.name absent du notebook : {notebook}")
            else:
                try:
                    from jupyter_client.kernelspec import KernelSpecManager

                    if kernel_name not in KernelSpecManager().find_kernel_specs():
                        problems.append(
                            f"kernel Jupyter absent : {kernel_name!r} "
                            "(installer le kernel déclaré dans le notebook, par exemple ipykernel pour python3)"
                        )
                except ImportError:
                    # Jupyter Kernel Gateway dépend de jupyter-client, mais
                    # garder ce diagnostic explicite si l'installation est cassée.
                    problems.append("dépendance absente : jupyter_client (réinstaller jupyter_kernel_gateway)")
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        problems.append(f"notebook illisible ou JSON invalide : {notebook} ({exc})")

    try:
        available = importlib.util.find_spec(GATEWAY_MODULE) is not None
    except (ImportError, ValueError):
        available = False
    if not available:
        problems.append(
            "dépendance absente : module kernel_gateway introuvable "
            "(installer le paquet PyPI jupyter_kernel_gateway dans cet environnement)"
        )
    return problems


def build_command(notebook: Path, host: str, port: int) -> list[str]:
    """Construit la commande avec un seed relatif au répertoire du notebook."""
    return [
        sys.executable,
        "-m",
        GATEWAY_MODULE,
        "--KernelGatewayApp.api=kernel_gateway.notebook_http",
        f"--KernelGatewayApp.seed_uri={notebook.name}",
        f"--KernelGatewayApp.ip={host}",
        f"--KernelGatewayApp.port={port}",
        "--KernelGatewayApp.port_retries=0",
        "--JupyterWebsocketPersonality.list_kernels=True",
    ]


def _openapi(base_url: str, token: str | None, timeout: float) -> tuple[int | None, Any]:
    headers = {"Accept": "application/json"}
    if token is not None:
        headers["Authorization"] = f"token {token}"
    request = urllib.request.Request(base_url + SWAGGER_PATH, headers=headers, method="GET")
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            spec = json.loads(response.read().decode("utf-8")) if response.status == 200 else None
            return response.status, spec
    except urllib.error.HTTPError as exc:
        return exc.code, None
    except (OSError, urllib.error.URLError, json.JSONDecodeError, UnicodeError):
        return None, None


def _route_is_registered(base_url: str, path: str, method: str, token: str, timeout: float) -> bool | None:
    status, spec = _openapi(base_url, token, timeout)
    if status is None or status != 200:
        return None
    routes: Any = spec.get("paths", {}) if isinstance(spec, dict) else {}
    methods = routes.get(path, {}) if isinstance(routes, dict) else {}
    return isinstance(methods, dict) and method.lower() in methods


def _base_url(host: str, port: int) -> str:
    authority = f"[{host}]" if ":" in host else host
    return f"http://{authority}:{port}"


def _probe(base_url: str, method: str, path: str, body: Any, token: str, timeout: float) -> tuple[int, Any]:
    data = None if body is None else json.dumps(body).encode("utf-8")
    headers = {"Accept": "application/json"}
    headers["Authorization"] = f"token {token}"
    if data is not None:
        headers["Content-Type"] = "application/json"
    request = urllib.request.Request(base_url + path, data=data, headers=headers, method=method)
    with urllib.request.urlopen(request, timeout=timeout) as response:
        payload = response.read().decode("utf-8")
        return response.status, json.loads(payload)


def _stop(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def _run_probe(
    command: list[str], notebook: Path, host: str, port: int,
    method: str, path: str, body: Any, timeout: float,
) -> int:
    base_url = _base_url(host, port)
    deadline = time.monotonic() + timeout
    openapi_seen = False
    token = secrets.token_urlsafe(32)
    child_environment = os.environ.copy()
    child_environment["KG_AUTH_TOKEN"] = token
    with tempfile.TemporaryFile(mode="w+b") as log:
        process = subprocess.Popen(
            command, cwd=notebook.parent, env=child_environment, stdout=log, stderr=subprocess.STDOUT
        )
        try:
            while time.monotonic() < deadline:
                if process.poll() is not None:
                    break
                registered = _route_is_registered(
                    base_url, path, method, token, min(1.0, max(0.1, deadline - time.monotonic()))
                )
                openapi_seen = openapi_seen or registered is not None
                if registered:
                    remaining = max(0.1, deadline - time.monotonic())
                    unauthenticated_status, _ = _openapi(base_url, None, remaining)
                    if unauthenticated_status != 401:
                        print(
                            "[kernel-gateway] identité du serveur non confirmée : "
                            f"la sonde sans jeton devait recevoir 401, reçu {unauthenticated_status}",
                            file=sys.stderr,
                        )
                        return EXIT_PROBE
                    status, result = _probe(base_url, method, path, body, token, remaining)
                    print(f"[kernel-gateway] HTTP {status} {method} {path}")
                    print(json.dumps(result, ensure_ascii=False, sort_keys=True))
                    return 0 if 200 <= status < 300 else EXIT_PROBE
                time.sleep(0.2)
            if openapi_seen:
                reason = f"la méthode {method} sur {path} n'a pas été enregistrée dans OpenAPI"
            else:
                reason = "le descripteur OpenAPI n'est pas devenu disponible"
            print(f"[kernel-gateway] {reason} avant le délai de {timeout:g} s", file=sys.stderr)
            log.seek(0)
            output = log.read().decode("utf-8", errors="replace")
            if output:
                print(output[-6000:], file=sys.stderr)
            return EXIT_PROBE
        except (OSError, urllib.error.URLError, json.JSONDecodeError, UnicodeError) as exc:
            print(f"[kernel-gateway] échec de la sonde HTTP {method} {path} : {exc}", file=sys.stderr)
            log.seek(0)
            output = log.read().decode("utf-8", errors="replace")
            if output:
                print(output[-6000:], file=sys.stderr)
            return EXIT_PROBE
        finally:
            _stop(process)


def _loopback_host(value: str) -> str:
    # L'outil vise les services locaux ; une adresse publique nécessite une
    # configuration de déploiement explicite du gateway, hors de ce lanceur.
    if value not in {"127.0.0.1", "localhost", "::1"}:
        raise argparse.ArgumentTypeError("l'hôte doit être loopback (127.0.0.1, localhost ou ::1)")
    return value


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Lance un notebook annoté avec le Kernel Gateway officiel (mode notebook-http)."
    )
    parser.add_argument("notebook", type=Path, help="carnet existant dont les annotations définissent l'API")
    parser.add_argument("--host", type=_loopback_host, default="127.0.0.1", help="adresse loopback (défaut : 127.0.0.1)")
    parser.add_argument("--port", type=int, default=8899, help="port HTTP (défaut : 8899)")
    parser.add_argument("--check-only", action="store_true", help="vérifie le seed et la dépendance, sans démarrer")
    parser.add_argument("--probe-path", help="avec --probe-json, teste cette route après démarrage")
    parser.add_argument("--probe-json", help="corps JSON envoyé en POST ; la route doit être enregistrée dans OpenAPI")
    parser.add_argument("--probe-method", choices=("GET", "POST"), default="POST", help="méthode de la sonde (défaut : POST)")
    parser.add_argument("--probe-timeout", type=float, default=30.0, help="délai de démarrage et de réponse (secondes)")
    args = parser.parse_args(argv)

    if not 1 <= args.port <= 65535:
        parser.error("--port doit être compris entre 1 et 65535")
    if args.probe_timeout <= 0:
        parser.error("--probe-timeout doit être strictement positif")
    if args.probe_json is not None and args.probe_path is None:
        parser.error("--probe-json exige --probe-path")
    if args.probe_path is not None and (not args.probe_path.startswith("/") or args.probe_path.startswith("//")):
        parser.error("--probe-path doit être un chemin HTTP absolu, par exemple /texte/extract")
    if args.probe_method == "GET" and args.probe_json is not None:
        parser.error("une sonde GET n'accepte pas --probe-json")
    if args.probe_method == "POST" and args.probe_path is not None and args.probe_json is None:
        parser.error("une sonde POST exige --probe-json (un objet JSON, par exemple '{}')")

    notebook = args.notebook.expanduser().resolve()
    problems = preflight(notebook)
    if problems:
        for problem in problems:
            print(f"[kernel-gateway] {problem}", file=sys.stderr)
        print("[kernel-gateway] lancement refusé avant le démarrage du serveur", file=sys.stderr)
        return EXIT_PREFLIGHT

    if args.check_only:
        print(f"[kernel-gateway] pré-vol OK : {notebook}")
        return 0

    body = None
    if args.probe_json is not None:
        try:
            body = json.loads(args.probe_json)
        except json.JSONDecodeError as exc:
            parser.error(f"--probe-json invalide : {exc}")
    command = build_command(notebook, args.host, args.port)
    if args.probe_path is not None:
        return _run_probe(
            command, notebook, args.host, args.port,
            args.probe_method, args.probe_path, body, args.probe_timeout,
        )

    print(f"[kernel-gateway] notebook : {notebook}")
    print(f"[kernel-gateway] écoute   : {_base_url(args.host, args.port)}")
    print("[kernel-gateway] routes définies par les annotations du notebook ; Ctrl-C pour arrêter")
    try:
        return subprocess.call(command, cwd=notebook.parent)
    except OSError as exc:
        print(f"[kernel-gateway] démarrage impossible : {exc}", file=sys.stderr)
        return EXIT_PREFLIGHT


if __name__ == "__main__":
    sys.exit(main())
