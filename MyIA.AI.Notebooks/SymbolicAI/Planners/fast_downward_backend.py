"""Un seul point d'appel a Fast Downward pour les carnets Python de Planners.

Pendant Python de ``FastDownwardBackend.cs`` (jumeaux C#). ``plan`` rend le dictionnaire
``{returncode, stdout, stderr}``, le contrat de ``POST /plan`` du conteneur
``coursia-fast-downward``. Le moteur est choisi une fois par session :

1. le service Docker (http://localhost:8200), s'il repond a ``/health`` ;
2. sinon le pilote ``fast-downward.py`` que livre le paquet ``up-fast-downward``
   (wheels compilees pour Linux, macOS et Windows), lance par l'interpreteur courant
   dans un dossier temporaire. Docker n'est donc pas requis.

Sans service ni paquet, ``plan`` leve ``RuntimeError`` avec la commande d'installation :
pas de sortie de substitution. Les chemins machine ne sont jamais imprimes.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from typing import Optional

SERVICE_URL = "http://localhost:8200"

_resolved = False
_service: Optional[dict] = None
_driver: Optional[str] = None
_local_version: Optional[str] = None


def _probe_service() -> Optional[dict]:
    try:
        with urllib.request.urlopen(f"{SERVICE_URL}/health", timeout=2) as resp:
            if resp.status != 200:
                return None
            try:
                return json.loads(resp.read().decode("utf-8"))
            except ValueError:
                return {}
    except (urllib.error.URLError, ConnectionError, OSError):
        return None


def _locate_driver() -> Optional[str]:
    try:
        import up_fast_downward
    except ImportError:
        return None
    path = os.path.join(os.path.dirname(up_fast_downward.__file__), "downward", "fast-downward.py")
    return path if os.path.isfile(path) else None


def _read_local_version(driver: str) -> Optional[str]:
    try:
        out = subprocess.run([sys.executable, driver, "--version"], capture_output=True,
                             text=True, encoding="utf-8", errors="replace", timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    for line in out.stdout.splitlines():
        if line.startswith("Fast Downward"):
            return line.strip()
    return None


def _resolve() -> None:
    global _resolved, _service, _driver, _local_version
    if _resolved:
        return
    _resolved = True
    _service = _probe_service()
    if _service is not None:
        return
    _driver = _locate_driver()
    if _driver is not None:
        _local_version = _read_local_version(_driver)


def reset() -> None:
    """Oublie le moteur retenu : le prochain appel sonde a nouveau (conteneur demarre entre-temps)."""
    global _resolved, _service, _driver, _local_version
    _resolved, _service, _driver, _local_version = False, None, None, None


def available() -> bool:
    _resolve()
    return _service is not None or _driver is not None


def description() -> str:
    """Moteur retenu pour la session, en clair."""
    _resolve()
    if _service is not None:
        version = _service.get("version")
        name = f"Fast Downward {version}" if version else "Fast Downward"
        return f"{name}, service Docker coursia-fast-downward (port 8200)"
    if _driver is not None:
        return f"{_local_version or 'Fast Downward'}, plugin local up_fast_downward"
    return "aucun (ni service Docker sur le port 8200, ni paquet Python up-fast-downward)"


def plan(domain: str, problem: str, search: str = "astar(lmcut())", timeout: int = 60) -> dict:
    """Planifie et rend ``{returncode, stdout, stderr}``, comme ``POST /plan``."""
    _resolve()
    if _service is not None:
        payload = json.dumps({"domain": domain, "problem": problem, "search": search}).encode("utf-8")
        req = urllib.request.Request(f"{SERVICE_URL}/plan", data=payload,
                                     headers={"Content-Type": "application/json"}, method="POST")
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        return {"returncode": data.get("returncode", -1),
                "stdout": data.get("stdout", ""), "stderr": data.get("stderr", "")}
    if _driver is None:
        raise RuntimeError("Fast Downward indisponible : demarrer le conteneur coursia-fast-downward "
                           "(port 8200) ou installer le paquet Python : pip install up-fast-downward")
    # Le pilote ecrit output.sas et sas_plan dans son dossier courant : un dossier
    # temporaire par appel garde l'arbre du depot propre.
    with tempfile.TemporaryDirectory(prefix="coursia-fd-") as work:
        for name, text in (("domain.pddl", domain), ("problem.pddl", problem)):
            with open(os.path.join(work, name), "w", encoding="utf-8") as fh:
                fh.write(text)
        try:
            out = subprocess.run([sys.executable, _driver, "domain.pddl", "problem.pddl", "--search", search],
                                 cwd=work, capture_output=True, text=True, encoding="utf-8",
                                 errors="replace", timeout=timeout)
        except subprocess.TimeoutExpired:
            return {"returncode": -1, "stdout": "", "stderr": f"delai de {timeout} s depasse"}
    return {"returncode": out.returncode, "stdout": out.stdout, "stderr": out.stderr}
