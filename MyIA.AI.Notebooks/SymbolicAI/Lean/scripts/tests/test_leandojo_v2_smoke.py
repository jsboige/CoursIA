"""Smoke test LeanDojo-v2 -- volet A phase 1 (issue #18430).

Phase 1 = environnement dedie installe et MESURE :

  - paquet      : ``lean-dojo-v2==1.0.9`` (PyPI), licence MIT
                 (metadonnees PyPI ``license=MIT`` et README ``License:
                 MIT``, mesures le 2026-10-04 ; la discordance
                 Apache-2.0 / MIT signalee dans le body de #18430 est
                 resolue a la mesure : les deux sources disent MIT).
                 Divergence interne mesuree : ``lean_dojo_v2.__version__
                 == "1.0.0"`` alors que le paquet installe est 1.0.9 --
                 le pin de ce test lit ``importlib.metadata`` (version
                 du paquet), seule source fiable.
  - machine     : myia-ai-01, venv WSL ``~/venvs/leandojo-v2``,
                 Python 3.12.3 (fourchette requise >= 3.11)
  - pantograph  : ``pantograph==0.3.15`` depuis
                 ``git+https://github.com/stanford-centaur/PyPantograph``
                 (non exigé par les ``requires_dist`` de lean-dojo-v2,
                 requis pour le serveur RPC Lean -- cf. README
                 ``Installation``)

Contrainte mesuree : ``lean_dojo_v2/utils/constants.py:20`` exige
``GITHUB_ACCESS_TOKEN`` **a l'import** (``ValueError`` sinon). Ce test
charge le token comme ``test_leandojo_basic.py`` (env, puis
``scripts/tests/.env`` gitignored, puis ``gh auth token``) et SKIP
proprement si introuvable ou si l'env dedie est absent. Le verdict
d'installation vit dans l'execution de reference (WSL myia-ai-01,
collee dans le corps de la PR) : un skip CI n'est pas un faux vert,
il signale l'env absent, il ne le simule pas.

Les trainers CUDA restent hors phase 1 : verdict axe-5 INTRINSIC deja
documente dans ``agent_tests/prover/integration/leandojo_feasibility.py``.

Execution de reference (machine nommee) :

    wsl -d Ubuntu bash -lc \
        "~/venvs/leandojo-v2/bin/python -m pytest \
         /mnt/d/CoursIA-2-wt-18430/MyIA.AI.Notebooks/SymbolicAI/Lean/scripts/tests/test_leandojo_v2_smoke.py -v"
"""
from __future__ import annotations

import importlib.metadata
import os
import subprocess
import sys
from pathlib import Path

import pytest

# Versions epinglees a la mesure du 2026-10-04 (pip, venv WSL ai-01).
LEAN_DOJO_V2_VERSION = "1.0.9"
PANTOGRAPH_VERSION = "0.3.15"

_TESTS_DIR = Path(__file__).parent


def _load_github_token() -> bool:
    """Expose GITHUB_ACCESS_TOKEN sans jamais l'ecrire en dur (secrets-hygiene).

    Ordre : environnement, scripts/tests/.env (gitignored), .env parent,
    puis ``gh auth token``. Rend True si le token est disponible.
    """
    if os.environ.get("GITHUB_ACCESS_TOKEN"):
        return True
    for env_path in (_TESTS_DIR / ".env", _TESTS_DIR.parent / ".env"):
        if env_path.exists():
            for line in env_path.read_text(encoding="utf-8", errors="replace").splitlines():
                line = line.strip()
                if line.startswith("GITHUB_ACCESS_TOKEN=") and "=" in line:
                    os.environ["GITHUB_ACCESS_TOKEN"] = line.split("=", 1)[1].strip()
                    return True
                if line.startswith("GITHUB_TOKEN=") and "GITHUB_ACCESS_TOKEN" not in os.environ:
                    os.environ["GITHUB_ACCESS_TOKEN"] = line.split("=", 1)[1].strip()
                    return True
    try:
        result = subprocess.run(
            ["gh", "auth", "token"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
        )
        if result.returncode == 0 and result.stdout.strip():
            os.environ["GITHUB_ACCESS_TOKEN"] = result.stdout.strip()
            return True
    except (OSError, subprocess.SubprocessError):
        pass
    return False


def _module():
    """Importe lean_dojo_v2 ou skip proprement (env dedie / token absent)."""
    if not _load_github_token():
        pytest.skip("GITHUB_ACCESS_TOKEN introuvable (env/.env/gh) -- requis a l'import de lean_dojo_v2")
    try:
        import lean_dojo_v2  # noqa: F401
    except ImportError as exc:
        pytest.skip(f"env dedie absent (paquet lean-dojo-v2 non installe) : {exc}")
    except ValueError as exc:
        pytest.skip(f"import lean_dojo_v2 bloque : {exc}")
    import lean_dojo_v2

    return lean_dojo_v2


def test_version_pinned():
    """Le paquet installe porte exactement la version epinglee.

    Lit ``importlib.metadata`` (version du paquet pip) : la constante
    interne ``__version__`` vaut "1.0.0" pour le paquet 1.0.9 mesure
    le 2026-10-04 -- divergence upstream, on ne pinne pas dessus.
    """
    _module()
    installed = importlib.metadata.version("lean-dojo-v2")
    assert installed == LEAN_DOJO_V2_VERSION, (
        f"lean-dojo-v2=={installed} != {LEAN_DOJO_V2_VERSION} epingle : "
        "re-mesurer et mettre a jour le pin (jamais suivre main, cf. #18430)"
    )


def test_license_metadata_is_mit():
    """La metadonnee License du paquet installe rend MIT (mesure PyPI).

    Clarifie l'acceptance #18430 : les metadonnees PyPI du 2026-10-04
    rendent license=MIT, coherent avec le README. Si une future version
    change de licence, ce test le revele avant toute adoption.
    """
    meta = importlib.metadata.metadata("lean-dojo-v2")
    license_field = meta.get("License", "") or ""
    classifiers = " ".join(c for c in (meta.get_all("Classifier") or []) if "License" in c)
    combined = f"{license_field} {classifiers}"
    assert "MIT" in combined, (
        f"License inattendue dans les metadonnees: {combined.strip()!r} -- "
        "re-verifier avant d'utiliser le paquet"
    )


def test_dynamic_database_importable():
    """Volet A composant 1 : la base dynamique de theoremes est atteignable."""
    _module()
    from lean_dojo_v2.database import DynamicDatabase

    assert callable(DynamicDatabase)
    assert callable(getattr(DynamicDatabase, "trace_repository", None)), (
        "DynamicDatabase.trace_repository absent -- API en derive par rapport "
        "au README mesure (Quick Start) : re-mesurer avant le carnet compagnon"
    )


def test_provers_importable():
    """Volet A composant 2 : les provers Pantograph sont importables (sans GPU)."""
    _module()
    from lean_dojo_v2.prover import ExternalProver, HFProver

    assert callable(ExternalProver)
    assert callable(HFProver)


def test_agents_importable():
    """Volet A composant 3 : les agents orchestrateurs sont importables."""
    _module()
    from lean_dojo_v2.agent.external_agent import ExternalAgent
    from lean_dojo_v2.agent.hf_agent import HFAgent

    assert callable(ExternalAgent)
    assert callable(HFAgent)


def test_pantograph_importable():
    """Le serveur RPC Pantograph (installe depuis Git) est importable, version epinglee."""
    panto = pytest.importorskip("pantograph")
    from pantograph.server import Server

    assert callable(Server)
    installed = importlib.metadata.version("pantograph")
    assert installed == PANTOGRAPH_VERSION, (
        f"pantograph=={installed} != {PANTOGRAPH_VERSION} epingle (installe depuis Git) : "
        "re-mesurer et mettre a jour le pin"
    )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
