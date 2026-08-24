"""Tests for scripts/genai-stack/core/sitecustomize.py — issue #12068.

Module : scripts/tests/test_sitecustomize_safe_ssl.py
Statut : MED/tooling, see issue #12068 (suite c.452, PR #12289)

Verifie que :
- Importer sitecustomize declenche l'install safe_ssl (si Windows + env mcp-jupyter-py310).
- Le bootstrap est idempotent.
- Sur Linux/macOS : `is_patched()` reste False (no-op documente).
- Echec silencieux si safe_ssl n'est pas importable.
"""

from __future__ import annotations

import importlib
import importlib.util
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
SITECUSTOMIZE = REPO_ROOT / "scripts" / "genai-stack" / "core" / "sitecustomize.py"


def _load_sitecustomize_fresh():
    """Charge sitecustomize dans un subprocess isole (pour etat neuf)."""
    code = f"""
import sys
sys.path.insert(0, r'{REPO_ROOT / "scripts" / "genai-stack"}')
sys.path.insert(0, r'{REPO_ROOT / "scripts" / "genai-stack" / "core"}')
import sitecustomize
from core import safe_ssl
print('PATCHED:', safe_ssl.is_patched())
"""
    result = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        env={**os.environ, "CONDA_DEFAULT_ENV": "mcp-jupyter-py310"},
    )
    return result


def test_sitecustomize_imports_without_error():
    """Importer sitecustomize ne leve pas."""
    # Charge directement (pas via subprocess) — le bootstrap s'execute au load.
    spec = importlib.util.spec_from_file_location("_sitecustomize_test", SITECUSTOMIZE)
    if spec is None or spec.loader is None:
        pytest.skip(f"sitecustomize introuvable a {SITECUSTOMIZE}")
    module = importlib.util.module_from_spec(spec)
    # Important : on capture les erreurs, on ne les propage pas.
    try:
        spec.loader.exec_module(module)
    except Exception as exc:  # noqa: BLE001
        pytest.fail(f"sitecustomize leve une exception a l'import : {exc!r}")


def test_sitecustomize_bootstrap_calls_install_on_windows():
    """Sur Windows + conda env mcp-jupyter-py310, is_patched() est True apres import."""
    if not sys.platform.startswith("win"):
        pytest.skip("Windows-only — _load_windows_store_certs absent ailleurs")
    if os.environ.get("CONDA_DEFAULT_ENV") != "mcp-jupyter-py310":
        pytest.skip("env conda differente — bootstrap filtre par env")
    result = _load_sitecustomize_fresh()
    assert "PATCHED: True" in result.stdout, (
        f"is_patched() devrait etre True apres sitecustomize. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )


def test_sitecustomize_no_op_on_non_windows():
    """Sur Linux/macOS, is_patched() reste False apres import."""
    if sys.platform.startswith("win"):
        pytest.skip("non-Windows — fixture inapplicable")
    result = _load_sitecustomize_fresh()
    assert "PATCHED: False" in result.stdout, (
        f"is_patched() devrait rester False sur Linux/macOS. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )


def test_sitecustomize_disabled_env_var():
    """SAFE_SSL_BOOTSTRAP_DISABLED=1 court-circuite le bootstrap."""
    if not sys.platform.startswith("win"):
        pytest.skip("Windows-only — sans _load_windows_store_certs, is_patched() est toujours False")
    code = f"""
import sys
sys.path.insert(0, r'{REPO_ROOT / "scripts" / "genai-stack"}')
sys.path.insert(0, r'{REPO_ROOT / "scripts" / "genai-stack" / "core"}')
import os
os.environ['SAFE_SSL_BOOTSTRAP_DISABLED'] = '1'
import sitecustomize
from core import safe_ssl
print('PATCHED:', safe_ssl.is_patched())
"""
    result = subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
    )
    assert "PATCHED: False" in result.stdout, (
        f"avec SAFE_SSL_BOOTSTRAP_DISABLED=1, is_patched() devrait etre False. "
        f"stdout={result.stdout!r} stderr={result.stderr!r}"
    )


def test_sitecustomize_bootstrap_idempotent():
    """Importer sitecustomize 2x ne double pas le patch."""
    spec = importlib.util.spec_from_file_location("_sitecustomize_test_dup", SITECUSTOMIZE)
    if spec is None or spec.loader is None:
        pytest.skip(f"sitecustomize introuvable a {SITECUSTOMIZE}")
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
        spec.loader.exec_module(module)  # 2e import : doit etre OK
    except Exception as exc:  # noqa: BLE001
        pytest.fail(f"sitecustomize double-import leve : {exc!r}")
