"""Conftest qui charge le package ``ict/`` via importlib au plus tot,
pour contourner le bug du pytest.ini racine (--import-mode=importlib).

L'import se fait ici, ce qui peuple sys.modules['ict'] ; quand pytest
charge ensuite les modules de test, le module 'ict' est deja connu
de importlib (meme en mode ``importlib``) et accessible.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_ICT_PKG = Path(__file__).resolve().parent.parent
_ICT_STR = str(_ICT_PKG)
_ICT_INIT = _ICT_PKG / "__init__.py"

# Charger ict/__init__.py explicitement via spec pour bypasser
# --import-mode=importlib.
if "ict" not in sys.modules:
    spec = importlib.util.spec_from_file_location(
        "ict",
        _ICT_INIT,
        submodule_search_locations=[_ICT_STR],
    )
    if spec is None or spec.loader is None:
        raise RuntimeError(f"impossible de loader {_ICT_INIT}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules["ict"] = mod
    spec.loader.exec_module(mod)