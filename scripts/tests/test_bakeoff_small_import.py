"""Test d'import de bakeoff_small -- garantie de l'invocation documentee (#17661).

Le docstring de measure_chatterbox_mtl_v3.py documente :

    cd .../prosody_lab/bakeoff_small
    python -m measure_chatterbox_mtl_v3 ...

L'import tardif `from bakeoff_small.bake import compute_wer_for_wav` exige que
prosody_lab (parent du package) soit sur sys.path -- pas seulement bakeoff_small.
Ces tests rejouent la chaine d'import exacte du script corrige, sans dependre de
torch ni d'aucune dependance GPU (imports top-level du package : stdlib seule).
"""

from __future__ import annotations

import importlib
import sys
from pathlib import Path

BAKEDIR = (
    Path(__file__).resolve().parents[2]
    / "MyIA.AI.Notebooks"
    / "GenAI"
    / "Audio"
    / "04-Applications"
    / "v4"
    / "prosody_lab"
    / "bakeoff_small"
)
PROSODY_LAB = BAKEDIR.parent


def _with_paths(paths):
    added = [p for p in paths if str(p) not in sys.path]
    for p in added:
        sys.path.insert(0, str(p))
    try:
        yield
    finally:
        for p in added:
            sys.path.remove(str(p))
        for mod in ("bakeoff_small", "bakeoff_small.bake", "measure_chatterbox_mtl_v3"):
            sys.modules.pop(mod, None)


def test_docstring_invocation_import_chain():
    """Le script corrige insere parent.parent PUIS parent ; l'import bakeoff_small.bake doit resoudre."""
    for _ in _with_paths([PROSODY_LAB, BAKEDIR]):
        bake = importlib.import_module("bakeoff_small.bake")
        assert callable(bake.compute_wer_for_wav), "compute_wer_for_wav doit etre importable"


def test_measure_module_importable_from_package_dir():
    """`python -m measure_chatterbox_mtl_v3` depuis bakeoff_small : le module doit s'importer (top = stdlib)."""
    for _ in _with_paths([BAKEDIR]):
        mod = importlib.import_module("measure_chatterbox_mtl_v3")
        assert mod is not None
