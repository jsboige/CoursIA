"""Conftest : ajoute MyIA.AI.Notebooks/IIT/ICT-Series au sys.path pour les tests."""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ICT_PATH = REPO_ROOT.parent / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series"
if str(ICT_PATH) not in sys.path:
    sys.path.insert(0, str(ICT_PATH))