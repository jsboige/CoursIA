"""Conftest : route `ict` pour les tests hashlife (#25381, acceptance 4).

Motif ecrit -- la suite reste hermetique sur bare checkout : le job
scripts-tests.yml qui joue `scripts/hashlife/tests` ne fait PAS
`pip install` du package ict (cf. commentaire du job : suite jouee depuis
le seul layout du checkout). On prefere donc un `ict` deja installe
(voie contractuelle #25381, `pip install -e ICT-Series`) s'il existe,
et on replie sur le chemin du checkout sinon -- les deux mondes restent
verts, CI sans install comme poste avec install editable.
"""
from __future__ import annotations

import sys
from pathlib import Path

try:  # ict installe ? (pip install -e, voie contractuelle #25381)
    import ict  # noqa: F401
except ImportError:  # repli hermetique : chemin du checkout
    REPO_ROOT = Path(__file__).resolve().parents[2]
    ICT_PATH = REPO_ROOT.parent / "MyIA.AI.Notebooks" / "IIT" / "ICT-Series"
    if str(ICT_PATH) not in sys.path:
        sys.path.insert(0, str(ICT_PATH))
