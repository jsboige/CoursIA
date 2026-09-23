"""Conftest : ajoute scripts/ au sys.path pour les imports des tests."""
import sys
from pathlib import Path

# Ajoute scripts/ (parent de tests/) au sys.path pour permettre
# `import roosync_archive_backfill` direct dans les tests.
_SCRIPTS_DIR = Path(__file__).resolve().parent.parent
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))
