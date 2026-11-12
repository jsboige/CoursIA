#!/usr/bin/env python3
"""Point d'entrée compatible ; implémentation dans scripts/epic/."""
from pathlib import Path
import sys

_impl = Path(__file__).resolve().parent / "epic" / "epic_neglect_sweep.py"
sys.path.insert(0, str(_impl.parent.parent))
__file__ = str(_impl)
exec(compile(_impl.read_bytes(), __file__, "exec"))
