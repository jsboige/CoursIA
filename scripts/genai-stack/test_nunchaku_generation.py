#!/usr/bin/env python3
"""
test_nunchaku_generation.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py validate --nunchaku' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python test_nunchaku_generation.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.validate import main_nunchaku

if __name__ == "__main__":
    main_nunchaku()
