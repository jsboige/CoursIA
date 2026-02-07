#!/usr/bin/env python3
"""
setup_z_image.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py models setup-zimage' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python setup_z_image.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.models import main_setup_zimage

if __name__ == "__main__":
    main_setup_zimage()
