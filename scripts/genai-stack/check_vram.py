#!/usr/bin/env python3
"""
check_vram.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py gpu' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python check_vram.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.gpu import main

if __name__ == "__main__":
    main()
