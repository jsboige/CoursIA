#!/usr/bin/env python3
"""
download_nunchaku_model.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py models download-nunchaku' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python download_nunchaku_model.py
    python download_nunchaku_model.py --model lightning-8step-r128
    python download_nunchaku_model.py --list
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.models import main_download_nunchaku

if __name__ == "__main__":
    main_download_nunchaku()
