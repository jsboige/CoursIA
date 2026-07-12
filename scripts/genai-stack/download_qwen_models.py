#!/usr/bin/env python3
"""
download_qwen_models.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py models download-qwen' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python download_qwen_models.py
    python download_qwen_models.py --dest /path/to/models
    python download_qwen_models.py --docker
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.models import main_download_qwen

if __name__ == "__main__":
    main_download_qwen()
