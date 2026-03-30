#!/usr/bin/env python3
"""
validate_notebooks.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py notebooks <options>' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python validate_notebooks.py
    python validate_notebooks.py <target>
    python validate_notebooks.py --cleanup
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.notebooks import main

if __name__ == "__main__":
    main()
