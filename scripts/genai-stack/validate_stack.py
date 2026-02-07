#!/usr/bin/env python3
"""
validate_stack.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py validate <options>' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python validate_stack.py --full
    python validate_stack.py --auth-only
    python validate_stack.py --nunchaku
    python validate_stack.py --notebooks
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.validate import main

if __name__ == "__main__":
    main()
