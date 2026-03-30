#!/usr/bin/env python3
"""
list_nodes.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py models list-nodes' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python list_nodes.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.models import list_nodes

if __name__ == "__main__":
    list_nodes()
