#!/usr/bin/env python3
"""
docker_manager.py - Wrapper de retrocompatibilite

DEPRECATION: Utiliser 'genai.py docker <action>' a la place.

Ce script conserve la compatibilite avec les appels existants:
    python docker_manager.py status
    python docker_manager.py start comfyui-qwen
    python docker_manager.py test --remote
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from commands.docker import main

if __name__ == "__main__":
    main()
