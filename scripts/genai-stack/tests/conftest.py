"""Shared fixtures for genai-stack tests."""

import sys
from pathlib import Path

# Add genai-stack root to sys.path so imports work
_genai_root = str(Path(__file__).resolve().parent.parent)
if _genai_root not in sys.path:
    sys.path.insert(0, _genai_root)
