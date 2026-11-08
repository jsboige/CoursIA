# Portage verbatim de `argumentation_analysis/services/ai_shield/__init__.py` depuis le projet
# 2025-Epita-Intelligence-Symbolique
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Commit source : 713927e1f4ce292d6532fc3f5457afa5ad3c662c (2026-10-28).
#
# CoursIA modification : le prefixe d'import `argumentation_analysis.services.ai_shield` est reecrit en `argumentation_lib.ai_shield` (le shim du depot resout les imports amont ; cf `argumentation_lib/_paths.py`). Aucune autre ligne n'est modifiee.
#
# Portage dans le cadre de l'issue #23163 (serie Argument_Analysis completee sur
# CoursIA) — le depot EPITA reste le cadre experimental, pas la destination.
# Registre des copies verbatim : `argumentation_lib/NOTICE-EPITA`.
"""AI Shield — adversarial protection framework for LLM pipelines.

Modular firewall/filter system that validates inputs before LLM calls
and filters outputs for sensitive information leaks.

Recreated from project 2.5.6 soutenance description (Schweitzer, Ruff, Hantzberg).

Layers:
  1. Heuristic — regex/keyword validation (fast, no LLM cost)
  2. LLM Validator — jailbreak/bias detection via LLM
  3. Output Filter — prevents sensitive information leaks

Usage:
    from argumentation_analysis.services.ai_shield import Shield, load_preset

    shield = load_preset("basic")  # heuristic only
    result = shield.validate_input("some user input")
    if result.blocked:
        print(f"Blocked: {result.reason}")
"""

from argumentation_lib.ai_shield.shield import (
    Shield,
    ShieldResult,
    ShieldLayer,
)
from argumentation_lib.ai_shield.presets import (
    PRESET_FAIL_OPEN,
    load_preset,
    resolve_fail_open,
)

__all__ = [
    "Shield",
    "ShieldResult",
    "ShieldLayer",
    "load_preset",
    "resolve_fail_open",
    "PRESET_FAIL_OPEN",
]
