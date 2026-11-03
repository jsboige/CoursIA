# Portage verbatim de `argumentation_analysis/services/ai_shield/layers/__init__.py` depuis le projet
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
"""Shield validation layers."""

from argumentation_lib.ai_shield.layers.heuristic import HeuristicLayer
from argumentation_lib.ai_shield.layers.llm_validator import (
    LLMValidatorLayer,
)
from argumentation_lib.ai_shield.layers.output_filter import (
    OutputFilterLayer,
)

__all__ = ["HeuristicLayer", "LLMValidatorLayer", "OutputFilterLayer"]
