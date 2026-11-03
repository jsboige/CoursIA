# Portage verbatim de `argumentation_analysis/services/ai_shield/presets.py` depuis le projet
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
"""Shield presets — pre-configured layer combinations.

Based on soutenance description:
- basic: Heuristic only (fast, zero cost)
- advanced: All layers (heuristic + LLM + output filter)
- output_only: Output filter only (for post-LLM validation)
- strict: All layers with lower thresholds, and the only profile whose
  declared policy is fail-closed (#2144)
"""

from typing import Dict, Optional

from argumentation_lib.ai_shield.shield import Shield
from argumentation_lib.ai_shield.layers.heuristic import HeuristicLayer
from argumentation_lib.ai_shield.layers.llm_validator import (
    LLMValidatorLayer,
)
from argumentation_lib.ai_shield.layers.output_filter import (
    OutputFilterLayer,
)

# Politique fail-open déclarée par preset — SOURCE UNIQUE (#2144).
# `fail_open=None` signifie « la politique déclarée ici ». La sémantique d'un
# preset vit à un seul endroit pour que les portes d'entrée (CLI, REST
# workflow, endpoint direct) ne puissent pas diverger : `strict` est le seul
# profil dont la garantie est « ne laisse rien passer en cas de panne ».
PRESET_FAIL_OPEN: Dict[str, bool] = {
    "basic": True,
    "advanced": True,
    "output_only": True,
    "strict": False,
}


def resolve_fail_open(preset_name: str, fail_open: Optional[bool] = None) -> bool:
    """Politique fail-open effective : l'explicite prime, sinon la déclaration du preset.

    Raises:
        ValueError: preset inconnu et aucune politique explicite — on refuse de
            deviner la politique d'un preset qui n'existe pas.
    """
    if fail_open is not None:
        return fail_open
    if preset_name not in PRESET_FAIL_OPEN:
        raise ValueError(
            f"Unknown preset '{preset_name}'. "
            f"Available: {', '.join(PRESET_FAIL_OPEN)}"
        )
    return PRESET_FAIL_OPEN[preset_name]


def load_preset(
    preset_name: str = "basic",
    api_key: Optional[str] = None,
    fail_open: Optional[bool] = None,
) -> Shield:
    """Load a pre-configured shield preset.

    Args:
        preset_name: "basic", "advanced", "output_only", or "strict".
        api_key: OpenAI API key for LLM validator layer.
        fail_open: Tri-state (#2144). None (default) = the preset's declared
            policy in PRESET_FAIL_OPEN (`strict` fails closed, the others fail
            open). True/False overrides it for any preset, `strict` included —
            the argument used to be silently ignored for `strict`.

    Returns:
        Configured Shield instance.
    """
    effective_fail_open = resolve_fail_open(preset_name, fail_open)

    if preset_name == "basic":
        return Shield(
            name="basic",
            fail_open=effective_fail_open,
            layers=[
                HeuristicLayer(threshold=0.5),
            ],
        )

    elif preset_name == "advanced":
        return Shield(
            name="advanced",
            fail_open=effective_fail_open,
            layers=[
                HeuristicLayer(threshold=0.5),
                LLMValidatorLayer(threshold=0.6, api_key=api_key),
                OutputFilterLayer(threshold=0.4),
            ],
        )

    elif preset_name == "output_only":
        return Shield(
            name="output_only",
            fail_open=effective_fail_open,
            layers=[
                OutputFilterLayer(threshold=0.4),
            ],
        )

    elif preset_name == "strict":
        return Shield(
            name="strict",
            fail_open=effective_fail_open,
            layers=[
                HeuristicLayer(threshold=0.3),  # Lower threshold = stricter
                LLMValidatorLayer(threshold=0.4, api_key=api_key),
                OutputFilterLayer(threshold=0.3),
            ],
        )

    else:
        raise ValueError(
            f"Unknown preset '{preset_name}'. "
            f"Available: {', '.join(PRESET_FAIL_OPEN)}"
        )
