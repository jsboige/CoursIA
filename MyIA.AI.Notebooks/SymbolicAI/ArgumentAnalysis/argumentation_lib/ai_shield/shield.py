# Portage verbatim de `argumentation_analysis/services/ai_shield/shield.py` depuis le projet
# 2025-Epita-Intelligence-Symbolique
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Commit source : 713927e1f4ce292d6532fc3f5457afa5ad3c662c (2026-10-28).
#
# CoursIA modification : AUCUNE. Le fichier ci-dessous est identique octet pour octet a la copie amont (aucun import EPITA dans ce fichier).
#
# Portage dans le cadre de l'issue #23163 (serie Argument_Analysis completee sur
# CoursIA) — le depot EPITA reste le cadre experimental, pas la destination.
# Registre des copies verbatim : `argumentation_lib/NOTICE-EPITA`.
"""AI Shield — main shield class with configurable layer pipeline.

The Shield processes input through a sequence of validation layers,
each producing a score (0.0-1.0). If any layer score exceeds its
threshold, the input is blocked.
"""

import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional

logger = logging.getLogger(__name__)


@dataclass
class LayerResult:
    """Result from a single validation layer."""

    layer_name: str
    score: float  # 0.0 = safe, 1.0 = maximum threat
    passed: bool
    details: Dict[str, Any] = field(default_factory=dict)
    reason: str = ""
    # Nom du type de l'exception quand la couche a **levé** (#2144, item 3).
    # Sans ce champ, `ReasoningStarvedError` re-levée par le validateur LLM
    # n'arrivait ici que comme texte dans `details["error"]` : un appelant qui
    # n'inspecte pas le dictionnaire ne distinguait pas « couche en panne » de
    # « pas de menace », les deux rendant `passed=True` sous fail-open — le
    # mécanisme par lequel la garde #1929 était neutralisée en aval.
    # Dérivé à l'exécution (`type(e).__name__`), jamais une liste de noms.
    error_type: Optional[str] = None


@dataclass
class ShieldResult:
    """Aggregate result from all shield layers."""

    blocked: bool
    overall_score: float  # Max score across all layers
    layer_results: List[LayerResult] = field(default_factory=list)
    reason: str = ""

    @property
    def passed(self) -> bool:
        return not self.blocked


class ShieldLayer(ABC):
    """Abstract base class for shield validation layers."""

    def __init__(self, name: str, threshold: float = 0.7, enabled: bool = True):
        self.name = name
        self.threshold = threshold
        self.enabled = enabled

    @abstractmethod
    def validate(self, text: str, **kwargs) -> LayerResult:
        """Validate input text and return a LayerResult.

        Args:
            text: Input text to validate.
            **kwargs: Additional context (e.g., conversation history).

        Returns:
            LayerResult with score and pass/fail status.
        """
        ...

    def _make_result(
        self, score: float, details: Optional[Dict] = None, reason: str = ""
    ) -> LayerResult:
        """Helper to create a LayerResult with threshold check."""
        passed = score < self.threshold
        return LayerResult(
            layer_name=self.name,
            score=score,
            passed=passed,
            details=details or {},
            reason=reason if not passed else "",
        )


class Shield:
    """Configurable multi-layer input/output validation shield.

    Processes text through a pipeline of ShieldLayer instances.
    Blocks input if any layer score exceeds its configured threshold.

    Example:
        shield = Shield(layers=[HeuristicLayer(), LLMValidatorLayer()])
        result = shield.validate_input("user prompt here")
        if result.blocked:
            handle_block(result.reason)
    """

    def __init__(
        self,
        layers: Optional[List[ShieldLayer]] = None,
        name: str = "default",
        fail_open: bool = False,
    ):
        """Initialize shield with validation layers.

        Args:
            layers: Ordered list of validation layers.
            name: Shield configuration name.
            fail_open: If True, allow input when a layer errors.
                       If False (default), block on layer errors.
        """
        self.layers = layers or []
        self.name = name
        self.fail_open = fail_open

    def add_layer(self, layer: ShieldLayer) -> "Shield":
        """Add a layer to the pipeline (fluent API)."""
        self.layers.append(layer)
        return self

    def validate_input(self, text: str, **kwargs) -> ShieldResult:
        """Validate input text through all enabled layers.

        Args:
            text: Input text to validate.
            **kwargs: Additional context passed to each layer.

        Returns:
            ShieldResult with aggregate pass/fail and per-layer details.
        """
        layer_results = []
        max_score = 0.0

        for layer in self.layers:
            if not layer.enabled:
                continue

            try:
                result = layer.validate(text, **kwargs)
                layer_results.append(result)
                max_score = max(max_score, result.score)

                if not result.passed:
                    logger.info(
                        f"Shield[{self.name}] blocked by {layer.name}: "
                        f"score={result.score:.2f} > threshold={layer.threshold:.2f}"
                    )
                    return ShieldResult(
                        blocked=True,
                        overall_score=max_score,
                        layer_results=layer_results,
                        reason=result.reason or f"Blocked by {layer.name}",
                    )

            except Exception as e:
                logger.warning(f"Shield layer {layer.name} error: {e}")
                error_result = LayerResult(
                    layer_name=layer.name,
                    score=0.0 if self.fail_open else 1.0,
                    passed=self.fail_open,
                    details={"error": str(e)},
                    reason=f"Layer error: {e}",
                    error_type=type(e).__name__,
                )
                layer_results.append(error_result)
                if not self.fail_open:
                    return ShieldResult(
                        blocked=True,
                        overall_score=1.0,
                        layer_results=layer_results,
                        reason=f"Layer {layer.name} error: {e}",
                    )

        return ShieldResult(
            blocked=False,
            overall_score=max_score,
            layer_results=layer_results,
        )

    def validate_output(self, text: str, **kwargs) -> ShieldResult:
        """Validate LLM output through enabled layers.

        Same pipeline as validate_input but intended for output filtering.
        Layers can behave differently based on the 'direction' kwarg.
        """
        return self.validate_input(text, direction="output", **kwargs)

    def get_config(self) -> Dict[str, Any]:
        """Return shield configuration summary."""
        return {
            "name": self.name,
            "fail_open": self.fail_open,
            "layers": [
                {
                    "name": layer.name,
                    "threshold": layer.threshold,
                    "enabled": layer.enabled,
                    "type": type(layer).__name__,
                }
                for layer in self.layers
            ],
        }
