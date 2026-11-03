# Portage verbatim de `argumentation_analysis/services/ai_shield/layers/heuristic.py` depuis le projet
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
"""Heuristic validation layer — regex/keyword-based threat detection.

Fast, zero-cost validation using pattern matching. No LLM calls needed.

Detects:
- Prompt injection attempts ("ignore previous instructions", "system prompt")
- Jailbreak patterns ("DAN mode", "do anything now", role-play exploits)
- SQL/code injection markers
- Known adversarial formulations
"""

import re
from typing import Any, Dict, List, Optional

from argumentation_lib.ai_shield.shield import ShieldLayer, LayerResult

# ── Pattern definitions ──────────────────────────────────────────────

INJECTION_PATTERNS = [
    # Prompt injection
    r"ignore\s+(all\s+)?(previous|prior|above)\s+(instructions|rules|guidelines)",
    r"disregard\s+(all\s+)?(previous|prior|above)",
    r"forget\s+(everything|all)\s+(you|that)",
    r"new\s+instructions?\s*:",
    r"system\s*prompt\s*:",
    r"you\s+are\s+now\s+(a|an|in)\s+",
    r"\bDAN\s+mode\b",
    r"\bdo\s+anything\s+now\b",
    r"act\s+as\s+(if\s+)?you\s+(have\s+)?no\s+(restrictions|limits|rules)",
    r"pretend\s+(you\s+are|to\s+be)\s+(an?\s+)?unrestricted",
    r"jailbreak",
    # Code/SQL injection markers
    r";\s*DROP\s+TABLE",
    r";\s*DELETE\s+FROM",
    r"UNION\s+SELECT",
    r"<script\s*>",
    r"eval\s*\(",
    r"__import__\s*\(",
    r"os\.system\s*\(",
    r"subprocess\.\w+\s*\(",
]

BIAS_KEYWORDS = [
    # Derogatory generalizations
    r"all\s+\w+\s+are\s+(stupid|lazy|evil|criminals|terrorists)",
    r"(women|men|blacks|whites|muslims|jews)\s+should\s+(not|never)",
    r"\b(racial\s+)?supremac(y|ist)\b",
    r"\beugenics\b",
]

MANIPULATION_PATTERNS = [
    # Emotional manipulation / social engineering
    r"(your\s+)?(mother|family|children)\s+(will\s+)?(die|suffer|be\s+hurt)",
    r"I\s+(will|am\s+going\s+to)\s+(kill|harm|hurt)\s+(myself|you)",
    r"(bomb|weapon|explosive)\s+(instructions|recipe|how\s+to)",
]


class HeuristicLayer(ShieldLayer):
    """Fast regex/keyword-based validation layer.

    Scans input for known prompt injection, jailbreak, bias,
    and manipulation patterns. Zero LLM cost.
    """

    def __init__(
        self,
        threshold: float = 0.5,
        enabled: bool = True,
        custom_patterns: Optional[List[str]] = None,
    ):
        super().__init__(name="heuristic", threshold=threshold, enabled=enabled)
        self._injection_re = [re.compile(p, re.IGNORECASE) for p in INJECTION_PATTERNS]
        self._bias_re = [re.compile(p, re.IGNORECASE) for p in BIAS_KEYWORDS]
        self._manipulation_re = [
            re.compile(p, re.IGNORECASE) for p in MANIPULATION_PATTERNS
        ]
        self._custom_re = [
            re.compile(p, re.IGNORECASE) for p in (custom_patterns or [])
        ]

    def validate(self, text: str, **kwargs) -> LayerResult:
        """Scan text for heuristic threat patterns.

        Score computation:
        - Each injection match: +0.4
        - Each bias match: +0.3
        - Each manipulation match: +0.5
        - Each custom pattern match: +0.3
        - Capped at 1.0
        """
        matches = []
        score = 0.0

        for pattern in self._injection_re:
            m = pattern.search(text)
            if m:
                matches.append(
                    {
                        "type": "injection",
                        "match": m.group(),
                        "pattern": pattern.pattern,
                    }
                )
                score += 0.4

        for pattern in self._bias_re:
            m = pattern.search(text)
            if m:
                matches.append(
                    {"type": "bias", "match": m.group(), "pattern": pattern.pattern}
                )
                score += 0.3

        for pattern in self._manipulation_re:
            m = pattern.search(text)
            if m:
                matches.append(
                    {
                        "type": "manipulation",
                        "match": m.group(),
                        "pattern": pattern.pattern,
                    }
                )
                score += 0.5

        for pattern in self._custom_re:
            m = pattern.search(text)
            if m:
                matches.append(
                    {"type": "custom", "match": m.group(), "pattern": pattern.pattern}
                )
                score += 0.3

        score = min(score, 1.0)

        reason = ""
        if matches:
            types = set(m["type"] for m in matches)
            reason = f"Detected: {', '.join(types)} ({len(matches)} pattern(s))"

        return self._make_result(
            score=score,
            details={"matches": matches, "match_count": len(matches)},
            reason=reason,
        )
