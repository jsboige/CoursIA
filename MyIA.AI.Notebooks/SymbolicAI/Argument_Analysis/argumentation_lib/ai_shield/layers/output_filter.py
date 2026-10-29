# Portage verbatim de `argumentation_analysis/services/ai_shield/layers/output_filter.py` depuis le projet
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
"""Output filter layer — prevents sensitive information leaks in LLM output.

Scans LLM output for patterns that suggest the model is leaking:
- System prompts or internal instructions
- API keys, tokens, credentials
- PII (emails, phone numbers, SSNs)
- Internal file paths or environment variables
"""

import re
from typing import Any, Dict, List, Optional

from argumentation_lib.ai_shield.shield import ShieldLayer, LayerResult

# ── Leak detection patterns ──────────────────────────────────────────

SYSTEM_PROMPT_LEAKS = [
    r"(my|the)\s+(system\s+)?instructions?\s+(are|say|tell)",
    r"I\s+(was|am)\s+instructed\s+to",
    r"my\s+original\s+prompt",
    r"here\s+(is|are)\s+my\s+(system\s+)?instructions?",
    r"as\s+an?\s+AI\s+(language\s+)?model,?\s+my\s+instructions",
]

CREDENTIAL_PATTERNS = [
    # API keys and tokens
    r"sk-[a-zA-Z0-9]{20,}",  # OpenAI-style
    r"sk-or-v1-[a-zA-Z0-9]{40,}",  # OpenRouter
    r"Bearer\s+[a-zA-Z0-9\-._~+/]+=*",  # Bearer tokens
    r"api[_-]?key\s*[=:]\s*['\"]?[a-zA-Z0-9]{16,}",  # Generic API key
    r"password\s*[=:]\s*['\"]?[^\s'\"]{8,}",  # Passwords
    r"secret\s*[=:]\s*['\"]?[a-zA-Z0-9]{16,}",  # Secrets
]

PII_PATTERNS = [
    # Email addresses
    r"\b[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}\b",
    # Phone numbers (various formats)
    r"\b(\+?\d{1,3}[-.\s]?)?\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}\b",
    # SSN-like patterns
    r"\b\d{3}[-\s]?\d{2}[-\s]?\d{4}\b",
    # Credit card numbers (basic)
    r"\b\d{4}[-\s]?\d{4}[-\s]?\d{4}[-\s]?\d{4}\b",
]

PATH_PATTERNS = [
    # File paths
    r"[A-Z]:\\[\w\\]+",  # Windows paths
    r"/(?:home|root|etc|var|usr)/[\w/]+",  # Unix paths
    # Environment variables
    r"\$\{?\w+_(?:KEY|SECRET|TOKEN|PASSWORD)\}?",
]


class OutputFilterLayer(ShieldLayer):
    """Filters LLM output for sensitive information leaks.

    Designed to be used on LLM responses (not user input).
    Detects system prompt leaks, credentials, PII, and file paths.
    """

    def __init__(
        self,
        threshold: float = 0.4,
        enabled: bool = True,
        check_pii: bool = True,
        check_credentials: bool = True,
        check_system_leaks: bool = True,
        check_paths: bool = True,
    ):
        super().__init__(name="output_filter", threshold=threshold, enabled=enabled)
        self._check_pii = check_pii
        self._check_credentials = check_credentials
        self._check_system_leaks = check_system_leaks
        self._check_paths = check_paths

        self._system_re = [re.compile(p, re.IGNORECASE) for p in SYSTEM_PROMPT_LEAKS]
        self._cred_re = [re.compile(p) for p in CREDENTIAL_PATTERNS]
        self._pii_re = [re.compile(p) for p in PII_PATTERNS]
        self._path_re = [re.compile(p) for p in PATH_PATTERNS]

    def validate(self, text: str, **kwargs) -> LayerResult:
        """Scan output for sensitive information leaks.

        Score computation:
        - System prompt leak: +0.5
        - Credential leak: +0.6
        - PII leak: +0.3 per match
        - Path leak: +0.2
        - Capped at 1.0
        """
        matches = []
        score = 0.0

        if self._check_system_leaks:
            for pattern in self._system_re:
                m = pattern.search(text)
                if m:
                    matches.append({"type": "system_leak", "match": m.group()})
                    score += 0.5
                    break  # One system leak is enough

        if self._check_credentials:
            for pattern in self._cred_re:
                m = pattern.search(text)
                if m:
                    # Redact the match for safety
                    matched = m.group()
                    redacted = (
                        matched[:4] + "***" + matched[-4:]
                        if len(matched) > 8
                        else "***"
                    )
                    matches.append({"type": "credential", "match": redacted})
                    score += 0.6
                    break

        if self._check_pii:
            for pattern in self._pii_re:
                for m in pattern.finditer(text):
                    matched = m.group()
                    redacted = (
                        matched[:3] + "***" + matched[-3:]
                        if len(matched) > 6
                        else "***"
                    )
                    matches.append({"type": "pii", "match": redacted})
                    score += 0.3
                    if score >= 1.0:
                        break

        if self._check_paths:
            for pattern in self._path_re:
                m = pattern.search(text)
                if m:
                    matches.append({"type": "path_leak", "match": m.group()})
                    score += 0.2
                    break

        score = min(score, 1.0)

        reason = ""
        if matches:
            types = set(m["type"] for m in matches)
            reason = f"Output leak: {', '.join(types)} ({len(matches)} finding(s))"

        return self._make_result(
            score=score,
            details={"findings": matches, "finding_count": len(matches)},
            reason=reason,
        )
