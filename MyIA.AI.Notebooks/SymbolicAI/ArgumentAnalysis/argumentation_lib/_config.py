# _config.py — static configuration defaults for argumentation_lib
#
# Replaces EPITA's `config/settings.py` which reads `.env` and contains
# hardcoded model names like `gpt-5-mini`. This shim provides ONLY static
# defaults with ZERO secrets, ZERO model names, ZERO env reads.
#
# The actual LLM service is INJECTED at runtime (kernel SK + Config/settings.json).
# This module never touches credentials.

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


@dataclass(frozen=True)
class LibConfig:
    """Static defaults for the argumentation library.

    No secrets. No model names. No env reads.
    The LLM kernel is built inline in notebooks and injected into agents.
    """

    # --- Tweety / JVM ---
    tweety_jar_dir: Optional[str] = None  # auto-detected by _jvm_compat

    # --- Pipeline ---
    max_turns_per_phase: int = 5
    max_conversation_turns: int = 20

    # --- Agents ---
    enable_tracing: bool = False
    trace_log_dir: str = "logs"

    # --- Reporting ---
    enable_enhanced_reporting: bool = False

    # --- Paths ---
    ontology_dir: str = "ontologies"
    data_dir: str = "data"


# Singleton default config
DEFAULT_CONFIG = LibConfig()


def get_config() -> LibConfig:
    """Return the default static configuration.

    Future: could be extended to read from a notebook-local config file,
    but NEVER from env vars with secret fallbacks.
    """
    return DEFAULT_CONFIG
