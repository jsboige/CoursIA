# _jvm_compat.py — JVM initialization shim
#
# Bridges EPITA's `initialize_jvm` / `shutdown_jvm` / `is_jvm_started`
# contract to CoursIA's `init_tweety()` (Tweety/tweety_init.py).
#
# CoursIA's Tweety infrastructure is SUPERIOR to EPITA's jvm_setup.py
# (idempotent init, 35+ modules v1.30, Clingo/SPASS/EProver/SAT/JDK17).
# We REUSE CoursIA infra, NOT vendor jvm_setup.py.

from __future__ import annotations

import logging
from typing import Optional

_logger = logging.getLogger("argumentation_lib._jvm_compat")

# Cache: was the JVM initialized by us?
_jvm_initialized: bool = False


def initialize_jvm(verbose: bool = False) -> bool:
    """Initialize the JVM via CoursIA's Tweety infrastructure.

    Robust, self-contained entry point for Argument_Analysis notebooks:
    resolves the Tweety directory, stages ``sys.path`` (so
    ``Tweety.tweety_init`` is importable) and ``chdir`` to the Tweety
    directory before calling ``init_tweety`` — which locates ``libs/`` and
    ``jdk-17-portable/`` RELATIVE to the current working directory.

    Idempotent (cached via ``_jvm_initialized``); safe to call repeatedly.
    ``verbose=True`` forwards to ``init_tweety`` so a notebook can surface
    the JDK/JAR-loading evidence (anti-theatre).
    Returns True on success, False on failure.
    """
    global _jvm_initialized
    if _jvm_initialized:
        _logger.debug("JVM already initialized (cached).")
        return True

    try:
        import os
        import sys
        from argumentation_lib._paths import SYMBOLIC_AI_DIR

        # The Tweety runtime lives canonically at SymbolicAI/Tweety: it holds
        # tweety_init.py, libs/*.jar and jdk-17-portable/. Resolve it directly
        # rather than via get_tweety_jar_dir() — whose first candidate
        # (Argument_Analysis/libs) is jar-less, so its parent has no
        # tweety_init.py and would silently skip the chdir below if a stray
        # jar ever landed there.
        tweety_dir = SYMBOLIC_AI_DIR / "Tweety"
        if not (tweety_dir / "tweety_init.py").exists():
            _logger.error("Tweety init module not found at %s", tweety_dir)
            return False

        # Make SymbolicAI importable so `Tweety.tweety_init` resolves, then
        # chdir into the Tweety dir: init_tweety() locates libs/ and
        # jdk-17-portable/ RELATIVE to the current working directory.
        sym = str(SYMBOLIC_AI_DIR)
        if sym not in sys.path:
            sys.path.insert(0, sym)
        os.chdir(str(tweety_dir))

        from Tweety.tweety_init import init_tweety
        result = init_tweety(verbose=verbose)
        if result:
            _jvm_initialized = True
            _logger.info("JVM initialized via CoursIA Tweety infrastructure.")
        return result
    except Exception as e:
        _logger.error("Failed to initialize JVM via Tweety: %s", e)
        return False


def is_jvm_started() -> bool:
    """Check if the JVM is currently running."""
    try:
        import jpype
        return jpype.isJVMStarted()
    except ImportError:
        return _jvm_initialized


def shutdown_jvm() -> None:
    """Shut down the JVM.

    Warning: once shut down, it cannot be restarted in the same process.
    Only call this at process exit.
    """
    global _jvm_initialized
    try:
        import jpype
        if jpype.isJVMStarted():
            jpype.shutdownJVM()
            _jvm_initialized = False
            _logger.info("JVM shut down.")
    except Exception as e:
        _logger.warning("Failed to shut down JVM: %s", e)
