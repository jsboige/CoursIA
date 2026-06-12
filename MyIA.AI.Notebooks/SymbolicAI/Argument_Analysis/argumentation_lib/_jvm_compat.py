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


def initialize_jvm() -> bool:
    """Initialize the JVM via CoursIA's Tweety infrastructure.

    Compatible with EPITA's ``core.jvm_setup.initialize_jvm`` contract:
    returns True on success, False on failure.

    Delegates to ``Tweety.tweety_init.init_tweety`` which is idempotent
    (safe to call multiple times).
    """
    global _jvm_initialized
    if _jvm_initialized:
        _logger.debug("JVM already initialized (cached).")
        return True

    try:
        # Import relative to SymbolicAI parent — notebooks add this to sys.path
        from Tweety.tweety_init import init_tweety
        result = init_tweety(verbose=False)
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
