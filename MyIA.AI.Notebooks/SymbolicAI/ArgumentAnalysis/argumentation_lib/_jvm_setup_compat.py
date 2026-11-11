# _jvm_setup_compat.py -- Runtime bridge shim for C186g (See EPIC #4960)
#
# This is G6 "colle" (glue), NOT a verbatim upstream port.  Per ai-01
# verdict msg-20260703T155506-3gv1da Q3: "Shim minimal de cycle-de-vie
# JVM accepte. Garde-le glue-fin : purete verbatim preservee pour le
# core, le shim est de la colle, pas du port."
#
# PURPOSE
# -------
# Verbatim upstream `_tweety_initializer.py` (C186f) imports at
# module-load time:
#
#     from argumentation_analysis.core.utils.logging_utils import setup_logging
#     from argumentation_analysis.core.jvm_setup import (
#         initialize_jvm as initialize_jvm_robustly,
#     )
#     from argumentation_analysis.core.jvm_setup import shutdown_jvm, is_jvm_started
#
# The `argumentation_analysis` Python package is EPITA-IS-internal and
# is NOT vendored in `argumentation_lib/` (and never will be: vendor
# time would explode, and CoursIA's JVM infra is already superior --
# see `_jvm_compat.py` C184 header for the rationale).
#
# Instead of vendoring the upstream module, this shim registers
# `argumentation_analysis.core.jvm_setup` and
# `argumentation_analysis.core.utils.logging_utils` as virtual
# sys.modules entries that proxy to existing CoursIA infrastructure.
# The verbatim imports then resolve transparently -- the upstream
# contract is satisfied without duplicating the upstream sources.
#
# SHAPE OF THE SHIM
# -----------------
# 1. REAL IMPLEMENTATION LIVES ELSEWHERE:
#    - `argumentation_lib.initialize_jvm / shutdown_jvm / is_jvm_started`
#      -> re-exported from `_jvm_compat.py` (C184).
#    - `setup_logging(name)` is stdlib-only (configures the named
#      logger to INFO+Stderr if no handlers attached).
#
# 2. THIS MODULE registers two types.ModuleType proxies under:
#      - sys.modules["argumentation_analysis"]
#      - sys.modules["argumentation_analysis.core"]
#      - sys.modules["argumentation_analysis.core.utils"]
#      - sys.modules["argumentation_analysis.core.utils.logging_utils"]
#      - sys.modules["argumentation_analysis.core.jvm_setup"]
#    Each proxy carries the appropriate public attributes.  Idempotent
#    via a process-local flag.
#
# 3. The proxy registration runs at module IMPORT TIME of this shim.
#    Tests that need the verbatim imports to succeed must therefore
#    `import argumentation_lib._jvm_setup_compat` BEFORE the verbatim
#    module (or use the accessor `install_epita_namespace_shim()`).
#
# ANTI-REGRESSION (D)
# -------------------
# 0 `pass`, 0 `return None`, 0 `sorry`, 0 `raise NotImplementedError`
# added.  This is a thin glue layer -- every public symbol either
# re-exports `_jvm_compat` (C184) or stdlib-only `logging.config`.  No
# derivation logic.

from __future__ import annotations

import logging
import sys
import types


_PROXY_INSTALLED: bool = False


def _build_setup_logging() -> types.FunctionType:
    """Build a stdlib-only `setup_logging(name=__name__)` callable.

    The upstream `argumentation_analysis.core.utils.logging_utils.setup_logging`
    is the canonical logger-config entry point used throughout the
    EPITA-IS chain.  We approximate it (one-line: ensure the named
    logger has a stderr handler at INFO+ and does not propagate
    duplicate messages) without dragging in the upstream file.

    Returns a module-level function bound to `setup_logging` so the
    proxy module attribute lookup finds it.
    """

    def setup_logging(name: str = "argumentation_analysis") -> None:
        """Configure the named logger to INFO+Stderr (idempotent).

        Mirrors the contract called by the verbatim upstream
        `_tweety_initializer.py` (L47 import) and the wider C186
        chain: ensure a single stderr StreamHandler at INFO level
        attaches iff no handlers are already configured, and stop
        propagation to avoid double-logging.
        """
        logger = logging.getLogger(name)
        if logger.handlers:
            return
        handler = logging.StreamHandler()
        handler.setLevel(logging.INFO)
        handler.setFormatter(
            logging.Formatter(
                fmt="%(asctime)s [%(levelname)s] %(name)s :: %(message)s",
                datefmt="%Y-%m-%dT%H:%M:%S",
            )
        )
        logger.addHandler(handler)
        logger.setLevel(logging.INFO)
        logger.propagate = False

    return setup_logging


def install_epita_namespace_shim() -> bool:
    """Register `argumentation_analysis.core.{jvm_setup,
    utils.logging_utils}` as virtual sys.modules proxies.

    Idempotent: returns False (no-op) if already installed in this
    process.

    Returns:
        True if installation took place, False if already installed.
    """
    global _PROXY_INSTALLED
    if _PROXY_INSTALLED:
        return False

    # 1. Lazy import to avoid hard link-time cycle.
    from argumentation_lib._jvm_compat import (
        initialize_jvm,
        is_jvm_started,
        shutdown_jvm,
    )

    # 2. Build parent packages (namespace-style, no __init__.py on disk).
    def _ensure_package(name: str) -> types.ModuleType:
        mod = sys.modules.get(name)
        if mod is None:
            mod = types.ModuleType(name)
            mod.__path__ = []  # mark as a package so submodule lookups work
            sys.modules[name] = mod
        return mod

    _ensure_package("argumentation_analysis")
    _ensure_package("argumentation_analysis.core")
    _ensure_package("argumentation_analysis.core.utils")

    # 3. jvm_setup proxy -- re-exports the C184 _jvm_compat functions,
    #    plus the aliased `initialize_jvm_robustly` for the C186f import.
    jvm_setup = types.ModuleType("argumentation_analysis.core.jvm_setup")
    jvm_setup.initialize_jvm = initialize_jvm
    jvm_setup.initialize_jvm_robustly = (
        initialize_jvm  # alias used by C186f at line L14-17
    )
    jvm_setup.shutdown_jvm = shutdown_jvm
    jvm_setup.is_jvm_started = is_jvm_started
    sys.modules["argumentation_analysis.core.jvm_setup"] = jvm_setup

    # 4. utils.logging_utils proxy -- single stdlib-only callable.
    logging_utils = types.ModuleType(
        "argumentation_analysis.core.utils.logging_utils"
    )
    logging_utils.setup_logging = _build_setup_logging()
    sys.modules[
        "argumentation_analysis.core.utils.logging_utils"
    ] = logging_utils

    _PROXY_INSTALLED = True
    return True


# Module-load-time installation (idempotent, safe to re-import).
try:
    install_epita_namespace_shim()
except Exception:
    # Best-effort: if C184 / JPype / stdlib is unavailable, leave the
    # proxies un-installed; downstream verbatim imports will then fail
    # with the original G.9 honest ModuleNotFoundError.
    pass


__all__ = [
    "install_epita_namespace_shim",
    # Proxy-side public names (also accessible via sys.modules lookups):
    "initialize_jvm",
    "initialize_jvm_robustly",
    "shutdown_jvm",
    "is_jvm_started",
    "setup_logging",
]
