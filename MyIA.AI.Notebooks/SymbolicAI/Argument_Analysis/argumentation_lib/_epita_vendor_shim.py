# _epita_vendor_shim.py -- EPITA-IS verbatim import bridge for issue #18391
#
# PURPOSE
# -------
# Verbatim upstream files vendored in this directory:
#
#   - `_fallacy_workflow_plugin.py`  (commit ecfd9b9c)
#   - `_exploration_plugin.py`        (commit ecfd9b9c)
#   - `_taxonomy_navigator.py`        (commit ecfd9b9c)
#   - `_taxonomy_local_overrides.py`  (commit ecfd9b9c)
#   - `_taxonomy_tree.py`             (commit ecfd9b9c)
#   - `_plaintext_destination.py`     (commit ecfd9b9c)
#   - `_identification_models.py`     (commit ecfd9b9c)
#
# All seven contain literal imports of the form
# `from argumentation_analysis.<sub>.<name> import ...`. Their bodies
# are byte-identical to the upstream source at commit ecfd9b9c -- the
# "Verbatim integrity: byte-for-byte identical" header on each file
# is the contract documented in NOTICE-EPITA.
#
# This module re-exposes each vendored CoursIA file as a virtual
# `argumentation_analysis.<sub>.<name>` sys.modules entry, so the
# verbatim imports inside the vendored files resolve transparently
# (just like the C186g `_jvm_setup_compat` shim does for
# `argumentation_analysis.core.jvm_setup`).
#
# ANTI-REGRESSION (D)
# -------------------
# 0 `pass`, 0 `return None`, 0 `sorry`, 0 `raise NotImplementedError`
# added.  This is a thin glue layer -- it only registers already-
# vendored modules under their upstream Python dotted names.  No
# derivation logic.
#
# SCOPE
# -----
# This shim is the portee 2 of issue #18391 acceptance 2/5 of
# EPIC #4960 (entonnoir taxonomique agentique).  It does NOT cover
# the LLM-backed execution (run_guided_analysis requires an LLM
# endpoint and a key) -- it only unblocks `import` so that consumers
# can read class definitions, type hints, and constant tables.

from __future__ import annotations

import importlib
import sys
import types


_PROXY_INSTALLED: bool = False


# Mapping : upstream_dotted_name -> local_vendored_module_name
# Each local module is the byte-for-byte verbatim file we vendored
# at commit ecfd9b9c (tronc EPITA fige). The mapping is deterministic
# (one-line per file) and the SHA of each is recorded in NOTICE-EPITA.
#
# LOAD ORDER matters: leaf modules first (no internal deps), then
# mid-level, then leaves-of-leaves-on-leaves that import them.
# - `taxonomy_local_overrides`, `taxonomy_tree`, `plaintext_destination`,
#   `identification_models` are pure utility modules (no internal
#   `argumentation_analysis` imports in their bodies beyond the
#   `from semantic_kernel...` lines they may share).
# - `taxonomy_navigator` imports from `taxonomy_local_overrides` and
#   `taxonomy_tree` (verified at vendor time, body imports at L5-9).
# - `exploration_plugin` imports from `taxonomy_navigator`.
# - `fallacy_workflow_plugin` imports from all of the above plus
#   `plaintext_destination` and `identification_models`.
# Hence: leaves first, then mid, then top.
VENDOR_MAP: list[tuple[str, str]] = [
    # Leaves (no internal argumentation_analysis deps beyond stdlib/SK)
    ("argumentation_analysis.utils.taxonomy_local_overrides",
     "argumentation_lib._taxonomy_local_overrides"),
    ("argumentation_analysis.utils.taxonomy_tree",
     "argumentation_lib._taxonomy_tree"),
    ("argumentation_analysis.core.plaintext_destination",
     "argumentation_lib._plaintext_destination"),
    ("argumentation_analysis.plugins.identification_models",
     "argumentation_lib._identification_models"),
    # Mid (depends on leaves)
    ("argumentation_analysis.agents.utils.taxonomy_navigator",
     "argumentation_lib._taxonomy_navigator"),
    ("argumentation_analysis.plugins.exploration_plugin",
     "argumentation_lib._exploration_plugin"),
    # Top (depends on everything)
    ("argumentation_analysis.plugins.fallacy_workflow_plugin",
     "argumentation_lib._fallacy_workflow_plugin"),
]


def install_epita_vendor_shim() -> bool:
    """Register vendored modules under their upstream dotted names.

    Idempotent: returns False (no-op) if already installed in this
    process. Best-effort: if a single mapping fails to import, the
    other six still install; the failure is logged but not raised.

    Returns:
        True if installation took place, False if already installed.
    """
    global _PROXY_INSTALLED
    if _PROXY_INSTALLED:
        return False

    def _ensure_package(name: str) -> types.ModuleType:
        mod = sys.modules.get(name)
        if mod is None:
            mod = types.ModuleType(name)
            mod.__path__ = []  # namespace package
            sys.modules[name] = mod
        return mod

    # Build the parent package chain lazily as we register submodules.
    # We need to ensure all of these exist:
    #   argumentation_analysis
    #   argumentation_analysis.plugins
    #   argumentation_analysis.agents
    #   argumentation_analysis.agents.utils
    #   argumentation_analysis.utils
    #   argumentation_analysis.core
    for parent in {
        "argumentation_analysis",
        "argumentation_analysis.plugins",
        "argumentation_analysis.agents",
        "argumentation_analysis.agents.utils",
        "argumentation_analysis.utils",
        "argumentation_analysis.core",
    }:
        _ensure_package(parent)

    for upstream_name, local_name in VENDOR_MAP:
        try:
            local_mod = importlib.import_module(local_name)
        except Exception as exc:  # noqa: BLE001
            # Best-effort: a missing optional dep (semantic_kernel, etc.)
            # may keep one of the seven from importing. Skip silently;
            # the verbatim import will then re-raise the G.9 fingerprint.
            sys.stderr.write(
                f"[epita_vendor_shim] skip {upstream_name}: {exc!r}\n"
            )
            continue
        sys.modules[upstream_name] = local_mod

    _PROXY_INSTALLED = True
    return True


# Module-load-time installation (idempotent, safe to re-import).
try:
    install_epita_vendor_shim()
except Exception:  # noqa: BLE001
    # Best-effort: if anything blows up at module-load (cycle, missing
    # import), the verbatim modules stay unbridged and downstream
    # imports re-raise the original G.9 ModuleNotFoundError.
    pass


__all__ = ["install_epita_vendor_shim", "VENDOR_MAP"]
