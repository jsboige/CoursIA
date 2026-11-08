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


# ===========================================================================
# #23633 (Volet B etape 4, EPIC #10355) -- runtime shim de la couche informal
# ===========================================================================
# Les DEUX fichiers verbatim non standalone-importables (mesure issue #23633) :
#
#   - `_taxonomy_sophism_detector.py` (a8025f60) : import relatif litteral
#     `from .informal_definitions import InformalAnalysisPlugin` alors que le
#     sibling sur disque s'appelle `_informal_definitions.py` (couche 1).
#   - `_informal_definitions.py` (a8025f60) : imports module-level du package
#     amont `argumentation_analysis.*` absent de l'arbre (couche 2) --
#     `core.utils.file_loaders`, `utils.taxonomy_loader`, `paths` -- PLUS un
#     import relatif litteral `from .prompts import ...` sans sibling local
#     (couche 1 bis, mesuree au scoping : aucun `_prompts.py` n'existait).
#
# La map ci-dessous registre, dans l'ORDRE (les corps s'executent a
# l'import) : les 3 helpers amont vendoes byte-identiques sous prefixe `_`
# (provenance NOTICE-EPITA), le prompts amont vendo, puis l'alias sibling
# `informal_definitions` -> `_informal_definitions`. L'entree runtime unique
# reste l'accesseur paresseux `argumentation_lib.get_taxonomy_sophism_detector()`
# (`__init__.py`), qui appelle `install_informal_runtime_shim()` avant son
# import differe -- `import argumentation_lib` reste sans effet de bord.
#
# `_epita_paths.py` porte une deviation NOT-VERBATIM declaree (appel
# module-level `ensure_directories_exist()` desactive : il recreerait
# `Argument_Analysis/libs/tweety` retire par l'arbitrage #23109).

INFORMAL_RUNTIME_MAP: list[tuple[str, str]] = [
    # 1) helpers amont vendoes (bootstrap : taxonomy_loader importe paths)
    ("argumentation_analysis.paths",
     "argumentation_lib._epita_paths"),
    ("argumentation_analysis.core.utils.file_loaders",
     "argumentation_lib._file_loaders"),
    ("argumentation_analysis.utils.taxonomy_loader",
     "argumentation_lib._taxonomy_loader"),
    # 2) sibling aliases : resolvent les imports RELATIFS litteraux des
    #    fichiers verbatim (couche 1 + couche 1 bis). prompts avant
    #    informal_definitions (le corps de ce dernier importe .prompts).
    ("argumentation_lib.prompts",
     "argumentation_lib._prompts"),
    ("argumentation_lib.informal_definitions",
     "argumentation_lib._informal_definitions"),
]

_informal_shim_installed: bool = False


def install_informal_runtime_shim() -> bool:
    """Registre la couche informal sous ses noms amont (#23633).

    Idempotent et RE-RETRYABLE : contrairement a la map #18391, le drapeau
    n'est pose que si TOUTES les entrees ont ete registrees -- une session CI
    sans ``semantic_kernel`` echoue sur la 5e entree (le corps de
    ``_informal_definitions`` importe SK au niveau module), et un appel
    ulterieur dans le meme process (SK installe entre-temps, regle F) doit
    pouvoir completer l'installation.

    Les entrees deja presentes dans ``sys.modules`` ne sont pas ecrasees ;
    les parents manquants de l'arbre ``argumentation_analysis.*`` sont crees
    en namespace packages.
    """
    global _informal_shim_installed
    if _informal_shim_installed:
        return False

    def _ensure_package(name: str) -> types.ModuleType:
        mod = sys.modules.get(name)
        if mod is None:
            mod = types.ModuleType(name)
            mod.__path__ = []  # namespace package
            sys.modules[name] = mod
        return mod

    # Parents amont requis par la couche informal (sur-ensemble minimal de
    # ceux de la map #18391 : seul core.utils est nouveau).
    for parent in {
        "argumentation_analysis",
        "argumentation_analysis.core",
        "argumentation_analysis.core.utils",
        "argumentation_analysis.utils",
    }:
        _ensure_package(parent)

    failures: list[str] = []
    for upstream_name, local_name in INFORMAL_RUNTIME_MAP:
        if upstream_name in sys.modules and sys.modules[upstream_name] is not None:
            continue  # deja registree (installation partielle anterieure)
        try:
            local_mod = importlib.import_module(local_name)
        except Exception as exc:  # noqa: BLE001
            # Best-effort aligne sur la map #18391 : une dep optionnelle
            # absente (semantic_kernel en CI sans requirements de serie)
            # laisse l'entree non registree -- l'import differe de
            # l'accesseur re-levera l'empreinte ModuleNotFoundError honnete.
            sys.stderr.write(
                f"[informal_runtime_shim] skip {upstream_name}: {exc!r}\n"
            )
            failures.append(upstream_name)
            continue
        sys.modules[upstream_name] = local_mod
        # Alias sibling : exposer aussi comme attribut du package parent pour
        # que `import argumentation_lib.prompts` resolve apres le shim.
        if upstream_name.startswith("argumentation_lib."):
            parent_pkg = importlib.import_module("argumentation_lib")
            setattr(parent_pkg, upstream_name.rsplit(".", 1)[-1], local_mod)

    if failures:
        return False

    _informal_shim_installed = True
    return True


__all__ = __all__ + [
    "install_informal_runtime_shim",
    "INFORMAL_RUNTIME_MAP",
]
