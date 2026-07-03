# argumentation_lib — vendored shim layer for Argument Analysis notebooks
#
# Provides the public API consumed by CoursIA notebooks, decoupled from
# the EPITA `argumentation_analysis` internals.  All heavy imports are
# lazy; importing this module alone must succeed without the EPITA package.
#
# Phase B.2 — core state + agents + runner vendored.
# See #2137 Phase B scope and acceptance criteria.

__version__ = "0.2.0"

# -- Configuration (zero secrets, zero model names) --
from argumentation_lib._config import LibConfig, get_config, DEFAULT_CONFIG

# -- Path management (pure, no import-time side effects) --
from argumentation_lib._paths import (
    LIB_DIR,
    ARGUMENT_ANALYSIS_DIR,
    SYMBOLIC_AI_DIR,
    get_tweety_jar_dir,
    get_ontology_dir,
    get_data_dir,
    get_ext_tools_dir,
    ensure_output_dirs,
)

# -- JVM initialization (bridges to CoursIA Tweety infra) --
from argumentation_lib._jvm_compat import (
    initialize_jvm,
    is_jvm_started,
    shutdown_jvm,
)

# -- Shared state (RhetoricalAnalysisState — autoportant, zero EPITA deps) --
from argumentation_lib._shared_state import (
    ArgumentProfile,
    RhetoricalAnalysisState,
    UnifiedAnalysisState,
)

# -- State Manager Plugin (Semantic Kernel @kernel_function wrapper) --
# Heavy import — requires semantic_kernel.  Use lazy pattern.
def get_state_manager_plugin():
    """Lazy import to avoid requiring semantic_kernel at package import."""
    from argumentation_lib._state_manager_plugin import StateManagerPlugin
    return StateManagerPlugin

# -- Reporting (no-op shims) --
from argumentation_lib._reporting_noop import (
    EnhancedGlobalTraceAnalyzer,
    enhanced_global_trace_analyzer,
    start_enhanced_pm_capture,
    stop_enhanced_pm_capture,
    start_pm_orchestration_phase,
    capture_shared_state,
    get_enhanced_pm_report,
    save_enhanced_pm_report,
)

# -- Runner (requires semantic_kernel) --
def get_analysis_runner():
    """Lazy import for the analysis runner."""
    from argumentation_lib._runner import AnalysisRunner
    return AnalysisRunner

# -- Taxonomy Sophism Detector (Semantic Kernel heavy dep via InformalAnalysisPlugin) --
def get_taxonomy_sophism_detector():
    """Lazy import for the TaxonomySophismDetector.

    Note: This module depends on `InformalAnalysisPlugin` from EPITA-IS upstream,
    which is NOT vendored in this tranche (Semantic-Kernel coupled, 891 lines).
    Instantiation will fail at runtime until Volet B etape 4 ports the SK shim.
    The class symbol itself is import-safe (analysis only).
    """
    from argumentation_lib._taxonomy_sophism_detector import (
        TaxonomySophismDetector,
        create_unified_detector,
        get_global_detector,
    )
    return TaxonomySophismDetector



# -- Informal Definitions (Semantic Kernel heavy dep via InformalAnalysisPlugin) --
def get_informal_definitions_symbols():
    """Lazy import for informal-definitions symbols.

    Returns a tuple of the 5 public symbols exported by
    `_informal_definitions.py`:

        (InformalAnalysisPlugin, IdentifiedFallacy, FallacyAnalysisResult,
         setup_informal_kernel, INFORMAL_AGENT_INSTRUCTIONS)

    Note (G.9 honest caveat): the upstream module imports
    `semantic_kernel`, `pandas`, `pydantic`, `requests` and three
    EPITA-internal helpers (`load_csv_file`, `get_taxonomy_path`,
    `DATA_DIR`) that are NOT vendored in `argumentation_lib/`. Even the
    module-level `import` will raise `ModuleNotFoundError:
    No module named 'argumentation_analysis'` today -- this lazy
    accessor exists for completeness with C184's accessor pattern, but
    C185 realizes it does not bypass the top-level imports. Runtime
    usability awaits Volet B etape 4 (TweetyBridge shim JPype).
    The verbatim copy is preserved here for the future shim that will
    re-export its public symbols.
    """
    from argumentation_lib._informal_definitions import (
        InformalAnalysisPlugin,
        IdentifiedFallacy,
        FallacyAnalysisResult,
        setup_informal_kernel,
        INFORMAL_AGENT_INSTRUCTIONS,
    )
    return (
        InformalAnalysisPlugin,
        IdentifiedFallacy,
        FallacyAnalysisResult,
        setup_informal_kernel,
        INFORMAL_AGENT_INSTRUCTIONS,
    )


# -- PL Handler (JPype singleton, SK-coupled upstream) --
def get_pl_handler_symbol():
    """Lazy import for the PLHandler class symbol.

    Note (G.9 honest caveat): `pl_handler.py` imports
    `argumentation_analysis.core.utils.logging_utils.setup_logging`,
    `from .tweety_initializer import TweetyInitializer`, and indirectly
    the `argumentation_analysis.core.jvm_setup` module — none vendored in
    `argumentation_lib/` today. Even the module-level `import` raises
    `ModuleNotFoundError`. The lazy accessor preserves the API symmetry
    with C184/C185 accessors but, like C185, does **not** bypass the
    top-level imports. Runtime usability awaits Volet B etape 4
    sub-tranches C186f (TweetyInitializer) and C186g (runtime bridge shim).

    **C186a sibling** : the PL/FOL handlers are imported at the top of
    `tweety_bridge.py` (which is itself a C186a sub-tranche, awaiting
    merge via PR #5231). This accessor is independently meaningful for
    modules that want to import PLHandler directly without going through
    the bridge.
    """
    from argumentation_lib._pl_handler import PLHandler
    return PLHandler


# -- FOL Handler (JPype singleton, SK-coupled upstream, prover9_runner dep) --
def get_fol_handler_symbol():
    """Lazy import for the FOLHandler class symbol.

    Note (G.9 honest caveat): `fol_handler.py` imports
    `argumentation_analysis.core.utils.logging_utils.setup_logging`,
    `from .tweety_initializer import TweetyInitializer`, and
    `argumentation_analysis.core.prover9_runner.run_prover9` — none
    vendored in `argumentation_lib/` today. The verbatim body relies on
    the external prover9 binary via this binding. Even the module-level
    `import` raises `ModuleNotFoundError`. Runtime usability awaits
    Volet B etape 4 sub-tranches C186f (TweetyInitializer) and C186g
    (runtime bridge shim).
    """
    from argumentation_lib._fol_handler import FOLHandler
    return FOLHandler



__all__ = [
    # config
    "LibConfig", "get_config", "DEFAULT_CONFIG",
    # paths
    "LIB_DIR", "ARGUMENT_ANALYSIS_DIR", "SYMBOLIC_AI_DIR",
    "get_tweety_jar_dir", "get_ontology_dir", "get_data_dir",
    "get_ext_tools_dir", "ensure_output_dirs",
    # jvm
    "initialize_jvm", "is_jvm_started", "shutdown_jvm",
    # state
    "ArgumentProfile", "RhetoricalAnalysisState", "UnifiedAnalysisState",
    "get_state_manager_plugin",
    # runner
    "get_analysis_runner",
    "get_taxonomy_sophism_detector",
    "get_informal_definitions_symbols",
    "get_pl_handler_symbol",
    "get_fol_handler_symbol",
    # reporting
    "EnhancedGlobalTraceAnalyzer", "enhanced_global_trace_analyzer",
    "start_enhanced_pm_capture", "stop_enhanced_pm_capture",
    "start_pm_orchestration_phase", "capture_shared_state",
    "get_enhanced_pm_report", "save_enhanced_pm_report",
]
