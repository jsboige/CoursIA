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
    # reporting
    "EnhancedGlobalTraceAnalyzer", "enhanced_global_trace_analyzer",
    "start_enhanced_pm_capture", "stop_enhanced_pm_capture",
    "start_pm_orchestration_phase", "capture_shared_state",
    "get_enhanced_pm_report", "save_enhanced_pm_report",
]
