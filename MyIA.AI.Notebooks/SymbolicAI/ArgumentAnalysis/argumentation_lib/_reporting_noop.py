# _reporting_noop.py — no-op reporting shims
#
# Replaces the 7 symbols imported from
# ``argumentation_analysis.reporting.enhanced_real_time_trace_analyzer``.
#
# The real reporting system writes trace files to disk and captures
# orchestration metadata — useful for EPITA's research pipeline but
# unnecessary for CoursIA pedagogical notebooks.  These stubs let the
# runner code import without error and produce clean no-ops.

from __future__ import annotations

from typing import Any, Dict, List, Optional


class EnhancedGlobalTraceAnalyzer:
    """No-op trace analyzer."""

    def get_report(self) -> dict[str, Any]:
        return {}


# Singleton matching EPITA's module-level instance
enhanced_global_trace_analyzer = EnhancedGlobalTraceAnalyzer()


def start_enhanced_pm_capture() -> None:
    """No-op: start trace capture."""
    pass


def stop_enhanced_pm_capture() -> None:
    """No-op: stop trace capture."""
    pass


def start_pm_orchestration_phase(
    phase_id: str,
    phase_name: str = "",
    assigned_agents: Optional[List[str]] = None,
) -> None:
    """No-op: mark the start of an orchestration phase."""
    pass


def capture_shared_state(
    phase_id: str = "",
    tour_number: int = 0,
    agent_active: str = "",
    state_variables: Optional[Dict[str, Any]] = None,
    metadata: Optional[Dict[str, Any]] = None,
) -> None:
    """No-op: capture a shared-state snapshot."""
    pass


def get_enhanced_pm_report() -> dict[str, Any]:
    """No-op: return the trace report."""
    return {}


def save_enhanced_pm_report(path: str) -> bool:
    """No-op: save trace report to disk."""
    return False
