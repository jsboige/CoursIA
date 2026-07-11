"""Lean verification backend.

`lean_server.py` lives one directory up (in `agent_tests/`), not inside the
`prover/` package. We resolve it explicitly via a path-aware import so the
prover works regardless of the caller's `cwd` or `sys.path` — fixes the
"No module named 'prover.lean_server'" failure mode reported on 2026-05-08.
"""

import importlib.util
import sys
import time
from pathlib import Path
from typing import Dict, Optional

from .config import LEAN_PROJECT_DIR
from .trace import TraceLogger

# Per-project_dir cache of LeanVerifier instances. Keyed by `project_dir`
# (after defaulting to `LEAN_PROJECT_DIR`) so cross-project invocations no
# longer bind to whichever project was loaded first.
#
# History: a single `_verifier = None` global made `get_verifier(pd_a)` then
# `get_verifier(pd_b)` return the same instance bound to pd_a — a silent
# cross-project lock-in that broke every other Lake project's builds.
# Surfaced by the depth-3 sweep in PR #6067 (See #1453); the verifier itself
# was held out of that PR for follow-up because it changes the test reset
# protocol (see test_prover_guards.py).
_verifiers: Dict[str, "LeanVerifier"] = {}
_LeanVerifier_cls = None


def _load_lean_verifier_class():
    """Load `LeanVerifier` from `agent_tests/lean_server.py` via spec import."""
    global _LeanVerifier_cls
    if _LeanVerifier_cls is not None:
        return _LeanVerifier_cls

    parent_dir = Path(__file__).resolve().parent.parent
    server_path = parent_dir / "lean_server.py"
    if not server_path.exists():
        raise ImportError(
            f"lean_server.py not found at {server_path}. "
            f"Expected it next to the prover/ package."
        )

    # Spec-based import bypasses sys.path quirks.
    spec = importlib.util.spec_from_file_location(
        "agent_tests_lean_server", str(server_path)
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["agent_tests_lean_server"] = module
    spec.loader.exec_module(module)
    _LeanVerifier_cls = module.LeanVerifier
    return _LeanVerifier_cls


def get_verifier(project_dir: str = None) -> "LeanVerifier":
    """Get or create the LeanVerifier instance for the given project_dir.

    Each `project_dir` gets its own cached instance — repeated calls with the
    same path return the same object (preserves the in-memory build cache
    keyed by file content), but switching projects no longer returns the
    first call's instance. This was the source of the cross-project lock-in
    bug documented at the top of this module (See #1453, follow-up to #6067).
    """
    global _verifiers
    pd = project_dir or LEAN_PROJECT_DIR
    cached = _verifiers.get(pd)
    if cached is not None:
        return cached
    cls = _load_lean_verifier_class()
    instance = cls(project_dir=pd, verbose=False)
    _verifiers[pd] = instance
    return instance


def reset_verifier(project_dir: Optional[str] = None) -> None:
    """Drop cached verifier(s). Test-only escape hatch.

    With `project_dir=None`, the entire cache is cleared (mirrors the old
    `_verifier = None` reset). With a path, only that project's entry is
    dropped — useful when a test wants to force a fresh instance for one
    project while leaving siblings intact.
    """
    global _verifiers
    if project_dir is None:
        _verifiers.clear()
    else:
        _verifiers.pop(project_dir, None)


def verify_with_lean(theorem: str, tactic: str, imports: Optional[str],
                     project_dir: Optional[str], trace: TraceLogger,
                     agent_name: str = "LeanVerifier") -> dict:
    """Verify a Lean proof using LeanVerifier."""
    if imports:
        code = f"{imports}\n{theorem} := by {tactic}"
    else:
        code = f"{theorem} := by {tactic}"

    verifier = get_verifier(project_dir)
    start = time.time()
    result = verifier.verify(code)
    duration = time.time() - start

    success = result["success"]
    errors = result.get("errors", "")
    backend = result.get("backend", "lean_verifier")

    trace.log(
        agent=agent_name, role="verification",
        content=f"{theorem[:60]} := by {tactic[:60]}",
        duration_s=duration, tool_name="verify_proof",
        tool_args={"theorem": theorem[:80], "proof": tactic[:80]},
        tool_result=f"success={success}, backend={backend}, errors={errors[:200]}",
        phase="verify",
    )

    return {
        "success": success,
        "errors": errors,
        "time_s": duration,
        "backend": backend,
        "raw_output": result.get("raw_output", ""),
    }
