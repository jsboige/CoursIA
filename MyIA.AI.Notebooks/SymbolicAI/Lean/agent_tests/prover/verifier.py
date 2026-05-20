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
from typing import Optional

from .config import LEAN_PROJECT_DIR
from .trace import TraceLogger

_verifier = None
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
    """Get or create the persistent LeanVerifier instance."""
    global _verifier
    if _verifier is None:
        cls = _load_lean_verifier_class()
        pd = project_dir or LEAN_PROJECT_DIR
        _verifier = cls(project_dir=pd, verbose=False)
    return _verifier


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
