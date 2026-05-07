"""Lean verification backend."""

import time
from typing import Optional

from .config import LEAN_PROJECT_DIR
from .trace import TraceLogger

_verifier = None


def get_verifier(project_dir: str = None) -> "LeanVerifier":
    """Get or create the persistent LeanVerifier instance."""
    global _verifier
    if _verifier is None:
        from lean_server import LeanVerifier
        pd = project_dir or LEAN_PROJECT_DIR
        _verifier = LeanVerifier(project_dir=pd, verbose=False)
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
