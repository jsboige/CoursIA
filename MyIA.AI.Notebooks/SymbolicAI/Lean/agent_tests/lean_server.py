"""
LeanVerifier - Fast Lean 4 proof verification via WSL.

Uses `lean` with pre-computed LEAN_PATH to skip `lake env` overhead.
Avoids re-loading Mathlib oleans on each invocation (~60s savings).

Performance:
  - ~5-6s per verification (vs ~60-65s with `lake env lean`)
  - Correct error detection (proof failures, sorry, unknown identifiers)

Architecture:
  - Discovers all .lake/build/lib paths from the Lake project
  - Sets LEAN_PATH to include project lib + all dependency libs
  - Writes code to temp file via base64, runs `lean <file>` via WSL
  - Parses stdout for error messages

Usage:
    from lean_server import LeanVerifier

    verifier = LeanVerifier(project_dir=LEAN_PROJECT_DIR)
    result = verifier.verify("theorem foo : 1 + 1 = 2 := by rfl")
    print(result["success"])  # True

Or standalone:
    python lean_server.py --project-dir <path> --theorem "theorem foo : True := by trivial"
"""

import subprocess
import time
import base64
import os
from pathlib import Path
from typing import Optional, List


class LeanVerifier:
    """Fast Lean 4 proof verifier using pre-computed LEAN_PATH."""

    def __init__(self, project_dir: str, verbose: bool = False):
        self.project_dir = project_dir
        self.verbose = verbose

        # WSL project path
        self._wsl_project = self._to_wsl_path(
            str(Path(project_dir).resolve())
        )

        # Build LEAN_PATH once (includes all dependency libs)
        self._lean_path = self._build_lean_path()

    @staticmethod
    def _to_wsl_path(p: str) -> str:
        p = p.replace("\\", "/")
        if len(p) >= 2 and p[1] == ":":
            drive = p[0].lower()
            rest = p[2:]
            return f"/mnt/{drive}{rest}"
        return p

    def _log(self, msg: str):
        if self.verbose:
            ts = time.strftime("%H:%M:%S")
            print(f"  [Lean {ts}] {msg}")

    def _build_lean_path(self) -> str:
        """Build LEAN_PATH pointing to the project's compiled library.

        Lean 4 stores oleans in .lake/build/lib/lean/ (with 'lean' subdir).
        Only includes the project's own path — Lean resolves transitive deps
        from the project's oleans. Including dependency paths causes Lean to
        re-index Mathlib (~60s overhead).
        """
        return f"{self._wsl_project}/.lake/build/lib/lean"

    def verify(self, code: str, timeout: float = 30.0,
               use_lake_env: bool = False) -> Optional[dict]:
        """
        Verify Lean code.

        Strategy: write code to _AgentVerify.lean inside the project dir,
        run `lean` on it, parse stdout for errors.

        Modes:
          - use_lake_env=False (default): LEAN_PATH with project lib only (~5s).
            Works for proofs without Mathlib imports.
          - use_lake_env=True: lake env lean (~60s). Required for Mathlib imports.

        Returns dict with: success (bool), errors (str), time_s (float),
                           backend (str).
        """
        start = time.time()

        encoded = base64.b64encode(code.encode()).decode()
        proj = self._wsl_project
        tmp = f"{proj}/_AgentVerify.lean"
        cleanup = f'rm -f "{tmp}" "{proj}/_AgentVerify.olean" "{proj}/_AgentVerify.ilean"'

        if use_lake_env:
            lean_cmd = f'lake env lean _AgentVerify.lean 2>&1'
        else:
            lean_cmd = (
                f'LEAN_PATH="{self._lean_path}" '
                f'lean _AgentVerify.lean 2>&1'
            )

        cmd = (
            f'source ~/.elan/env && '
            f'echo {encoded} | base64 -d > "{tmp}" && '
            f'cd "{proj}" && '
            f'{lean_cmd}; '
            f'{cleanup}'
        )

        try:
            r = subprocess.run(
                ["wsl", "-d", "Ubuntu", "--", "bash", "-c", cmd],
                capture_output=True, text=True, timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            duration = time.time() - start
            self._log(f"Verification timed out after {duration:.1f}s")
            subprocess.run(
                ["wsl", "-d", "Ubuntu", "--", "bash", "-c",
                 f'source ~/.elan/env && {cleanup}'],
                capture_output=True, timeout=5,
            )
            return {
                "success": False,
                "errors": f"Timeout after {timeout}s",
                "time_s": duration,
                "backend": "lake_env" if use_lake_env else "lean_path",
            }

        duration = time.time() - start

        # Parse errors from output
        output = r.stdout
        errors = []
        has_sorry = False

        for line in output.split("\n"):
            if "error:" in line.lower():
                errors.append(line.strip())
            if "sorry" in line.lower() and "declaration uses" in line.lower():
                has_sorry = True

        success = len(errors) == 0 and not has_sorry
        backend = "lake_env" if use_lake_env else "lean_path"

        self._log(
            f"{'OK' if success else 'FAIL'} in {duration:.1f}s "
            f"({len(errors)} errors, sorry={has_sorry}, {backend})"
        )

        return {
            "success": success,
            "errors": "\n".join(errors),
            "time_s": duration,
            "backend": backend,
        }

    def verify_with_imports(
        self, code: str, imports: str, timeout: float = 60.0
    ) -> Optional[dict]:
        """Verify Lean code with import statements prepended."""
        if imports:
            full_code = f"{imports}\n{code}"
        else:
            full_code = code
        return self.verify(full_code, timeout=timeout)


class LeanLSPServer:
    """Backward-compatible alias for LeanVerifier.

    The LSP approach was abandoned because Lean 4 LSP does not report
    proof errors via publishDiagnostics. This class wraps LeanVerifier
    to maintain API compatibility with existing code.
    """

    def __init__(self, project_dir: str, verbose: bool = False):
        self._verifier = LeanVerifier(project_dir, verbose=verbose)
        self._initialized = True
        self._warmed_up = True
        self.verbose = verbose

    def start(self, timeout: float = 60.0) -> bool:
        return True

    def warmup(self, imports: str = None, timeout: float = 180.0) -> bool:
        return True

    def verify(self, code: str, timeout: float = 60.0, use_lake_env: bool = False):
        return self._verifier.verify(code, timeout=timeout, use_lake_env=use_lake_env)

    def stop(self):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.stop()


# ── CLI ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Lean Verifier CLI")
    parser.add_argument("--project-dir", required=True, help="Lake project directory")
    parser.add_argument("--theorem", help="Verify a theorem string")
    parser.add_argument("--timeout", type=float, default=30, help="Timeout (s)")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    verifier = LeanVerifier(args.project_dir, verbose=args.verbose)

    if args.theorem:
        print(f"Verifying: {args.theorem[:80]}...")
        result = verifier.verify(args.theorem, timeout=args.timeout)
        if result:
            print(f"Result: {'SUCCESS' if result['success'] else 'FAILED'}")
            print(f"Time: {result['time_s']:.2f}s")
            if result["errors"]:
                print(f"Errors:\n{result['errors']}")
        else:
            print("Verification failed (no result)")
    else:
        # Default: run a few tests
        tests = [
            ("Valid rfl", "theorem test : 1 + 1 = 2 := by rfl", True),
            ("Invalid rfl", "theorem test : 1 + 1 = 3 := by rfl", False),
            ("Valid trivial", "theorem test : True := by trivial", True),
            ("Sorry", "theorem test (n : Nat) : n = n + 1 := by sorry", False),
            ("Unknown ident", "theorem test : foo := by rfl", False),
        ]

        print(f"Running {len(tests)} tests...\n")
        total = 0
        passed = 0
        for label, code, expected in tests:
            result = verifier.verify(code, timeout=args.timeout)
            total += 1
            ok = result and result["success"] == expected
            passed += ok
            status = "PASS" if ok else "FAIL"
            print(f"  [{status}] {label}: {result['time_s']:.1f}s "
                  f"(expected={'success' if expected else 'fail'}, "
                  f"got={'success' if result['success'] else 'fail'})")
            if result["errors"] and not ok:
                print(f"         {result['errors'][:120]}")

        print(f"\nResults: {passed}/{total} passed")
