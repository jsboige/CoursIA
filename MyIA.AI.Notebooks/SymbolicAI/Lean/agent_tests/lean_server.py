"""
LeanVerifier - Lean 4 proof verification via WSL.

Architecture:
  - Discovers toolchain from lean-toolchain file
  - Builds LEAN_PATH with project lib + all dependency libs
  - Fast path (no imports): ~5-6s per call
  - Full path (Mathlib imports): ~130-150s per call (module indexing cost)
  - Uses script file approach to avoid WSL shell escaping issues with long LEAN_PATH

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

        # Discover toolchain and build paths
        self._toolchain = self._discover_toolchain()
        self._lean_path_fast = self._build_lean_path_fast()
        self._lean_path_full = self._build_lean_path_full()
        self._warm = False
        self._verify_count = 0

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

    def _discover_toolchain(self) -> str:
        """Read lean-toolchain to find the correct Lean version."""
        tc_file = Path(self.project_dir) / "lean-toolchain"
        if tc_file.exists():
            version = tc_file.read_text().strip().split(":")[-1]
            return version
        return "stable"

    def _build_lean_path_fast(self) -> str:
        """LEAN_PATH with project lib only. Fast (~5s) but no Mathlib."""
        return f"{self._wsl_project}/.lake/build/lib/lean"

    def _build_lean_path_full(self) -> str:
        """LEAN_PATH with project lib + all dependency libs."""
        proj = self._wsl_project
        paths = [f"{proj}/.lake/build/lib/lean"]

        pkg_dir = f"{proj}/.lake/packages"
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--", "bash", "-c",
             f"ls -d {pkg_dir}/*/.lake/build/lib/lean/ 2>/dev/null"],
            capture_output=True, text=True, timeout=10,
        )
        for line in result.stdout.strip().split("\n"):
            line = line.strip().rstrip("/")
            if line and "No such" not in line:
                paths.append(line)

        return ":".join(paths)

    def _get_lean_bin(self) -> str:
        """Get the lean binary path for this project's toolchain."""
        return f"$HOME/.elan/toolchains/leanprover--lean4---{self._toolchain}/bin/lean"

    def warmup(self, timeout: float = 300.0) -> bool:
        """Pay the cold-start cost once. Subsequent full-path calls are faster.

        Returns True if warmup succeeded.
        """
        if self._warm:
            return True

        self._log(f"Warmup: indexing modules (toolchain={self._toolchain})...")
        start = time.time()

        # Use verify() which now uses the script approach
        result = self.verify(
            "theorem _warmup_test : True := by trivial",
            timeout=timeout,
            use_full_path=True,
        )

        duration = time.time() - start
        if result and result["success"]:
            self._warm = True
            self._log(f"Warmup complete in {duration:.1f}s")
            return True
        else:
            self._log(f"Warmup failed in {duration:.1f}s")
            return False

    def verify(self, code: str, timeout: float = None,
               use_full_path: bool = None) -> Optional[dict]:
        """Verify Lean code.

        Args:
            code: Lean source code to verify.
            timeout: Max seconds to wait. Default: 300s for full_path, 60s
                for fast_path.
            use_full_path: If True, use LEAN_PATH with all deps (needed for
                Mathlib imports). If False, use project lib only (~5s).
                If None, auto-detect from code content (check for imports).

        Returns dict with: success, errors, raw_output, time_s, backend, warm.
        """
        # Auto-detect if full path needed
        if use_full_path is None:
            use_full_path = self._code_needs_deps(code)

        # Auto-timeout: full_path needs ~150s+, fast_path ~5s
        if timeout is None:
            timeout = 300.0 if use_full_path else 60.0

        start = time.time()
        self._verify_count += 1

        encoded = base64.b64encode(code.encode()).decode()
        proj = self._wsl_project
        tmp = f"{proj}/_AgentVerify.lean"
        script = f"{proj}/_agent_verify.sh"
        cleanup = f'rm -f "{tmp}" "{proj}/_AgentVerify.olean" "{proj}/_AgentVerify.ilean" "{script}"'

        if use_full_path:
            lean_path = self._lean_path_full
            lean_bin = self._get_lean_bin()
            backend = "full_path"
        else:
            lean_path = self._lean_path_fast
            lean_bin = "lean"
            backend = "fast_path"

        # Write a shell script to WSL to avoid quoting issues with long LEAN_PATH
        # The script is written via base64 to avoid any shell escaping problems
        script_content = (
            f'#!/bin/bash\n'
            f'source ~/.elan/env\n'
            f'echo {encoded} | base64 -d > "{tmp}"\n'
            f'cd "{proj}"\n'
            f'export LEAN_PATH="{lean_path}"\n'
            f'{lean_bin} "{tmp}" 2>&1\n'
            f'{cleanup}\n'
        )
        script_b64 = base64.b64encode(script_content.encode()).decode()

        cmd = f'echo {script_b64} | base64 -d > "{script}" && chmod +x "{script}" && bash "{script}"'

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
                "backend": backend,
                "warm": self._warm,
            }

        duration = time.time() - start
        output = r.stdout
        errors = []
        has_sorry = False
        raw_errors = []

        for line in output.split("\n"):
            if "error:" in line.lower():
                errors.append(line.strip())
                raw_errors.append(line.strip())
            if "sorry" in line.lower() and "declaration uses" in line.lower():
                has_sorry = True

        success = len(errors) == 0 and not has_sorry

        # Track warm state: any successful full_path call means modules are indexed
        if use_full_path and success:
            self._warm = True

        self._log(
            f"{'OK' if success else 'FAIL'} in {duration:.1f}s "
            f"({len(errors)} err, sorry={has_sorry}, {backend})"
        )

        return {
            "success": success,
            "errors": "\n".join(errors),
            "raw_output": output,
            "time_s": duration,
            "backend": backend,
            "warm": self._warm,
        }

    @staticmethod
    def _code_needs_deps(code: str) -> bool:
        """Detect if code imports Mathlib or project modules."""
        for line in code.split("\n"):
            stripped = line.strip()
            if stripped.startswith("import "):
                if "Mathlib" in stripped or "CooperativeGames" in stripped:
                    return True
        return False

    def verify_with_imports(
        self, code: str, imports: str, timeout: float = 120.0
    ) -> Optional[dict]:
        """Verify Lean code with import statements prepended."""
        if imports:
            full_code = f"{imports}\n{code}"
        else:
            full_code = code
        return self.verify(full_code, timeout=timeout)

    @property
    def stats(self) -> dict:
        return {
            "verify_count": self._verify_count,
            "warm": self._warm,
            "toolchain": self._toolchain,
            "project": self._wsl_project,
        }


class LeanLSPServer:
    """Backward-compatible alias for LeanVerifier."""

    def __init__(self, project_dir: str, verbose: bool = False):
        self._verifier = LeanVerifier(project_dir, verbose=verbose)
        self._initialized = True
        self._warmed_up = False
        self.verbose = verbose

    def start(self, timeout: float = 60.0) -> bool:
        return True

    def warmup(self, imports: str = None, timeout: float = 300.0) -> bool:
        ok = self._verifier.warmup(timeout=timeout)
        self._warmed_up = ok
        return ok

    def verify(self, code: str, timeout: float = 120.0, use_lake_env: bool = False):
        return self._verifier.verify(code, timeout=timeout,
                                     use_full_path=use_lake_env)

    def stop(self):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.stop()


# -- CLI --

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Lean Verifier CLI")
    parser.add_argument("--project-dir", required=True, help="Lake project directory")
    parser.add_argument("--theorem", help="Verify a theorem string")
    parser.add_argument("--timeout", type=float, default=120, help="Timeout (s)")
    parser.add_argument("--warmup", action="store_true", help="Run warmup first")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    verifier = LeanVerifier(args.project_dir, verbose=args.verbose)

    if args.warmup:
        print("Warming up (indexing Mathlib)...")
        ok = verifier.warmup(timeout=args.timeout)
        print(f"Warmup {'OK' if ok else 'FAILED'}")

    if args.theorem:
        print(f"Verifying: {args.theorem[:80]}...")
        result = verifier.verify(args.theorem, timeout=args.timeout)
        if result:
            print(f"Result: {'SUCCESS' if result['success'] else 'FAILED'}")
            print(f"Time: {result['time_s']:.2f}s ({result['backend']})")
            if result["errors"]:
                print(f"Errors:\n{result['errors']}")
        else:
            print("Verification failed (no result)")
    else:
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
