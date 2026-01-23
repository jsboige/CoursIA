"""
LeanRunner - Execute Lean 4 code from Python via multiple backends

This module provides a unified interface to run Lean 4 code from Python with
multiple backend options:

1. subprocess (default): Direct Lean execution via subprocess (Windows/Linux/macOS)
2. wsl: Execute via WSL lean4_jupyter kernel (Windows with WSL)
3. leandojo: Use LeanDojo for ML/LLM theorem proving (requires Python <3.13, GitHub token)

Usage:
    from lean_runner import LeanRunner

    # Default subprocess backend
    runner = LeanRunner()
    result = runner.run('#eval 2 + 2')
    print(result.output)

    # WSL backend (for full REPL support on Windows)
    runner = LeanRunner(backend='wsl')
    result = runner.run('#eval 2 + 2')

    # Auto-detect best backend
    runner = LeanRunner(backend='auto')

LeanDojo Backend (for ML/LLM theorem proving):
    from lean_runner import LeanRunner

    runner = LeanRunner(backend='leandojo')

    # Trace a repository to extract theorems
    traced = runner.trace_repo(
        "https://github.com/yangky11/lean4-example",
        "7761283d0aed994cd1c7e893786212d2a01d159e"
    )

    # Get all theorems from the repo
    theorems = runner.get_theorems(traced)
    print(f"Found {len(theorems)} theorems")

    # Try to prove a theorem with tactics
    result = runner.prove_with_tactics(theorems[0], ["rfl"])
    print(f"Proof succeeded: {result['success']}")

    # Or interact with Dojo directly
    dojo, state = runner.create_dojo(theorems[0])
    new_state = runner.run_tactic(dojo, state, "intro x")
"""

import subprocess
import tempfile
import os
import shutil
import json
import platform
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, List, Literal
from enum import Enum


class Backend(Enum):
    SUBPROCESS = "subprocess"
    WSL = "wsl"
    LEANDOJO = "leandojo"
    AUTO = "auto"


@dataclass
class LeanResult:
    """Result of executing Lean code"""
    success: bool
    output: str
    errors: str
    code: str
    exit_code: int
    backend: str = "subprocess"


class LeanRunner:
    """
    Execute Lean 4 code via multiple backends.

    Backends:
    - subprocess: Direct Lean execution (default, works on all platforms)
    - wsl: WSL lean4_jupyter kernel (Windows only, full REPL support)
    - leandojo: LeanDojo for ML/LLM theorem proving (requires setup)
    - auto: Automatically select best available backend
    """

    def __init__(
        self,
        lean_path: Optional[str] = None,
        timeout: int = 30,
        backend: Literal["subprocess", "wsl", "leandojo", "auto"] = "subprocess"
    ):
        """
        Initialize the Lean runner.

        Args:
            lean_path: Path to lean executable. If None, auto-detected.
            timeout: Timeout in seconds for Lean execution.
            backend: Backend to use ('subprocess', 'wsl', 'leandojo', 'auto')
        """
        self.timeout = timeout
        self._temp_dir = None
        self._wsl_kernel = None
        self._leandojo_repo = None

        # Select backend
        if backend == "auto":
            self.backend = self._auto_select_backend()
        else:
            self.backend = Backend(backend)

        # Initialize backend-specific resources
        if self.backend == Backend.SUBPROCESS:
            self.lean_path = lean_path or self._find_lean()
        elif self.backend == Backend.WSL:
            self._init_wsl()
        elif self.backend == Backend.LEANDOJO:
            self._init_leandojo()

    def _auto_select_backend(self) -> Backend:
        """Automatically select the best available backend."""
        # On Windows, try WSL first for full REPL support
        if platform.system() == "Windows":
            if self._check_wsl_available():
                return Backend.WSL

        # Fall back to subprocess
        return Backend.SUBPROCESS

    def _check_wsl_available(self) -> bool:
        """Check if WSL with lean4_jupyter is available."""
        try:
            result = subprocess.run(
                ["wsl", "-d", "Ubuntu", "--", "bash", "-c",
                 "source ~/.lean4-venv/bin/activate 2>/dev/null && "
                 "source ~/.elan/env 2>/dev/null && "
                 "which lean && which repl"],
                capture_output=True, text=True, timeout=10
            )
            return result.returncode == 0
        except:
            return False

    def _find_lean(self) -> str:
        """Find the lean executable in PATH or common locations."""
        # Try PATH first
        lean_path = shutil.which("lean")
        if lean_path:
            return lean_path

        # Try elan default location
        elan_bin = Path.home() / ".elan" / "bin"
        if (elan_bin / "lean").exists():
            return str(elan_bin / "lean")
        if (elan_bin / "lean.exe").exists():
            return str(elan_bin / "lean.exe")

        raise FileNotFoundError(
            "Lean executable not found. Please install Lean 4 via elan:\n"
            "  elan default leanprover/lean4:stable"
        )

    def _init_wsl(self):
        """Initialize WSL backend."""
        if not self._check_wsl_available():
            raise RuntimeError(
                "WSL backend not available. Ensure:\n"
                "1. WSL Ubuntu is installed\n"
                "2. ~/.lean4-venv with lean4_jupyter is set up\n"
                "3. elan and repl are installed in WSL"
            )

    def _init_leandojo(self):
        """Initialize LeanDojo backend."""
        try:
            # Set GitHub token if available (check multiple sources)
            if "GITHUB_ACCESS_TOKEN" not in os.environ:
                # 1. Try local .env file first
                local_env = Path(__file__).parent / ".env"
                if local_env.exists():
                    try:
                        with open(local_env) as f:
                            for line in f:
                                line = line.strip()
                                if line.startswith("GITHUB_ACCESS_TOKEN="):
                                    token = line.split("=", 1)[1].strip()
                                    os.environ["GITHUB_ACCESS_TOKEN"] = token
                                    break
                                elif line.startswith("GITHUB_TOKEN=") and "GITHUB_ACCESS_TOKEN" not in os.environ:
                                    token = line.split("=", 1)[1].strip()
                                    os.environ["GITHUB_ACCESS_TOKEN"] = token
                    except:
                        pass

            # 2. Try gh CLI
            if "GITHUB_ACCESS_TOKEN" not in os.environ:
                try:
                    result = subprocess.run(["gh", "auth", "token"],
                                            capture_output=True, text=True)
                    if result.returncode == 0:
                        os.environ["GITHUB_ACCESS_TOKEN"] = result.stdout.strip()
                except:
                    pass

            from lean_dojo import LeanGitRepo
            self._leandojo_available = True
        except ImportError:
            raise RuntimeError(
                "LeanDojo not available. Install with:\n"
                "  pip install lean-dojo\n"
                "Requires Python < 3.13"
            )

    def check_installation(self) -> dict:
        """Check Lean installation and return version info."""
        if self.backend == Backend.SUBPROCESS:
            return self._check_subprocess_installation()
        elif self.backend == Backend.WSL:
            return self._check_wsl_installation()
        elif self.backend == Backend.LEANDOJO:
            return self._check_leandojo_installation()

    def _check_subprocess_installation(self) -> dict:
        """Check subprocess backend installation."""
        try:
            result = subprocess.run(
                [self.lean_path, "--version"],
                capture_output=True, text=True, timeout=10
            )
            version = result.stdout.strip() if result.returncode == 0 else "unknown"
            return {
                "installed": True,
                "backend": "subprocess",
                "path": self.lean_path,
                "version": version,
                "error": None
            }
        except FileNotFoundError:
            return {
                "installed": False,
                "backend": "subprocess",
                "path": None,
                "version": None,
                "error": "Lean executable not found"
            }
        except Exception as e:
            return {
                "installed": False,
                "backend": "subprocess",
                "path": self.lean_path,
                "version": None,
                "error": str(e)
            }

    def _check_wsl_installation(self) -> dict:
        """Check WSL backend installation."""
        try:
            result = subprocess.run(
                ["wsl", "-d", "Ubuntu", "--", "bash", "-c",
                 "source ~/.elan/env && lean --version"],
                capture_output=True, text=True, timeout=15
            )
            version = result.stdout.strip() if result.returncode == 0 else "unknown"
            return {
                "installed": result.returncode == 0,
                "backend": "wsl",
                "path": "wsl://Ubuntu",
                "version": version,
                "error": None if result.returncode == 0 else result.stderr
            }
        except Exception as e:
            return {
                "installed": False,
                "backend": "wsl",
                "path": None,
                "version": None,
                "error": str(e)
            }

    def _check_leandojo_installation(self) -> dict:
        """Check LeanDojo backend installation."""
        try:
            import lean_dojo
            return {
                "installed": True,
                "backend": "leandojo",
                "path": "lean_dojo",
                "version": lean_dojo.__version__,
                "error": None
            }
        except ImportError as e:
            return {
                "installed": False,
                "backend": "leandojo",
                "path": None,
                "version": None,
                "error": str(e)
            }

    def run(self, code: str, filename: str = "Main.lean") -> LeanResult:
        """
        Execute Lean code and return the result.

        Args:
            code: Lean 4 source code to execute.
            filename: Name for the temporary file (affects error messages).

        Returns:
            LeanResult with output, errors, and success status.
        """
        if self.backend == Backend.SUBPROCESS:
            return self._run_subprocess(code, filename)
        elif self.backend == Backend.WSL:
            return self._run_wsl(code)
        elif self.backend == Backend.LEANDOJO:
            return self._run_leandojo(code)

    def _run_subprocess(self, code: str, filename: str) -> LeanResult:
        """Execute Lean code via subprocess."""
        # Create temp directory if needed
        if self._temp_dir is None:
            self._temp_dir = tempfile.mkdtemp(prefix="lean_runner_")

        # Write code to temp file
        file_path = Path(self._temp_dir) / filename
        file_path.write_text(code, encoding="utf-8")

        try:
            result = subprocess.run(
                [self.lean_path, str(file_path)],
                capture_output=True, text=True,
                timeout=self.timeout, cwd=self._temp_dir
            )

            return LeanResult(
                success=result.returncode == 0,
                output=result.stdout.strip(),
                errors=result.stderr.strip(),
                code=code,
                exit_code=result.returncode,
                backend="subprocess"
            )

        except subprocess.TimeoutExpired:
            return LeanResult(
                success=False, output="",
                errors=f"Timeout after {self.timeout} seconds",
                code=code, exit_code=-1, backend="subprocess"
            )
        except Exception as e:
            return LeanResult(
                success=False, output="", errors=str(e),
                code=code, exit_code=-1, backend="subprocess"
            )

    def _run_wsl(self, code: str) -> LeanResult:
        """Execute Lean code via WSL lean4_jupyter REPL."""
        # Build JSON command for REPL
        json_cmd = json.dumps({"cmd": code})

        try:
            result = subprocess.run(
                ["wsl", "-d", "Ubuntu", "--", "bash", "-c",
                 f'source ~/.elan/env && echo \'{json_cmd}\' | repl'],
                capture_output=True, text=True, timeout=self.timeout
            )

            if result.returncode == 0 and result.stdout.strip():
                try:
                    output_json = json.loads(result.stdout.strip())
                    messages = output_json.get("messages", [])
                    outputs = []
                    errors = []

                    for msg in messages:
                        severity = msg.get("severity", "info")
                        data = msg.get("data", "")
                        if severity == "error":
                            errors.append(data)
                        else:
                            outputs.append(data)

                    return LeanResult(
                        success=len(errors) == 0,
                        output="\n".join(outputs),
                        errors="\n".join(errors),
                        code=code,
                        exit_code=0 if len(errors) == 0 else 1,
                        backend="wsl"
                    )
                except json.JSONDecodeError:
                    return LeanResult(
                        success=False, output=result.stdout,
                        errors="Failed to parse REPL output",
                        code=code, exit_code=1, backend="wsl"
                    )
            else:
                return LeanResult(
                    success=False, output="",
                    errors=result.stderr or "Unknown error",
                    code=code, exit_code=result.returncode, backend="wsl"
                )

        except subprocess.TimeoutExpired:
            return LeanResult(
                success=False, output="",
                errors=f"Timeout after {self.timeout} seconds",
                code=code, exit_code=-1, backend="wsl"
            )
        except Exception as e:
            return LeanResult(
                success=False, output="", errors=str(e),
                code=code, exit_code=-1, backend="wsl"
            )

    def _run_leandojo(self, code: str) -> LeanResult:
        """Execute Lean code via LeanDojo (limited - mainly for tracing)."""
        # LeanDojo is primarily for tracing repos and extracting theorems
        # For direct code execution, use subprocess backend
        subprocess_runner = LeanRunner(timeout=self.timeout, backend="subprocess")
        result = subprocess_runner.run(code)
        result.backend = "leandojo-subprocess"
        return result

    # =========================================================================
    # LeanDojo-specific methods for ML/LLM theorem proving
    # =========================================================================

    def trace_repo(self, repo_url: str, commit: str, force: bool = False):
        """
        Trace a Lean Git repository to extract theorems and their states.

        Args:
            repo_url: GitHub repository URL (e.g., "https://github.com/yangky11/lean4-example")
            commit: Commit hash to trace
            force: Force re-tracing even if cached

        Returns:
            TracedRepo object from LeanDojo

        Example:
            runner = LeanRunner(backend='leandojo')
            traced = runner.trace_repo("https://github.com/yangky11/lean4-example",
                                       "7761283d0aed994cd1c7e893786212d2a01d159e")
            theorems = runner.get_theorems(traced)
        """
        if self.backend != Backend.LEANDOJO:
            raise RuntimeError("trace_repo requires 'leandojo' backend")

        from lean_dojo import LeanGitRepo, trace, is_available_in_cache

        repo = LeanGitRepo(repo_url, commit)
        if not force and is_available_in_cache(repo):
            print(f"Repository found in cache")

        traced_repo = trace(repo)
        self._leandojo_repo = traced_repo
        return traced_repo

    def get_theorems(self, traced_repo=None) -> list:
        """
        Extract all theorems from a traced repository.

        Args:
            traced_repo: TracedRepo object (or use last traced repo)

        Returns:
            List of Theorem objects with full_name, file_path, etc.
        """
        if traced_repo is None:
            traced_repo = self._leandojo_repo
        if traced_repo is None:
            raise RuntimeError("No traced repository. Call trace_repo() first.")

        return list(traced_repo.get_theorems())

    def create_dojo(self, theorem):
        """
        Create a Dojo environment for interactive proving.

        Args:
            theorem: Theorem object from get_theorems()

        Returns:
            Tuple of (Dojo, initial_state)

        Example:
            runner = LeanRunner(backend='leandojo')
            traced = runner.trace_repo(url, commit)
            theorems = runner.get_theorems(traced)
            dojo, state = runner.create_dojo(theorems[0])
            # Use dojo.run_tac(state, "rfl") to run tactics
        """
        from lean_dojo import Dojo
        return Dojo(theorem).__enter__()

    def run_tactic(self, dojo, state, tactic: str):
        """
        Run a tactic in a Dojo environment.

        Args:
            dojo: Dojo environment
            state: Current proof state
            tactic: Tactic string to run (e.g., "rfl", "simp", "apply foo")

        Returns:
            New state after running the tactic, or None if tactic failed
        """
        return dojo.run_tac(state, tactic)

    def prove_with_tactics(self, theorem, tactics: list) -> dict:
        """
        Attempt to prove a theorem using a sequence of tactics.

        Args:
            theorem: Theorem object
            tactics: List of tactic strings to try in sequence

        Returns:
            Dict with 'success', 'steps', 'remaining_goals'

        Example:
            runner = LeanRunner(backend='leandojo')
            traced = runner.trace_repo(url, commit)
            theorems = runner.get_theorems(traced)
            result = runner.prove_with_tactics(theorems[0], ["intro x", "rfl"])
        """
        from lean_dojo import Dojo

        steps = []
        with Dojo(theorem) as (dojo, state):
            current_state = state
            for tactic in tactics:
                if current_state is None or not current_state.goals:
                    break

                result = dojo.run_tac(current_state, tactic)
                steps.append({
                    'tactic': tactic,
                    'success': result is not None,
                    'goals_before': len(current_state.goals),
                    'goals_after': len(result.goals) if result else None
                })

                if result is not None:
                    current_state = result
                else:
                    break

            return {
                'success': current_state is not None and len(current_state.goals) == 0,
                'steps': steps,
                'remaining_goals': len(current_state.goals) if current_state else None
            }

    def run_interactive(self, code: str) -> None:
        """
        Run Lean code and print output in a notebook-friendly format.

        Args:
            code: Lean 4 source code to execute.
        """
        result = self.run(code)

        # Print code block
        print("=" * 50)
        print(f"Lean 4 Code (backend: {result.backend}):")
        print("-" * 50)
        for i, line in enumerate(code.strip().split('\n'), 1):
            print(f"{i:3d} | {line}")
        print("-" * 50)

        # Print output
        if result.output:
            print("\nOutput:")
            print(result.output)

        # Print errors
        if result.errors:
            if result.success:
                print("\nWarnings:")
            else:
                print("\nErrors:")
            # Clean up error paths
            if self._temp_dir:
                errors = result.errors.replace(str(self._temp_dir), ".")
            else:
                errors = result.errors
            print(errors)

        # Status
        status = "OK" if result.success else "FAILED"
        print(f"\n[{status}]")
        print("=" * 50)

    def eval(self, expr: str) -> str:
        """
        Evaluate a Lean expression and return the result.

        Args:
            expr: Lean expression to evaluate.

        Returns:
            The evaluated result as a string.
        """
        code = f"#eval {expr}"
        result = self.run(code)
        if result.success:
            return result.output
        else:
            raise RuntimeError(f"Evaluation failed: {result.errors}")

    def check(self, expr: str) -> str:
        """
        Check the type of a Lean expression.

        Args:
            expr: Lean expression to check.

        Returns:
            The type as a string.
        """
        code = f"#check {expr}"
        result = self.run(code)
        if result.success or result.output:
            return result.output
        else:
            raise RuntimeError(f"Type check failed: {result.errors}")

    def prove(self, theorem: str, proof: str) -> LeanResult:
        """
        Verify a theorem with its proof.

        Args:
            theorem: Theorem statement (e.g., "(a b : Nat) : a + b = b + a")
            proof: Proof tactics or term.

        Returns:
            LeanResult indicating if the proof is valid.
        """
        code = f"""
theorem test_theorem {theorem} := by
  {proof}

#check test_theorem
"""
        return self.run(code)

    def cleanup(self):
        """Clean up temporary files."""
        if self._temp_dir and Path(self._temp_dir).exists():
            shutil.rmtree(self._temp_dir)
            self._temp_dir = None

    def __del__(self):
        """Destructor to clean up temp files."""
        try:
            self.cleanup()
        except:
            pass

    @staticmethod
    def available_backends() -> List[str]:
        """Return list of available backends on this system."""
        backends = ["subprocess"]  # Always available if Lean is installed

        # Check WSL
        if platform.system() == "Windows":
            try:
                result = subprocess.run(
                    ["wsl", "-d", "Ubuntu", "--", "bash", "-c", "which lean"],
                    capture_output=True, text=True, timeout=5
                )
                if result.returncode == 0:
                    backends.append("wsl")
            except:
                pass

        # Check LeanDojo
        try:
            import lean_dojo
            backends.append("leandojo")
        except:
            pass

        return backends


# Convenience function for quick execution
def run_lean(code: str, timeout: int = 30, backend: str = "subprocess") -> LeanResult:
    """
    Quick way to run Lean code.

    Args:
        code: Lean 4 source code.
        timeout: Timeout in seconds.
        backend: Backend to use ('subprocess', 'wsl', 'auto')

    Returns:
        LeanResult with execution results.
    """
    runner = LeanRunner(timeout=timeout, backend=backend)
    try:
        return runner.run(code)
    finally:
        runner.cleanup()


# Test when run directly
if __name__ == "__main__":
    print("Testing LeanRunner...")
    print(f"Available backends: {LeanRunner.available_backends()}")

    # Test default backend
    runner = LeanRunner()
    print(f"\nUsing backend: {runner.backend.value}")

    # Check installation
    info = runner.check_installation()
    print(f"Installation: {info}")

    if info["installed"]:
        # Test #eval
        print("\n--- Test #eval ---")
        result = runner.run('#eval "Hello from Lean 4!"')
        print(f"Output: {result.output}")
        print(f"Success: {result.success}")
        print(f"Backend: {result.backend}")

        # Test #check
        print("\n--- Test #check ---")
        result = runner.run('#check Nat → Nat')
        print(f"Output: {result.output}")

        # Test theorem
        print("\n--- Test theorem ---")
        code = """
theorem add_comm_example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

#check add_comm_example
"""
        result = runner.run(code)
        print(f"Output: {result.output}")
        print(f"Success: {result.success}")

        # Interactive mode
        print("\n--- Interactive mode ---")
        runner.run_interactive("""
-- Simple arithmetic
#eval 2 + 2
#eval List.range 5

-- Type checking
#check Nat.add_comm
""")

    runner.cleanup()

    # Test LeanDojo if available
    if "leandojo" in LeanRunner.available_backends():
        print("\n--- Test LeanDojo backend ---")
        try:
            dojo_runner = LeanRunner(backend='leandojo')
            info = dojo_runner.check_installation()
            print(f"LeanDojo version: {info['version']}")

            # Note: tracing a repo takes several minutes, so we skip in basic test
            print("LeanDojo available. Use trace_repo() to trace repositories.")
            print("Example:")
            print('  traced = runner.trace_repo("https://github.com/yangky11/lean4-example",')
            print('                             "7761283d0aed994cd1c7e893786212d2a01d159e")')
            print('  theorems = runner.get_theorems(traced)')
        except Exception as e:
            print(f"LeanDojo test skipped: {e}")

    print("\nDone!")
