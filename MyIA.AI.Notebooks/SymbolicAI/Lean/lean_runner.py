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

            # IMPORTANT: Lean outputs errors to stdout, not stderr!
            # And returns exit code 0 even with errors.
            # We need to check stdout for error patterns.
            stdout = result.stdout.strip()
            stderr = result.stderr.strip()

            # Detect errors in stdout (Lean's actual error output)
            has_errors = (
                ": error:" in stdout or
                ": warning: declaration uses 'sorry'" in stdout or
                "unknown identifier" in stdout or
                "unknown constant" in stdout or
                "tactic 'sorry' failed" in stdout or
                "unsolved goals" in stdout
            )

            # Extract error messages from stdout
            error_lines = []
            output_lines = []
            for line in stdout.split('\n'):
                if ": error:" in line or ": warning:" in line:
                    error_lines.append(line)
                else:
                    output_lines.append(line)

            # Combine errors from stdout and stderr
            errors = '\n'.join(error_lines)
            if stderr:
                errors = f"{errors}\n{stderr}" if errors else stderr

            return LeanResult(
                success=not has_errors and result.returncode == 0,
                output='\n'.join(output_lines).strip(),
                errors=errors.strip(),
                code=code,
                exit_code=result.returncode if has_errors else 0,
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


# =========================================================================
# LLM Integration Classes for Lean Proof Generation
# =========================================================================
# Added January 2026
# =========================================================================

# Try to import optional LLM dependencies
try:
    import openai as _openai_module
    _OPENAI_AVAILABLE = True
except ImportError:
    _OPENAI_AVAILABLE = False

try:
    import anthropic as _anthropic_module
    _ANTHROPIC_AVAILABLE = True
except ImportError:
    _ANTHROPIC_AVAILABLE = False

# Additional imports for LLM classes
from typing import Dict, Any
import time
import re


def load_env_file(env_path: Path = None) -> bool:
    """Load environment variables from .env file."""
    try:
        from dotenv import load_dotenv as _load_dotenv
    except ImportError:
        return False
    if env_path and env_path.exists():
        _load_dotenv(env_path, override=True)  # Force override existing vars
        return True
    for path in [Path(__file__).parent / ".env", Path.cwd() / ".env"]:
        if path.exists():
            _load_dotenv(path, override=True)  # Force override existing vars
            return True
    return False

# Configuration des providers LLM
PROVIDERS_CONFIG = {
    "openai": {
        "models": {
            "gpt-5.2": {"max_tokens_param": "max_completion_tokens", "default": 1000},
            "gpt-5-mini": {"max_tokens_param": "max_completion_tokens", "default": 1000},
        },
        "api_key_env": "OPENAI_API_KEY",
        "default_model": "gpt-5.2"
    },
    "anthropic": {
        "models": {
            "claude-sonnet-4-5": {"max_tokens": 4096},
            "claude-opus-4-5": {"max_tokens": 4096},
            "claude-3-5-sonnet": {"max_tokens": 4096}
        },
        "api_key_env": "ANTHROPIC_API_KEY",
        "default_model": "claude-sonnet-4-5"
    }
}

@dataclass
class LLMResponse:
    """Reponse d'un LLM avec metadonnees."""
    content: str
    model: str
    provider: str
    tokens_used: Dict[str, int]
    latency_ms: float

class LLMClient:
    """
    Client unifie pour OpenAI et Anthropic avec retry logic.
    
    Gere automatiquement :
    - Parametres max_tokens vs max_completion_tokens selon le modele
    - Retry avec exponential backoff pour rate limits
    - Extraction de code Lean des reponses
    """
    
    def __init__(self, provider: str = "openai", model: str = None):
        """
        Initialise le client LLM.
        
        Args:
            provider: "openai" ou "anthropic"
            model: Nom du modele (None = utiliser defaut du provider)
        """
        self.provider = provider.lower()
        if self.provider not in PROVIDERS_CONFIG:
            raise ValueError(f"Provider {provider} non supporte. Utilisez: {list(PROVIDERS_CONFIG.keys())}")
        
        config = PROVIDERS_CONFIG[self.provider]
        # Lire la variable d'environnement spécifique au provider
        env_model_var = f"{self.provider.upper()}_CHAT_MODEL_ID"
        self.model = model or os.getenv(env_model_var) or config["default_model"]
        self.api_key = os.getenv(config["api_key_env"])
        
        if not self.api_key or self.api_key.startswith(("sk-...", "sk-ant-...")):
            raise ValueError(
                f"Cle API {config['api_key_env']} non configuree. "
                f"Ajoutez-la dans .env : {config['api_key_env']}=sk-..."
            )
        
        # Initialiser les clients API
        if self.provider == "openai":
            from openai import OpenAI
            self.client = OpenAI(api_key=self.api_key)
        elif self.provider == "anthropic":
            from anthropic import Anthropic
            self.client = Anthropic(api_key=self.api_key)
    
    def generate(
        self,
        prompt: str,
        system_prompt: str = "Tu es un expert en Lean 4 et Mathlib4.",
        temperature: float = 0.3,
        max_retries: int = 3
    ) -> LLMResponse:
        """
        Genere une reponse avec retry logic.
        
        Args:
            prompt: Le prompt utilisateur
            system_prompt: Le prompt systeme
            temperature: Temperature (0.0-1.0, bas = deterministe)
            max_retries: Nombre de tentatives en cas d'erreur
        
        Returns:
            LLMResponse avec le contenu et les metadonnees
        """
        for attempt in range(max_retries):
            try:
                start_time = time.time()
                
                if self.provider == "openai":
                    response = self._generate_openai(prompt, system_prompt, temperature)
                elif self.provider == "anthropic":
                    response = self._generate_anthropic(prompt, system_prompt, temperature)
                
                latency_ms = (time.time() - start_time) * 1000
                
                return LLMResponse(
                    content=response["content"],
                    model=response["model"],
                    provider=self.provider,
                    tokens_used=response["tokens"],
                    latency_ms=latency_ms
                )
            
            except Exception as e:
                if attempt < max_retries - 1:
                    wait_time = 2 ** attempt  # Exponential backoff
                    print(f"  [Erreur API, retry dans {wait_time}s: {e}]")
                    time.sleep(wait_time)
                else:
                    raise RuntimeError(f"Echec apres {max_retries} tentatives: {e}")
    
    def _generate_openai(self, prompt: str, system_prompt: str, temperature: float) -> Dict[str, Any]:
        """Genere avec OpenAI."""
        # Detecter le bon parametre max_tokens
        model_config = PROVIDERS_CONFIG["openai"]["models"]
        for model_prefix, config in model_config.items():
            if self.model.startswith(model_prefix):
                max_tokens_param = config["max_tokens_param"]
                max_tokens_value = config["default"]
                break
        else:
            # Defaut pour modeles inconnus
            max_tokens_param = "max_tokens"
            max_tokens_value = 800
        
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": prompt}
            ],
            temperature=temperature,
            **{max_tokens_param: max_tokens_value}
        )
        
        return {
            "content": response.choices[0].message.content,
            "model": response.model,
            "tokens": {
                "prompt": response.usage.prompt_tokens,
                "completion": response.usage.completion_tokens,
                "total": response.usage.total_tokens
            }
        }
    
    def _generate_anthropic(self, prompt: str, system_prompt: str, temperature: float) -> Dict[str, Any]:
        """Genere avec Anthropic."""
        model_config = PROVIDERS_CONFIG["anthropic"]["models"]
        max_tokens = model_config.get(self.model, {"max_tokens": 4096})["max_tokens"]
        
        response = self.client.messages.create(
            model=self.model,
            max_tokens=max_tokens,
            temperature=temperature,
            system=system_prompt,
            messages=[
                {"role": "user", "content": prompt}
            ]
        )
        
        return {
            "content": response.content[0].text,
            "model": response.model,
            "tokens": {
                "prompt": response.usage.input_tokens,
                "completion": response.usage.output_tokens,
                "total": response.usage.input_tokens + response.usage.output_tokens
            }
        }

# Verification de la configuration

class LeanProofPrompt:
    """
    Gestion des prompts pour generation de preuves Lean.

    Fournit :
    - Templates de prompts structures (initial, correction, few-shot)
    - Extraction de code Lean des reponses LLM
    - Nettoyage et formatting du code
    """

    # System prompt when Mathlib is NOT available
    SYSTEM_PROMPT = """Tu es un expert en Lean 4.

Tu dois generer des preuves Lean 4 qui :
1. Utilisent les tactiques Lean 4 STANDARD (rfl, simp, omega, exact, apply, intro, constructor, cases, induction, rw, have)
2. N'utilisent PAS de tactiques Mathlib (ring, linarith, norm_num, field_simp, polyrith) - Mathlib n'est pas disponible
3. Pour les operations sur Nat, utilisent les lemmes standard comme Nat.add_comm, Nat.mul_comm, Nat.add_assoc, Nat.mul_assoc, Nat.left_distrib, etc.
4. Sont syntaxiquement correctes
5. Sont concises et elegantes

IMPORTANT: Ne genere PAS d'import Mathlib, ils ne sont pas disponibles.

Reponds UNIQUEMENT avec le code Lean, sans explications supplementaires."""

    # System prompt when Mathlib IS available
    SYSTEM_PROMPT_MATHLIB = """Tu es un expert en Lean 4 et Mathlib4.

Tu dois generer des preuves Lean 4 qui :
1. Utilisent les tactiques appropriees (rfl, simp, omega, ring, linarith, exact, apply, intro, etc.)
2. Sont syntaxiquement correctes
3. Sont concises et elegantes
4. Utilisent Mathlib quand approprie

Reponds UNIQUEMENT avec le code Lean, sans explications supplementaires."""

    @staticmethod
    def build_initial_prompt(
        theorem_statement: str,
        context: Optional[Dict[str, Any]] = None
    ) -> str:
        """
        Construit le prompt initial pour generer une preuve.
        
        Args:
            theorem_statement: Le theoreme a prouver (sans 'by sorry')
            context: Contexte optionnel (imports, hypotheses, variables)
        
        Returns:
            Le prompt structure
        """
        prompt_parts = ["Ecris une preuve Lean 4 pour le theoreme suivant:\n"]
        
        # Ajouter le contexte si disponible
        if context:
            if "imports" in context:
                prompt_parts.append(f"Imports disponibles:\n{context['imports']}\n")
            if "variables" in context:
                prompt_parts.append(f"Variables:\n{context['variables']}\n")
            if "hypotheses" in context:
                prompt_parts.append(f"Hypotheses:\n{context['hypotheses']}\n")
        
        # Ajouter le theoreme
        prompt_parts.append(f"Theoreme:\n```lean\n{theorem_statement}\n```\n")

        # Instructions - adapt based on Mathlib availability
        has_mathlib = context and "imports" in context and "Mathlib" in context["imports"]
        if has_mathlib:
            prompt_parts.append(
                "\nDonne le code Lean complet avec la preuve (remplace 'by sorry' par les tactiques).\n"
                "Utilise les tactiques Mathlib si appropriees (ring, linarith, omega, simp)."
            )
        else:
            prompt_parts.append(
                "\nDonne le code Lean complet avec la preuve (remplace 'by sorry' par les tactiques).\n"
                "IMPORTANT: Mathlib n'est PAS disponible. Utilise uniquement les tactiques standard:\n"
                "- rfl, simp, omega (pour arithmetique entiere)\n"
                "- exact (avec lemmes standard: Nat.add_comm, Nat.mul_comm, etc.)\n"
                "- apply, intro, constructor, cases, induction, rw\n"
                "- NE PAS utiliser ring, linarith, norm_num (ils necessitent Mathlib)"
            )

        return "\n".join(prompt_parts)
    
    @staticmethod
    def build_correction_prompt(
        theorem_statement: str,
        previous_proof: str,
        error_message: str,
        iteration: int
    ) -> str:
        """
        Construit le prompt de correction base sur une erreur.
        
        Args:
            theorem_statement: Le theoreme original
            previous_proof: La preuve qui a echoue
            error_message: L'erreur Lean
            iteration: Numero de l'iteration
        
        Returns:
            Le prompt de correction
        """
        return f"""La preuve suivante contient une erreur (iteration {iteration}):

Theoreme:
```lean
{theorem_statement}
```

Preuve actuelle:
```lean
{previous_proof}
```

Erreur Lean:
```
{error_message}
```

Analyse l'erreur et fournis une preuve CORRIGEE complete.
Donne UNIQUEMENT le code Lean corrige, sans explications."""
    
    @staticmethod
    def build_few_shot_prompt(
        theorem_statement: str,
        examples: List[Dict[str, str]]
    ) -> str:
        """
        Construit un prompt few-shot avec exemples similaires.
        
        Args:
            theorem_statement: Le theoreme a prouver
            examples: Liste de {theorem, proof} exemples
        
        Returns:
            Le prompt few-shot
        """
        prompt_parts = ["Voici des exemples de preuves Lean 4:\n"]
        
        for i, example in enumerate(examples, 1):
            prompt_parts.append(f"\nExemple {i}:")
            prompt_parts.append(f"```lean\n{example['theorem']}\n{example['proof']}\n```")
        
        prompt_parts.append(f"\nMaintenant, prouve ce theoreme en suivant le meme style:")
        prompt_parts.append(f"```lean\n{theorem_statement}\n```")
        
        return "\n".join(prompt_parts)
    
    @staticmethod
    def extract_lean_code(llm_response: str) -> str:
        """
        Extrait le code Lean d'une reponse LLM.
        
        Gere plusieurs formats :
        - ```lean ... ```
        - ``` ... ```
        - Code direct sans backticks
        
        Args:
            llm_response: La reponse complete du LLM
        
        Returns:
            Le code Lean extrait et nettoye
        """
        # Cas 1: Code dans ```lean ... ```
        lean_match = re.search(r'```lean\s*(.*?)\s*```', llm_response, re.DOTALL)
        if lean_match:
            return lean_match.group(1).strip()
        
        # Cas 2: Code dans ``` ... ``` (sans langue specifiee)
        code_match = re.search(r'```\s*(.*?)\s*```', llm_response, re.DOTALL)
        if code_match:
            return code_match.group(1).strip()
        
        # Cas 3: Pas de backticks, prendre tout le contenu
        # Nettoyer les lignes de commentaire explicatif
        lines = []
        for line in llm_response.split('\n'):
            # Garder les lignes qui ressemblent a du code Lean
            if line.strip() and not line.strip().startswith(('Voici', 'La preuve', 'Explication')):
                lines.append(line)
        
        return '\n'.join(lines).strip()

# Exemples d'utilisation

@dataclass
class ErrorInfo:
    """Information sur une erreur Lean."""
    message: str
    line: Optional[int] = None
    column: Optional[int] = None
    severity: str = "error"

class ProofVerifier:
    """
    Verifie les preuves Lean avec lean_runner.py.
    
    Gere :
    - Verification formelle avec multiple backends (subprocess, wsl, leandojo)
    - Parsing des erreurs Lean (ligne, colonne, message)
    - Feedback structure pour le LLM
    """
    
    def __init__(self, backend: str = "auto", timeout: int = 30):
        """
        Initialise le verificateur.
        
        Args:
            backend: Backend LeanRunner ("subprocess", "wsl", "leandojo", "auto")
            timeout: Timeout en secondes pour la verification
        """
        self.backend = backend
        self.timeout = timeout
        
        # Initialiser LeanRunner
        try:
            # LeanRunner is defined above in this module
            self.runner = LeanRunner(backend=backend, timeout=timeout)
            self.available = True
            print(f"LeanRunner initialise (backend: {self.runner.backend.value})")
        except Exception as e:
            self.runner = None
            self.available = False
            print(f"[Warning] LeanRunner non disponible: {e}")
            print("  -> Les verifications seront simulees")
    
    def verify(self, code: str) -> 'LeanResult':
        """
        Verifie le code Lean.
        
        Args:
            code: Le code Lean complet a verifier
        
        Returns:
            LeanResult avec success, output, errors, etc.
        """
        if not self.available:
            # Simulation si LeanRunner non disponible
            return self._simulate_verification(code)
        
        try:
            result = self.runner.run(code)
            return result
        except Exception as e:
            # En cas d'erreur d'execution
            from lean_runner import LeanResult
            return LeanResult(
                success=False,
                output="",
                errors=f"Erreur d'execution: {str(e)}",
                code=code,
                exit_code=-1,
                backend=self.backend
            )
    
    def _simulate_verification(self, code: str) -> 'LeanResult':
        """Simule une verification (pour tests sans Lean)."""
        from lean_runner import LeanResult
        
        # Heuristique simple : si contient 'sorry', echec
        if 'sorry' in code:
            return LeanResult(
                success=False,
                output="",
                errors="Main.lean:1:0: error: declaration uses 'sorry'",
                code=code,
                exit_code=1,
                backend="simulation"
            )
        
        # Sinon, simuler succes
        return LeanResult(
            success=True,
            output="",
            errors="",
            code=code,
            exit_code=0,
            backend="simulation"
        )
    
    def parse_errors(self, result: 'LeanResult') -> List[ErrorInfo]:
        """
        Parse les erreurs Lean du resultat.
        
        Format typique:
        Main.lean:10:5: error: unknown identifier 'foo'
        Main.lean:12:0: warning: unused variable
        
        Args:
            result: Le resultat de verification
        
        Returns:
            Liste d'ErrorInfo structures
        """
        errors = []
        
        if not result.errors:
            return errors
        
        # Pattern pour erreurs Lean : filename:line:column: severity: message
        error_pattern = re.compile(r'([^:]+):(\d+):(\d+):\s*(error|warning):\s*(.+)')
        
        for line in result.errors.split('\n'):
            match = error_pattern.match(line.strip())
            if match:
                _, line_num, col_num, severity, message = match.groups()
                errors.append(ErrorInfo(
                    message=message.strip(),
                    line=int(line_num),
                    column=int(col_num),
                    severity=severity
                ))
            elif line.strip() and ('error' in line.lower() or 'warning' in line.lower()):
                # Erreur sans format standard
                errors.append(ErrorInfo(
                    message=line.strip(),
                    severity="error" if "error" in line.lower() else "warning"
                ))
        
        return errors
    
    def get_readable_feedback(self, result: 'LeanResult') -> str:
        """
        Formate le feedback pour le LLM.
        
        Args:
            result: Le resultat de verification
        
        Returns:
            Message de feedback structure
        """
        if result.success:
            return "Preuve verifiee avec succes!"
        
        errors = self.parse_errors(result)
        
        if not errors:
            # Erreur generique sans parsing
            return f"Echec de verification:\n{result.errors}"
        
        # Formater les erreurs de maniere pedagogique
        feedback_parts = [f"La preuve contient {len(errors)} erreur(s):"]
        
        for i, error in enumerate(errors, 1):
            location = f" (ligne {error.line}, col {error.column})" if error.line else ""
            feedback_parts.append(f"\n{i}. {error.severity.upper()}{location}:")
            feedback_parts.append(f"   {error.message}")
        
        return '\n'.join(feedback_parts)


@dataclass
class ProofAttempt:
    """Une tentative de preuve dans la boucle de feedback."""
    iteration: int
    code: str
    result: 'LeanResult'
    llm_response: LLMResponse
    timestamp: float

@dataclass
class ProofResult:
    """Resultat final d'une session de preuve."""
    success: bool
    theorem_statement: str
    final_proof: Optional[str]
    attempts: List[ProofAttempt]
    total_iterations: int
    total_time_ms: float
    llm_provider: str
    llm_model: str
    
    def get_metrics(self) -> Dict[str, Any]:
        """Extrait les metriques de la session."""
        total_tokens = sum(
            attempt.llm_response.tokens_used["total"]
            for attempt in self.attempts
        )
        avg_latency = sum(
            attempt.llm_response.latency_ms
            for attempt in self.attempts
        ) / len(self.attempts) if self.attempts else 0
        
        return {
            "success": self.success,
            "iterations": self.total_iterations,
            "total_time_ms": self.total_time_ms,
            "total_tokens": total_tokens,
            "avg_llm_latency_ms": avg_latency,
            "provider": self.llm_provider,
            "model": self.llm_model
        }

class ProofGenerator:
    """
    Generateur de preuves avec feedback loop LLM ↔ Lean.
    
    Orchestration complete :
    1. LLM genere une preuve initiale
    2. LeanRunner verifie formellement
    3. Si echec : LLM corrige base sur l'erreur
    4. Repeter jusqu'a succes ou max_iterations
    """
    
    def __init__(
        self,
        llm_client: LLMClient,
        verifier: ProofVerifier,
        max_iterations: int = 5,
        temperature: float = 0.3
    ):
        """
        Initialise le generateur.
        
        Args:
            llm_client: Client LLM (OpenAI ou Anthropic)
            verifier: Verificateur Lean
            max_iterations: Nombre max d'iterations
            temperature: Temperature pour la generation
        """
        self.llm = llm_client
        self.verifier = verifier
        self.max_iterations = max_iterations
        self.temperature = temperature
    
    def prove(
        self,
        theorem_statement: str,
        context: Optional[Dict[str, Any]] = None,
        verbose: bool = True
    ) -> ProofResult:
        """
        Tente de prouver un theoreme avec feedback iteratif.
        
        Args:
            theorem_statement: Le theoreme a prouver (sans 'by sorry')
            context: Contexte optionnel (imports, variables, hypotheses)
            verbose: Afficher les details
        
        Returns:
            ProofResult avec succes, preuve, historique et metriques
        """
        start_time = time.time()
        attempts = []
        current_code = None
        
        if verbose:
            print(f"\n{'='*60}")
            print(f"TENTATIVE DE PREUVE")
            print(f"{'='*60}")
            print(f"Theoreme: {theorem_statement[:80]}...")
            print(f"Provider: {self.llm.provider} / {self.llm.model}")
            print(f"Max iterations: {self.max_iterations}")
            print(f"{'='*60}\n")
        
        for iteration in range(1, self.max_iterations + 1):
            if verbose:
                print(f"--- Iteration {iteration}/{self.max_iterations} ---")
            
            # Etape 1: Generer ou corriger
            if current_code is None:
                # Generation initiale
                prompt = LeanProofPrompt.build_initial_prompt(theorem_statement, context)
                if verbose:
                    print("Generation initiale...")
            else:
                # Correction base sur erreur
                last_error = attempts[-1].result.errors
                prompt = LeanProofPrompt.build_correction_prompt(
                    theorem_statement,
                    current_code,
                    last_error,
                    iteration
                )
                if verbose:
                    print(f"Correction (erreur precedente: {last_error[:60]}...)")
            
            # Appeler le LLM
            # Select system prompt based on Mathlib availability
            has_mathlib = context and "imports" in context and "Mathlib" in context["imports"]
            system_prompt = (
                LeanProofPrompt.SYSTEM_PROMPT_MATHLIB if has_mathlib
                else LeanProofPrompt.SYSTEM_PROMPT
            )
            try:
                llm_response = self.llm.generate(
                    prompt,
                    system_prompt=system_prompt,
                    temperature=self.temperature
                )
                
                # Extraire le code Lean
                current_code = LeanProofPrompt.extract_lean_code(llm_response.content)
                
                if verbose:
                    print(f"LLM genere ({llm_response.latency_ms:.0f}ms, "
                          f"{llm_response.tokens_used['total']} tokens)")
                    print(f"Code:\n{current_code[:150]}...")
                
            except Exception as e:
                if verbose:
                    print(f"[ERREUR LLM] {e}")
                break
            
            # Etape 2: Verifier avec Lean
            # Ajouter les imports du contexte si necessaire
            code_to_verify = current_code
            if context and "imports" in context:
                imports_str = context["imports"]
                # Verifier si les imports sont deja dans le code
                if imports_str not in current_code:
                    code_to_verify = f"{imports_str}\n\n{current_code}"

            lean_result = self.verifier.verify(code_to_verify)
            
            # Enregistrer la tentative
            attempts.append(ProofAttempt(
                iteration=iteration,
                code=current_code,
                result=lean_result,
                llm_response=llm_response,
                timestamp=time.time()
            ))
            
            if lean_result.success:
                # SUCCES !
                total_time = (time.time() - start_time) * 1000
                if verbose:
                    print(f"\n[SUCCES] Preuve verifiee en {iteration} iteration(s)!")
                    print(f"Temps total: {total_time:.0f}ms")
                
                return ProofResult(
                    success=True,
                    theorem_statement=theorem_statement,
                    final_proof=current_code,
                    attempts=attempts,
                    total_iterations=iteration,
                    total_time_ms=total_time,
                    llm_provider=self.llm.provider,
                    llm_model=self.llm.model
                )
            else:
                # Echec - afficher feedback
                if verbose:
                    feedback = self.verifier.get_readable_feedback(lean_result)
                    print(f"[ECHEC] {feedback[:100]}...")
        
        # Echec apres max_iterations
        total_time = (time.time() - start_time) * 1000
        if verbose:
            print(f"\n[ECHEC] Pas de preuve trouvee apres {self.max_iterations} iterations")
            print(f"Temps total: {total_time:.0f}ms")
        
        return ProofResult(
            success=False,
            theorem_statement=theorem_statement,
            final_proof=current_code,
            attempts=attempts,
            total_iterations=self.max_iterations,
            total_time_ms=total_time,
            llm_provider=self.llm.provider,
            llm_model=self.llm.model
        )
