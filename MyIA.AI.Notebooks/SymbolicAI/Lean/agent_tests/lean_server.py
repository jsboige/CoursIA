"""Minimal Lean verification server using lake build.

Provides LeanVerifier class with verify_project_file() interface
expected by multi_agent_proof.py.
"""

import os
import subprocess
import re
from pathlib import Path


class LeanVerifier:
    """Verify Lean 4 files using lake build."""

    def __init__(self, project_dir: str = None, verbose: bool = False):
        self.project_dir = project_dir or os.getenv("LEAN_PROJECT_DIR")
        self.verbose = verbose
        self._lean_path = self._find_lean()

    def _find_lean(self) -> str:
        """Find lean/lake binary path."""
        elan_env = Path.home() / ".elan" / "env"
        if elan_env.exists():
            return str(elan_env.parent / "bin")
        return os.getenv("PATH", "")

    def verify_project_file(self, relative_path: str) -> dict:
        """Verify a Lean file within the project using lake build.

        Args:
            relative_path: Path relative to project root (e.g. 'CooperativeGames/Shapley.lean')

        Returns:
            dict with 'success' (bool), 'errors' (str), 'raw_output' (str)
        """
        if not self.project_dir:
            return {"success": False, "errors": "No project directory set", "raw_output": ""}

        project = Path(self.project_dir)
        if not (project / "lakefile.lean").exists() and not (project / "lakefile.toml").exists():
            return {"success": False, "errors": f"Not a Lake project: {project}", "raw_output": ""}

        module_name = relative_path.replace("/", ".").replace("\\", ".")
        if module_name.endswith(".lean"):
            module_name = module_name[:-5]

        env = os.environ.copy()
        elan_bin = Path.home() / ".elan" / "bin"
        if elan_bin.exists():
            env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

        try:
            cmd = ["lake", "build", module_name]
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=300,
                env=env,
            )

            output = result.stdout + "\n" + result.stderr
            errors = self._extract_errors(output)

            return {
                "success": len(errors) == 0,
                "errors": "\n".join(errors),
                "raw_output": output,
            }
        except subprocess.TimeoutExpired:
            return {"success": False, "errors": "lake build timed out (300s)", "raw_output": ""}
        except FileNotFoundError:
            return {"success": False, "errors": "lake not found in PATH", "raw_output": ""}

    def verify(self, code: str) -> dict:
        """Verify standalone Lean code (writes to temp file in project).

        Args:
            code: Complete Lean source code to verify.

        Returns:
            dict with 'success', 'errors', 'backend'
        """
        if not self.project_dir:
            return {"success": False, "errors": "No project directory set", "backend": "lean_server"}

        project = Path(self.project_dir)
        tmp_file = project / "CooperativeGames" / "_TempVerify.lean"

        try:
            tmp_file.write_text(code, encoding="utf-8")
            result = self.verify_project_file("CooperativeGames/_TempVerify.lean")
            result["backend"] = "lean_server"
            return result
        finally:
            try:
                tmp_file.unlink()
            except OSError:
                pass

    @staticmethod
    def _extract_errors(output: str) -> list:
        """Extract error lines from lake build output."""
        errors = []
        for line in output.split("\n"):
            if ": error:" in line:
                errors.append(line.strip())
        return errors
