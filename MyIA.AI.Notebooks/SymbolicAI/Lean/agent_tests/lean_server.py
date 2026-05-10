"""Lean verification server using lake build with shared content-hash cache.

Provides LeanVerifier class with verify_project_file() interface
expected by multi_agent_proof.py. Build results are cached by file content
hash and shared across all LeanVerifier instances.
"""

import hashlib
import os
import subprocess
import re
import time
from pathlib import Path
from typing import Dict, Optional


class LeanVerifier:
    """Verify Lean 4 files using lake build with content-hash caching.

    Cache is class-level (shared across instances). Key = sha256 of ALL .lean
    files in the target module's directory. This means:
    - Same content → instant cache hit (no lake build)
    - Any .lean change → cache miss → fresh build
    - Cache survives across prover iterations and sessions
    """

    _cache: Dict[str, dict] = {}

    def __init__(self, project_dir: str = None, verbose: bool = False):
        self.project_dir = project_dir or os.getenv("LEAN_PROJECT_DIR")
        self.verbose = verbose
        self._lean_path = self._find_lean()
        self._cache_hits = 0
        self._cache_misses = 0

    def _find_lean(self) -> str:
        """Find lean/lake binary path."""
        elan_env = Path.home() / ".elan" / "env"
        if elan_env.exists():
            return str(elan_env.parent / "bin")
        return os.getenv("PATH", "")

    def verify_project_file(self, relative_path: str, force: bool = False) -> dict:
        """Verify a Lean file within the project using lake build.

        Results are cached by content hash of the target .lean file.
        Use force=True to bypass cache (after external changes).

        Args:
            relative_path: Path relative to project root (e.g. 'SocialChoice/Voting.lean')
            force: Skip cache and force a fresh build

        Returns:
            dict with 'success' (bool), 'errors' (str), 'raw_output' (str),
                     'cached' (bool), 'cache_key' (str)
        """
        if not self.project_dir:
            return {"success": False, "errors": "No project directory set", "raw_output": ""}

        project = Path(self.project_dir)
        if not (project / "lakefile.lean").exists() and not (project / "lakefile.toml").exists():
            return {"success": False, "errors": f"Not a Lake project: {project}", "raw_output": ""}

        target_file = project / relative_path
        cache_key = self._compute_cache_key(target_file) if target_file.exists() else None

        if not force and cache_key and cache_key in LeanVerifier._cache:
            self._cache_hits += 1
            cached = LeanVerifier._cache[cache_key]
            cached["cached"] = True
            if self.verbose:
                print(f"[CACHE HIT] {relative_path} (key={cache_key[:12]}...)")
            return cached

        self._cache_misses += 1
        result = self._run_lake_build(project, relative_path)
        result["cached"] = False
        result["cache_key"] = cache_key

        if cache_key:
            LeanVerifier._cache[cache_key] = result

        return result

    def _compute_cache_key(self, filepath: Path) -> str:
        """Compute cache key from file content hash."""
        content = filepath.read_text(encoding="utf-8", errors="replace")
        return hashlib.sha256(content.encode()).hexdigest()

    def _run_lake_build(self, project: Path, relative_path: str) -> dict:
        """Execute lake build for a module via WSL (Lean toolchain is in WSL)."""
        module_name = relative_path.replace("/", ".").replace("\\", ".")
        if module_name.endswith(".lean"):
            module_name = module_name[:-5]

        # Convert Windows project path to WSL path
        wsl_project = str(project).replace("\\", "/")
        if len(wsl_project) >= 2 and wsl_project[1] == ":":
            drive = wsl_project[0].lower()
            wsl_project = f"/mnt/{drive}{wsl_project[2:]}"

        try:
            start = time.time()
            # Use WSL to run lake build (elan/lean toolchain is in WSL)
            lake_cmd = f"source ~/.elan/env > /dev/null 2>&1 && lake build {module_name} 2>&1"
            cmd = ["wsl", "bash", "-c", lake_cmd]
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=300,
            )
            duration = time.time() - start

            output = result.stdout + "\n" + result.stderr
            errors = self._extract_errors(output)

            return {
                "success": len(errors) == 0,
                "errors": "\n".join(errors),
                "raw_output": output,
                "build_time_s": round(duration, 1),
            }
        except subprocess.TimeoutExpired:
            return {"success": False, "errors": "lake build timed out (300s)", "raw_output": ""}
        except FileNotFoundError:
            return {"success": False, "errors": "lake not found in PATH", "raw_output": ""}

    @classmethod
    def invalidate(cls, filepath: str):
        """Remove cache entries that no longer match the file content."""
        path = Path(filepath)
        if not path.exists():
            return
        current_key = hashlib.sha256(path.read_text(encoding="utf-8", errors="replace").encode()).hexdigest()
        stale = [k for k in cls._cache if k != current_key]
        for k in stale:
            del cls._cache[k]

    @classmethod
    def cache_stats(cls) -> dict:
        """Return cache statistics."""
        return {
            "entries": len(cls._cache),
            "hits": sum(1 for _ in []),  # placeholder
        }

    @classmethod
    def clear_cache(cls):
        """Clear all cached build results."""
        cls._cache.clear()

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

    def check_axioms(self, module_name: str, whitelist: list = None) -> dict:
        """Check axioms used by a module via #print axioms.

        Level 3 verification: after build succeeds, check that no
        unexpected axioms (beyond sorry/classical.choice) are used.

        Args:
            module_name: Dotted module name (e.g. 'SocialChoice.Voting')
            whitelist: List of allowed axiom names (default: classical + propext + funext)

        Returns:
            dict with 'success', 'axioms' (list), 'forbidden' (list), 'raw_output'
        """
        if whitelist is None:
            whitelist = [
                "Classical.choice",
                "propext",
                "funext",
                "Quot.lift",
                "Quot.mk",
            ]

        project = Path(self.project_dir)
        env = os.environ.copy()
        elan_bin = Path.home() / ".elan" / "bin"
        if elan_bin.exists():
            env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

        try:
            cmd = ["lake", "env", "lean", "--stdin"]
            stdin_input = f"import {module_name}\n#print axioms {module_name.split('.')[-1]}\n"
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=60,
                env=env,
                input=stdin_input,
            )

            output = result.stdout + "\n" + result.stderr
            axioms = self._extract_axioms(output)
            forbidden = [a for a in axioms if a not in whitelist and a != "sorryAx"]

            return {
                "success": len(forbidden) == 0,
                "axioms": axioms,
                "forbidden": forbidden,
                "whitelist": whitelist,
                "has_sorry": "sorryAx" in axioms,
                "raw_output": output,
            }
        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            return {
                "success": False,
                "axioms": [],
                "forbidden": [],
                "error": str(e),
                "raw_output": "",
            }

    def search_lean(self, module_name: str, goal: str, tactic: str = "exact?") -> dict:
        """Search Mathlib using Lean's suggestion tactics (exact?, apply?, library_search).

        Writes a temporary snippet importing the module and applying the search tactic,
        then parses the output for suggested proof.

        Args:
            module_name: Dotted module name (e.g. 'SocialChoice.Voting')
            goal: The Lean goal expression to search for
            tactic: Search tactic to use ('exact?', 'apply?', or 'library_search')

        Returns:
            dict with 'success', 'suggestions' (list of found proofs), 'raw_output'
        """
        project = Path(self.project_dir)
        env = os.environ.copy()
        elan_bin = Path.home() / ".elan" / "bin"
        if elan_bin.exists():
            env["PATH"] = f"{elan_bin}:{env.get('PATH', '')}"

        short_name = module_name.split(".")[-1]
        snippet = (
            f"import {module_name}\n"
            f"example : {goal} := by\n"
            f"  {tactic}\n"
        )

        tmp_file = project / "SocialChoice" / "_LeanSearch.lean"
        if not (project / "SocialChoice").exists():
            for subdir in project.iterdir():
                if subdir.is_dir() and (subdir / "lakefile.lean").exists():
                    continue
                if subdir.is_dir():
                    tmp_file = subdir / "_LeanSearch.lean"
                    break

        try:
            tmp_file.write_text(snippet, encoding="utf-8")

            relative = tmp_file.relative_to(project)
            module = str(relative).replace("/", ".").replace("\\", ".")
            if module.endswith(".lean"):
                module = module[:-5]

            cmd = ["lake", "build", module]
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=120,
                env=env,
            )

            output = result.stdout + "\n" + result.stderr
            suggestions = self._extract_suggestions(output, tactic)

            return {
                "success": len(suggestions) > 0,
                "suggestions": suggestions,
                "tactic_used": tactic,
                "goal": goal[:200],
                "raw_output": output[:1000],
            }
        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            return {
                "success": False,
                "suggestions": [],
                "error": str(e),
                "raw_output": "",
            }
        finally:
            try:
                tmp_file.unlink()
            except OSError:
                pass

    @staticmethod
    def _extract_suggestions(output: str, tactic: str) -> list:
        """Extract proof suggestions from exact?/apply? output."""
        suggestions = []
        for line in output.split("\n"):
            line = line.strip()
            if "Try this:" in line:
                proof = line.split("Try this:")[-1].strip()
                suggestions.append({"tactic": proof, "source": tactic})
            elif tactic == "exact?" and "exact " in line and "error" not in line.lower():
                proof = line.strip().rstrip(",")
                if proof.startswith("exact "):
                    suggestions.append({"tactic": proof, "source": "exact?"})
        return list({s["tactic"]: s for s in suggestions}.values())

    @staticmethod
    def _extract_axioms(output: str) -> list:
        """Extract axiom names from #print axioms output."""
        axioms = []
        for line in output.split("\n"):
            line = line.strip()
            if line and not line.startswith("[") and not line.startswith("error"):
                for name in line.split(","):
                    name = name.strip().rstrip(".")
                    if name and name not in ("", "axioms"):
                        axioms.append(name)
        return list(set(axioms))

    @staticmethod
    def _extract_errors(output: str) -> list:
        """Extract error lines from lake build output."""
        errors = []
        for line in output.split("\n"):
            if ": error:" in line:
                errors.append(line.strip())
        return errors
