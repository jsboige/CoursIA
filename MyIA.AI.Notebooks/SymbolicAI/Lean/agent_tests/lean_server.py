"""Lean verification server using lake build with shared content-hash cache.

Provides LeanVerifier class with verify_project_file() interface
expected by multi_agent_proof.py. Build results are cached by file content
hash and shared across all LeanVerifier instances.

Lake invocation (2026-05-11): the original implementation called WSL with
``source ~/.elan/env && lake build`` — but on this machine elan is installed
Windows-side under ``%USERPROFILE%/.elan/bin``, not in any WSL distro. The
WSL ``source`` failed silently (exit 1, output empty), short-circuited the
``&&``, and the verifier saw 0 errors → reported SUCCESS without ever
building. ``_resolve_lake_command`` now prefers Windows-side ``lake.exe`` so
prover builds and operator builds both write to the same ``.lake/build/lib``
cache (verified ~2s for a Voting.lean cache hit).
"""

import hashlib
import os
import platform
import subprocess
import re
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def _to_wsl_path(win_path: str) -> str:
    """Convert ``C:\\foo\\bar`` to ``/mnt/c/foo/bar`` for use inside WSL bash."""
    p = str(win_path).replace("\\", "/")
    if len(p) >= 2 and p[1] == ":":
        return f"/mnt/{p[0].lower()}{p[2:]}"
    return p


def _resolve_lake_command(extra_args: List[str], cwd: str = None) -> Tuple[List[str], dict]:
    """Return (argv, env) for invoking ``lake <extra_args>``.

    Strategy (in order):
    1. ``$LEAN_LAKE_BIN`` if set and executable — operator override.
    2. Native Windows ``lake.exe`` under ``%USERPROFILE%/.elan/bin`` — fastest
       path, shares the on-disk ``.lake/build`` cache with manual builds.
    3. WSL ``lake`` if the Linux toolchain is available (sourced from
       ``~/.elan/env`` inside WSL).
    4. Bare ``lake`` on PATH — assumes lake is otherwise reachable.

    The returned env injects elan's bin directory into PATH for option 2 so
    sub-tools (lean, leanc) resolve without a separate elan setup.
    """
    env = os.environ.copy()

    override = os.getenv("LEAN_LAKE_BIN")
    if override and Path(override).exists():
        return [override, *extra_args], env

    # WSL preferred when LEAN_USE_WSL=1 (Conway KS Pilier 1 #1651: WSL .lake
    # cache is already warm, Windows lake.exe would trigger 1-2h Mathlib
    # rebuild because OS-specific .c IR files differ).
    if os.getenv("LEAN_USE_WSL") == "1":
        cd_prefix = f"cd '{_to_wsl_path(cwd)}' && " if cwd else ""
        wsl_cmd = cd_prefix + "source ~/.elan/env 2>/dev/null; lake " + " ".join(
            f"'{a}'" for a in extra_args
        )
        return ["wsl", "-d", "Ubuntu", "bash", "-lc", wsl_cmd], env

    if platform.system() == "Windows":
        elan_bin = Path.home() / ".elan" / "bin"
        lake_exe = elan_bin / "lake.exe"
        if lake_exe.exists():
            env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"
            return [str(lake_exe), *extra_args], env

    return ["lake", *extra_args], env


def _has_lakefile(p: Path) -> bool:
    """True if directory ``p`` holds a Lake manifest (lakefile.lean/.toml)."""
    return (p / "lakefile.lean").exists() or (p / "lakefile.toml").exists()


def _find_lake_root(start: Path) -> Optional[Path]:
    """Walk up from ``start`` to the nearest directory holding a lakefile.

    Returns the Lake root, or ``None`` if none is found before the filesystem
    root. Used to re-root callers that derived a too-deep ``project_dir`` from
    a nested file path (e.g. ``conway_lean/Conway`` for a ``Conway/Life/*``
    file, which holds no lakefile).
    """
    cur = start
    while True:
        if _has_lakefile(cur):
            return cur
        if cur == cur.parent:
            return None
        cur = cur.parent


class LeanVerifier:
    """Verify Lean 4 files using lake build with content-hash caching.

    Cache is class-level (shared across instances). Key = sha256 of ALL .lean
    files in the target module's directory. This means:
    - Same content → instant cache hit (no lake build)
    - Any .lean change → cache miss → fresh build
    - Cache survives across prover iterations and sessions
    """

    _cache: Dict[str, dict] = {}

    # Cumulative wall-clock seconds spent inside actual `lake build` subprocess
    # calls (cache hits never reach the builder, so they don't count). Class-level
    # so every verifier instance — including the latch-verifier the workflow
    # spins up — accrues to the SAME counter. The prover's wall-clock supervisor
    # reads this to credit build time back to the reasoning budget ("pause the
    # timer during builds", user mandate 2026-06-21): a long compile must not
    # eat the time the agents need to reason on hard nuts.
    _total_build_seconds: float = 0.0

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
        # The prover derives project_dir as `<file>.parent.parent`, which is the
        # Lake root only for files directly under the top package (e.g.
        # `Conway/Nim.lean` -> root `conway_lean`). For files nested deeper (e.g.
        # `Conway/Life/HashlifeCorrectness.lean`) that yields `conway_lean/Conway`,
        # which holds no lakefile. Walk up to the real Lake root and re-root
        # `relative_path` with the directory names we passed (so the module name
        # resolves to `Conway.Life.HashlifeCorrectness`). Backward-compatible: a
        # project_dir that already holds the lakefile is used unchanged.
        if not _has_lakefile(project):
            cur = project
            prefix = []
            while cur != cur.parent and not _has_lakefile(cur):
                prefix.insert(0, cur.name)
                cur = cur.parent
            if _has_lakefile(cur):
                project = cur
                relative_path = "/".join(prefix + [relative_path])
            else:
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
        """Execute ``lake build`` for a module, sharing the on-disk cache.

        Uses Windows-side lake.exe by default (see ``_resolve_lake_command``);
        the cwd is the Lake project root so ``.lake/build/lib/<module>.olean``
        is written/read at the same path as manual builds.

        Timeout is 600s (increased from 300s). WSL builds via ``/mnt/c/``
        suffer 9P/NTFS overhead (~10x slower than native), so a cold build
        can exceed the original 300s ceiling. See DEMO 35/36 traces.
        """
        module_name = relative_path.replace("/", ".").replace("\\", ".")
        if module_name.endswith(".lean"):
            module_name = module_name[:-5]

        cmd, env = _resolve_lake_command(["build", "-R", module_name], cwd=str(project))

        try:
            start = time.time()
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=600,
                env=env,
            )
            duration = time.time() - start
            # Credit this compile against the prover's reasoning budget.
            LeanVerifier._total_build_seconds += duration

            output = result.stdout + "\n" + result.stderr

            # Filter out the stale-config warning that lake emits when the
            # cached configuration is out of date — it is NOT a proof error.
            config_stale = "compiled configuration is invalid" in output
            if config_stale:
                output_lines = []
                for line in output.split("\n"):
                    if "compiled configuration is invalid" not in line:
                        output_lines.append(line)
                output = "\n".join(output_lines)

            errors = self._extract_errors(output)

            # If lake itself failed (returncode != 0) but no parsed errors,
            # surface a synthetic error so callers don't think this was a
            # silent success — protects against the regression where missing
            # toolchain returned 0 errors and was treated as success.
            # Exception: if the only issue was a stale config (now fixed by
            # -R), and -R succeeded (returncode 0), this branch is skipped.
            if not errors and result.returncode != 0 and not config_stale:
                errors = [
                    f"lake exit={result.returncode}; output: {output[:500] or '(empty)'}"
                ]

            return {
                "success": len(errors) == 0,
                "errors": "\n".join(errors),
                "raw_output": output,
                "build_time_s": round(duration, 1),
                "lake_cmd": cmd[0],
            }
        except subprocess.TimeoutExpired:
            return {"success": False, "errors": "lake build timed out (300s)", "raw_output": ""}
        except FileNotFoundError:
            return {
                "success": False,
                "errors": (
                    f"lake not found (tried {cmd[0]!r}). Set LEAN_LAKE_BIN or install "
                    f"elan, then retry."
                ),
                "raw_output": "",
            }

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
        cmd, env = _resolve_lake_command(["env", "lean", "--stdin"], cwd=str(project))

        try:
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
        # The persistent verifier singleton is pinned to whatever project_dir the
        # first caller passed — for a nested file that is a too-deep dir with no
        # lakefile (e.g. `conway_lean/Conway`). `verify_project_file` re-roots per
        # call, so `search_lean` self-heals the same way. Walk up to the real Lake
        # root (no-op when project already holds a lakefile).
        if not _has_lakefile(project):
            root = _find_lake_root(project)
            if root is not None:
                project = root

        # Feed the search snippet to `lake env lean --stdin` — the same fast path
        # `verify_project_file`/`check_axioms` use. The prior implementation wrote a
        # temp module inside the source tree and ran `lake build <module>`, which
        # forces Lake to traverse the whole dependency graph (Mathlib) before
        # elaborating: on a heavy project that overruns the timeout and returns zero
        # suggestions every time (root cause of `actual_iterations: 0` on the P4/P5
        # traces). `lake env lean` sets LEAN_PATH from the build dir, so `import`
        # resolves against prebuilt oleans with no graph walk (~4 s vs 120 s here).
        snippet = (
            f"import {module_name}\n"
            f"example : {goal} := by\n"
            f"  {tactic}\n"
        )
        cmd, env = _resolve_lake_command(["env", "lean", "--stdin"], cwd=str(project))
        try:
            result = subprocess.run(
                cmd,
                cwd=str(project),
                capture_output=True,
                text=True,
                timeout=120,
                env=env,
                input=snippet,
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

    @staticmethod
    def _extract_suggestions(output: str, tactic: str) -> list:
        """Extract proof suggestions from exact?/apply? output."""
        def _clean(s: str) -> str:
            # Drop a leading "[apply]"/"[exact]" tag Lean prepends to the tactic.
            s = s.strip()
            if s.startswith("[") and "]" in s:
                s = s[s.index("]") + 1:].strip()
            return s.rstrip(",").strip()

        suggestions = []
        lines = output.split("\n")
        for i, raw in enumerate(lines):
            line = raw.strip()
            if "Try this:" in line:
                after = line.split("Try this:")[-1].strip()
                if after:
                    suggestions.append({"tactic": _clean(after), "source": tactic})
                    continue
                # Two-line form: "Try this:" alone, tactic on the next non-empty,
                # non-diagnostic line (e.g. "  [apply] exact True.intro").
                for nxt in lines[i + 1:]:
                    n = nxt.strip()
                    if not n:
                        continue
                    if n.lower().startswith(("warning:", "error:")) or ": error:" in n:
                        break
                    suggestions.append({"tactic": _clean(n), "source": tactic})
                    break
            elif tactic in ("exact?", "apply?") and "error" not in line.lower():
                cand = _clean(line)
                if cand.startswith(("exact ", "apply ", "refine ")):
                    suggestions.append({"tactic": cand, "source": tactic})
        uniq = {}
        for s in suggestions:
            if s["tactic"]:
                uniq.setdefault(s["tactic"], s)
        return list(uniq.values())

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
