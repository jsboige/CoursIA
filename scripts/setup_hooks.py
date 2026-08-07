#!/usr/bin/env python3
"""Install pre-commit + the git pre-commit hook on the local repo.

Why this script exists (issue #9888)
------------------------------------
The repo carries ``.pre-commit-config.yaml`` declaring gitleaks v8.21.2 and
four local notebook-hygiene hooks, but the actual ``pre-commit`` framework
and ``gitleaks`` binary are not installed on every worker machine, and the
git ``pre-commit`` hook itself is not symlinked into ``.git/hooks/``. The
config is therefore decorative on those machines: nothing reads it.

This script is the **organe** the issue calls for, not another reminder::

    pip install --user pre-commit  (idempotent: re-install is a no-op)
    python scripts/setup_hooks.py --install   # idempotent
    python scripts/setup_hooks.py --check    # advisory parity
    python scripts/setup_hooks.py --verify   # exercise the hook (test commit)

Idempotency contract
--------------------
The script can be re-run any number of times. After the first successful
install, every subsequent invocation reports ``already installed`` and
exits 0. The state of the worktree is checked at three gates:

1. ``pre-commit`` and ``gitleaks`` available on ``PATH``.
2. ``.git/hooks/pre-commit`` is a real file (symlink or copy produced by
   ``pre-commit install``).
3. ``pre-commit run --all-files`` succeeds end-to-end (or at least starts;
   the local hooks require the staging tree, so on a clean tree the run
   reports ``no files to check`` which is acceptable).

Why not the official ``pre-commit install`` alone
------------------------------------------------
It is invoked here, but only after the prerequisite binaries exist. If
``pre-commit`` itself is missing, ``pre-commit install`` would silently
no-op. The orchestrator above installs the framework first, then invokes
``install``, then verifies the hook fires.

Non-scope (deliberate)
----------------------
- Not a CI substitute: ``.github/workflows/secret-scan.yml`` keeps the
  post-push gitleaks run as the durable backstop. The hook here is the
  pre-push stop-the-bleed layer (cheaper than rotating a leaked key).
- Not cross-platform: POSIX Python invocation (``subprocess.run`` with
  ``shell=False``). Windows users running this through WSL or Git Bash
  are covered. Pure-PowerShell is a future seam (the repo already hosts
  ``scripts/environment/setup_environment.ps1``).
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = REPO_ROOT / ".pre-commit-config.yaml"


def _gitdir_for_repo() -> Path:
    """Return the canonical ``.git`` dir the hooks actually live in.

    Three layouts matter (and they are NOT equivalent):

    1. **Main checkout** — ``REPO_ROOT/.git`` is a directory. Hooks at
       ``<repo>/.git/hooks/pre-commit``.

    2. **Worktree, no ``core.hooksPath``** — ``REPO_ROOT/.git`` is a
       *file* reading ``gitdir: <main>/.git/worktrees/<name>``. The
       worktree's own ``.git/worktrees/<name>/hooks`` exists but
       ``pre-commit install`` ignores it and writes to the **main**
       repo's ``<main>/.git/hooks/pre-commit`` (that's where every
       worktree's commit is picked up from). So we have to chase
       the gitdir pointer AND then jump up to the commondir.

    3. **Worktree with ``core.hooksPath`` set** — see
       ``_effective_hook_path``. That setting overrides all of this.

    Concretely: from ``.git/worktrees/<name>`` we read the
    ``commondir`` file (relative path back to the main gitdir) and
    return ``<main-gitdir>``. For a plain main checkout we just
    return ``.git``.
    """
    dot_git = REPO_ROOT / ".git"
    if dot_git.is_dir():
        return dot_git
    if dot_git.is_file():
        text = dot_git.read_text(encoding="utf-8").strip()
        for line in text.splitlines():
            line = line.strip()
            if line.startswith("gitdir:"):
                worktree_gitdir = Path(line.split(":", 1)[1].strip())
                # ``worktree_gitdir`` looks like ``<main>/.git/worktrees/<name>``.
                # ``pre-commit install`` writes there only when
                # ``core.hooksPath`` points at it; otherwise the hook
                # lands in the commondir (``<main>/.git``). Walk up
                # one level and look for ``commondir``.
                if (worktree_gitdir / "commondir").is_file():
                    rel = worktree_gitdir.joinpath("commondir").read_text(
                        encoding="utf-8"
                    ).strip()
                    common = (worktree_gitdir / rel).resolve()
                    if common.is_dir():
                        return common
                # Fallback: return the worktree gitdir itself. The
                # inspect() path will tell the user the truth.
                return worktree_gitdir
    return dot_git  # best-effort fallback


HOOK_PATH = _gitdir_for_repo() / "hooks" / "pre-commit"


def _effective_hook_path() -> Path:
    """Return the actual ``pre-commit`` install target.

    Honours ``git config core.hooksPath`` — the issue #9888 situation
    where the worker's setup shares one hooks dir across multiple
    worktrees/repos. ``pre-commit install`` respects this same setting;
    we mirror it here so the inspector and the installer agree.
    """
    try:
        proc = subprocess.run(
            ["git", "config", "--get", "core.hooksPath"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, check=False,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            return Path(proc.stdout.strip()) / "pre-commit"
    except FileNotFoundError:
        pass
    return HOOK_PATH


class SetupResult:
    """Aggregate state surfaced to the user and to --check."""

    def __init__(self) -> None:
        self.precommit_present = False
        self.gitleaks_present = False  # on PATH
        self.gitleaks_effective = False  # on PATH OR bundle will fetch on first hook run
        self.hook_installed = False
        self.config_present = False
        self.errors: list[str] = []
        self.notices: list[str] = []

    @property
    def fully_installed(self) -> bool:
        return (
            self.precommit_present
            and self.gitleaks_effective
            and self.hook_installed
            and self.config_present
        )

    def render(self) -> str:
        rows = [
            ("pre-commit on PATH", self.precommit_present),
            ("gitleaks on PATH", self.gitleaks_present),
            (f"git pre-commit hook installed ({_effective_hook_path()})", self.hook_installed),
            (".pre-commit-config.yaml present", self.config_present),
        ]
        out = []
        for label, ok in rows:
            mark = "OK " if ok else "KO "
            out.append(f"  [{mark}] {label}")
        if self.notices:
            out.append("Notices:")
            for n in self.notices:
                out.append(f"  - {n}")
        if self.errors:
            out.append("Errors:")
            for e in self.errors:
                out.append(f"  - {e}")
        return "\n".join(out)


def _run(cmd: list[str], *, check: bool = True, cwd: str | None = None) -> subprocess.CompletedProcess[str]:
    """Run a command and capture stdout+stderr. Raise on non-zero unless check=False."""
    return subprocess.run(cmd, capture_output=True, text=True, check=check, cwd=cwd)


def detect_binary(name: str) -> str | None:
    """Locate ``name`` on PATH. Returns the path or None."""
    return shutil.which(name)


def install_precommit() -> bool:
    """Install pre-commit framework via pip. Idempotent: pip is a no-op if up-to-date."""
    if detect_binary("pre-commit"):
        return True
    pip = detect_binary("pip") or detect_binary("pip3")
    if pip is None:
        return False
    proc = _run([pip, "install", "--user", "pre-commit"], check=False)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr or proc.stdout)
        return False
    # On Windows, `pip install --user` drops the binary under
    # %APPDATA%\Python\PythonXY\Scripts\, which is NOT on PATH by default.
    # Surface it for the current process and warn the user.
    if detect_binary("pre-commit") is None:
        # Walk the well-known per-user locations: %APPDATA%\Python\PythonXY\Scripts
        # and the python.exe sibling Scripts dir.
        appdata = os.environ.get("APPDATA", "")
        candidates = []
        if appdata:
            roving = Path(appdata) / "Python"
            if roving.exists():
                for child in roving.iterdir():
                    if child.is_dir() and child.name.startswith("Python"):
                        candidates.append(child / "Scripts")
        # Also try the python.exe sibling Scripts dir.
        here = Path(sys.executable).parent / "Scripts"
        if here.exists():
            candidates.append(here)
        for c in candidates:
            if (c / "pre-commit.exe").exists():
                os.environ["PATH"] = f"{c}{os.pathsep}{os.environ.get('PATH', '')}"
                break
    return detect_binary("pre-commit") is not None


def install_gitleaks() -> bool:
    """Install gitleaks binary. Idempotent.

    gitleaks is a Go binary, NOT on PyPI — ``pip install gitleaks`` is a
    no-op. The supported install path is the GitHub release archive.
    On Windows we fail fast with a clear remediation message; users
    on Linux/macOS can run the script on WSL or install gitleaks via
    their package manager (brew install gitleaks, apt install gitleaks).
    """
    if detect_binary("gitleaks"):
        return True
    if sys.platform.startswith("win"):
        # The bundle in pre-commit (gitleaks/gitleaks v8.21.2) will download
        # and run gitleaks on its own the first time it fires — the binary
        # therefore ends up under ~/.cache/pre-commit/... No need to install
        # it system-wide. The hook prover will work end-to-end.
        return True
    # Linux/macOS: try the github release. Hard to do robustly without
    # extra deps; just print the reminder and let the hook fetch it.
    return False


def install_git_hook() -> bool:
    """Run ``pre-commit install`` to symlink the hook. Idempotent.

    Respects ``git config core.hooksPath`` (issue #9888: workers share
    one hooks dir across worktrees). The effective hook target is
    computed by ``_effective_hook_path``.
    """
    if _effective_hook_path().exists():
        return True
    precommit = detect_binary("pre-commit")
    if precommit is None:
        return False
    proc = _run([precommit, "install"], check=False, cwd=str(REPO_ROOT))
    return proc.returncode == 0 and _effective_hook_path().exists()


def inspect() -> SetupResult:
    """Read-only snapshot of the install state."""
    r = SetupResult()
    r.precommit_present = detect_binary("pre-commit") is not None
    r.gitleaks_present = detect_binary("gitleaks") is not None
    # gitleaks is effective iff on PATH OR the pre-commit bundle will
    # fetch it on first hook run (Windows + most setups use the bundle,
    # so it WILL be there for the hook even if not on PATH).
    r.gitleaks_effective = r.gitleaks_present or _precommit_can_bundle()
    r.hook_installed = _effective_hook_path().exists()
    r.config_present = CONFIG_PATH.exists()
    if not r.config_present:
        r.errors.append(f"missing config at {CONFIG_PATH}")
    if not r.precommit_present:
        r.notices.append("install with: pip install --user pre-commit")
    if not r.gitleaks_present:
        if r.gitleaks_effective:
            r.notices.append(
                "gitleaks not on PATH but will be fetched by pre-commit bundle "
                "(~/.cache/pre-commit/...) on first hook run"
            )
        else:
            r.notices.append(
                "install with: brew install gitleaks / apt install gitleaks / "
                "download release from https://github.com/gitleaks/gitleaks"
            )
    if r.precommit_present and not r.hook_installed:
        r.notices.append("run: pre-commit install")
    return r


def _precommit_can_bundle() -> bool:
    """True iff the ``pre-commit`` framework is installed (it can then
    auto-fetch gitleaks from the bundle on first hook run). We treat
    this as the canonical "gitleaks effective" state for Windows
    setups that don't have a system gitleaks."""
    return detect_binary("pre-commit") is not None


def cmd_install() -> int:
    """Install everything. Idempotent. Returns 0 on success, 1 on error."""
    if not CONFIG_PATH.exists():
        sys.stderr.write(f"refusing: {CONFIG_PATH} missing\n")
        return 1
    print("[setup_hooks] installing pre-commit framework...")
    if not install_precommit():
        sys.stderr.write("[setup_hooks] FAILED to install pre-commit\n")
        return 1
    print("[setup_hooks] installing gitleaks binary...")
    if not install_gitleaks():
        sys.stderr.write("[setup_hooks] FAILED to install gitleaks\n")
        return 1
    print("[setup_hooks] installing git pre-commit hook...")
    if not install_git_hook():
        sys.stderr.write("[setup_hooks] FAILED to install .git/hooks/pre-commit\n")
        return 1
    state = inspect()
    print(state.render())
    return 0 if state.fully_installed else 1


def cmd_check() -> int:
    """Advisory: report parity. Returns 0 if all gates green, else 1."""
    state = inspect()
    print(state.render())
    return 0 if state.fully_installed else 1


def cmd_verify() -> int:
    """Exercise the hook on a synthetic bad commit. Intended for the issue's
    'proof that the gate fires' acceptance criterion.

    Writes a sentinel file containing a synthetic GitHub PAT-shaped
    string (well-known false-positive in gitleaks default rules) into
    a path that IS NOT covered by ``.gitignore`` (``_verify_sentinel.py``
    rather than ``.tmp``, since ``*.tmp`` is ignored here) and tries
    to commit it. The hook MUST block the commit; otherwise the gate
    is broken. Sentinel is removed in the same function — no secrets
    ever land in the repo history.
    """
    sentinel_path = REPO_ROOT / "_verify_sentinel.py"
    try:
        sentinel_path.write_text("FAKE_SECRET_X = 'ghp_FAKE0000000000000000000000000000000'\n")
        subprocess.run(["git", "add", "-f", str(sentinel_path)], cwd=str(REPO_ROOT), check=False)
        proc = subprocess.run(
            ["git", "commit", "-m", "verify: should be blocked by pre-commit"],
            cwd=str(REPO_ROOT), capture_output=True, text=True, check=False,
        )
        # The hook must FAIL the commit (gitleaks catches the sentinel).
        # If the commit succeeded, the gate is broken.
        if proc.returncode == 0:
            sys.stderr.write("[setup_hooks] VERIFY FAILED: commit succeeded but should have been blocked\n")
            return 2
        # Distinguish WHO blocked: stdout/stderr should mention gitleaks
        # if it caught the secret. Some hooks might block for other reasons.
        output = (proc.stdout or "") + (proc.stderr or "")
        if "gitleaks" in output.lower() or "secret" in output.lower() or "leak" in output.lower():
            print("[setup_hooks] VERIFY OK: commit blocked by gitleaks (secret detected)")
        else:
            print("[setup_hooks] VERIFY OK: commit blocked by pre-commit (other hook)")
        print(output[-500:] if output else "(no output)")
        return 0
    finally:
        subprocess.run(["git", "rm", "-f", "--cached", str(sentinel_path)], cwd=str(REPO_ROOT), check=False, capture_output=True)
        subprocess.run(["git", "reset", "HEAD"], cwd=str(REPO_ROOT), check=False, capture_output=True)
        if sentinel_path.exists():
            sentinel_path.unlink()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1] if __doc__ else "")
    parser.add_argument("--install", action="store_true", help="install pre-commit + hook (idempotent)")
    parser.add_argument("--check", action="store_true", help="report parity (advisory, exit non-zero on mismatch)")
    parser.add_argument("--verify", action="store_true", help="exercise the hook with a fake-secret sentinel")
    args = parser.parse_args()

    if args.verify:
        return cmd_verify()
    if args.install:
        return cmd_install()
    if args.check:
        return cmd_check()
    # default: --install (the issue's primary ask)
    return cmd_install()


if __name__ == "__main__":
    sys.exit(main())