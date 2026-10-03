"""LeanDojo v2 installability + API surface check (cycle c.76, issue #18915).

This module encodes the **prerequisites** verified firsthand on this machine
(2026-10-03, myia-ai-01:CoursIA-2) so the integration work in follow-up
cycles starts from a known-good baseline.

Verdict per the sota-not-work-workaround rule (6 axes):
  RECOVERABLE-LOCAL — the full stack installs in <5 min on CPU, no GPU
  required, no user action needed beyond a single `elan toolchain install`.

The module also exposes the runtime tactic-loop hooks (`DojoTools` skeleton)
that follow-up cycles will fill in. Kept minimal: the goal of c.76 is to
verify the prerequisites, not to deliver the integration.
"""

from __future__ import annotations

import importlib
import shutil
import subprocess
import sys
from dataclasses import dataclass
from typing import Optional


# Pin matched to Lean-10 notebook (#18893) -- see issue #18915 for the
# compatibility rationale (lean-dojo 2.2.0 + Lean 4.11.0 is the only pair
# where the Dojo runtime works; lean-dojo 4.20+ drops Dojo for newer toolchains).
LEAN_DOJO_VERSION = "2.2.0"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.11.0"


@dataclass
class LeanDojoPrereq:
    """Result of one prereq check (issue #18915, c.76)."""

    name: str
    ok: bool
    detail: str

    def render(self) -> str:
        flag = "OK" if self.ok else "FAIL"
        return f"  [{flag}] {self.name}: {self.detail}"


def check_python_version() -> LeanDojoPrereq:
    """Python 3.10-3.12 is the supported range for lean-dojo 2.2.0.

    PyPI metadata (https://pypi.org/pypi/lean-dojo/2.2.0/json) declares
    Requires-Python: <=3.12,>=3.9. Versions 3.13+ are NOT supported by
    this pin -- installation requires ``--ignore-requires-python`` and the
    runtime may break in unsupported ways. The control rejects 3.13+ so
    the verdict stays honest about the supported range.
    """
    major, minor = sys.version_info[:2]
    ok = (3, 10) <= (major, minor) <= (3, 12)
    return LeanDojoPrereq(
        "python 3.10-3.12",
        ok,
        f"detected {major}.{minor} (supported: 3.10-3.12 per Requires-Python)",
    )


def check_lean_dojo_installed() -> LeanDojoPrereq:
    """`pip show lean-dojo` should report the pinned version 2.2.0."""
    proc = subprocess.run(
        [sys.executable, "-m", "pip", "show", "lean-dojo"],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=False,
    )
    if proc.returncode != 0:
        return LeanDojoPrereq(
            "lean-dojo installable",
            False,
            "pip show lean-dojo failed; install via `pip install --ignore-requires-python lean-dojo==2.2.0`",
        )
    version = None
    for line in proc.stdout.splitlines():
        if line.lower().startswith("version:"):
            version = line.split(":", 1)[1].strip()
    ok = version == LEAN_DOJO_VERSION
    return LeanDojoPrereq(
        "lean-dojo version",
        ok,
        f"want {LEAN_DOJO_VERSION}, have {version or 'unknown'}",
    )


def check_lean_dojo_importable() -> LeanDojoPrereq:
    """`import lean_dojo` + `from lean_dojo import Dojo, LeanGitRepo, trace`."""
    try:
        mod = importlib.import_module("lean_dojo")
    except Exception as exc:  # ImportError, OSError, etc.
        return LeanDojoPrereq("lean-dojo import", False, f"import failed: {exc!r}")
    api = []
    for symbol in ("Dojo", "LeanGitRepo", "trace"):
        api.append(f"{symbol}={'Y' if hasattr(mod, symbol) else 'N'}")
    return LeanDojoPrereq(
        "lean-dojo API surface",
        all(hasattr(mod, s) for s in ("Dojo", "LeanGitRepo", "trace")),
        ", ".join(api),
    )


def check_elan_available() -> LeanDojoPrereq:
    """`elan --version` reports a working elan installation."""
    elan = shutil.which("elan")
    if not elan:
        return LeanDojoPrereq("elan on PATH", False, "elan not found")
    proc = subprocess.run(
        [elan, "--version"], capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    return LeanDojoPrereq(
        "elan on PATH",
        proc.returncode == 0,
        f"{elan} -> exit {proc.returncode}",
    )


def check_lean_toolchain_pinned() -> LeanDojoPrereq:
    """`elan toolchain list` should include `leanprover/lean4:v4.11.0`."""
    elan = shutil.which("elan")
    if not elan:
        return LeanDojoPrereq("lean toolchain v4.11.0", False, "elan missing")
    proc = subprocess.run(
        [elan, "toolchain", "list"], capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    ok = LEAN_TOOLCHAIN in proc.stdout
    return LeanDojoPrereq(
        f"toolchain {LEAN_TOOLCHAIN}",
        ok,
        "installed" if ok else f"run `elan toolchain install {LEAN_TOOLCHAIN}`",
    )


def check_lean_default_toolchain() -> LeanDojoPrereq:
    """`lean --version` should report 4.11.0 (the only pair with lean-dojo 2.2.0)."""
    lean = shutil.which("lean")
    if not lean:
        return LeanDojoPrereq("lean binary", False, "lean not on PATH")
    proc = subprocess.run(
        [lean, "--version"], capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    if proc.returncode != 0:
        return LeanDojoPrereq("lean --version", False, f"exit {proc.returncode}")
    ok = "4.11.0" in (proc.stdout + proc.stderr)
    return LeanDojoPrereq(
        "lean 4.11.0 active",
        ok,
        f"{proc.stdout.strip() or proc.stderr.strip()}",
    )


def run_all_checks() -> list[LeanDojoPrereq]:
    """Run every prereq check; return the list (caller renders or asserts)."""
    return [
        check_python_version(),
        check_lean_dojo_installed(),
        check_lean_dojo_importable(),
        check_elan_available(),
        check_lean_toolchain_pinned(),
        check_lean_default_toolchain(),
    ]


def main() -> int:
    """Entry point: print a verdict table and exit 0 iff every prereq is green.

    The exit code is what the eventual CI gate would consume; the function is
    deliberately synchronous and side-effect-free apart from the checks
    themselves.
    """
    results = run_all_checks()
    print("LeanDojo v2 prerequisites (issue #18915, c.76 verdict):")
    for r in results:
        print(r.render())
    all_ok = all(r.ok for r in results)
    print()
    print("Verdict:", "RECOVERABLE-LOCAL" if all_ok else "BLOCKED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
