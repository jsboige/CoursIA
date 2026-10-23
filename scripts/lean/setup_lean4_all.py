#!/usr/bin/env python3
"""Single entry point for Lean 4 kernel setup (WSL + Windows registration + validation).

Orchestrates the 3 setup steps:
1. WSL installation (elan, lean, venv, wrapper) via GameTheory/scripts/setup_wsl_lean4.sh
1bis. WSL Python venv (~/.python3-wsl-venv + dependances) via
     SymbolicAI/Lean/scripts/setup_wsl_python.sh -- the venv the validator
     actually checks (#21614, defect 3)
2. Windows kernel registration via GameTheory/scripts/setup_lean4_kernel.ps1
3. Validation via SymbolicAI/Lean/scripts/validate_lean_setup.py

Usage:
    python scripts/lean/setup_lean4_all.py              # Full setup (1+2+3)
    python scripts/lean/setup_lean4_all.py --wsl-only    # Step 1 only
    python scripts/lean/setup_lean4_all.py --register    # Step 2 only
    python scripts/lean/setup_lean4_all.py --validate    # Step 3 only
    python scripts/lean/setup_lean4_all.py --check-wrapper  # Check kernel.json wrapper
"""

import argparse
import shutil
import subprocess
import sys
from pathlib import Path

# Canonical wrapper-regression check (issue #1618) lives in this same dir.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_kernel_check import inspect_kernel_wrapper  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GT_SCRIPTS = REPO_ROOT / "MyIA.AI.Notebooks" / "GameTheory" / "scripts"
LEAN_SCRIPTS = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "scripts"

WSL_DISTRO = "Ubuntu"

# Regex + helper mirror scripts/notebook_tools/wsl_papermill.py:win_to_wsl_path
# (kept local to avoid a cross-directory import; identical logic, #2871 part 2).
import re as _re
_WIN_DRIVE_RE = _re.compile(r"^([A-Za-z]:)[\\/](.*)$")


def _win_to_wsl_path(win_path: str) -> str:
    """Convert a Windows path (``C:\\dev\\repo``) to its WSL mount form
    (``/mnt/c/dev/repo``). WSL ``bash`` strips backslashes from args, so passing
    a raw Windows path to ``wsl -- bash <winpath>`` yields ``C:devrepo`` ->
    file-not-found (incident po-2024 c.355 lean4-wsl setup, exit 127). A path
    without a drive prefix is returned unchanged.
    """
    m = _WIN_DRIVE_RE.match(win_path)
    if not m:
        return win_path
    drive = m.group(1)[0].lower()
    rest = m.group(2).replace("\\", "/")
    return f"/mnt/{drive}/{rest}"


#: Distributions WSL qui ne sont PAS des environnements utilisateur (#21611).
#: ``docker-desktop`` est un conteneur Linux interne a Docker Desktop : ni
#: bash, ni elan, ni Python, ni depot Windows monte comme la chaine l'attend.
#: Prendre la premiere ligne de ``wsl -l -q`` (mesure 2026-10-20, poste
#: myia-po-2028) fait echouer l'installation Lean avec un ``127`` opaque
#: (``/bin/sh: bash: not found``) -- un echec qui ne nomme pas sa cause.
_NON_USER_DISTROS = frozenset({"docker-desktop", "docker-desktop-data"})


def _is_user_distro(name: str) -> bool:
    """True when the WSL distribution can host the Lean toolchain."""
    lowered = name.strip().lower()
    if not lowered or "\x00" in lowered:
        return False
    if lowered in _NON_USER_DISTROS:
        return False
    # Docker Desktop expose aussi des distributions au nom compose ; on les
    # ecarte par famille plutot que par une liste qui derive a chaque version.
    return "docker" not in lowered


def _distro_has_bash(name: str, timeout: int = 30) -> bool:
    """Probe a distribution: a user environment answers ``bash -lc true``.

    The probe boots the distribution, which the setup does anyway on the next
    step; what it avoids is installing the toolchain into a distribution that
    cannot run it.
    """
    try:
        probe = subprocess.run(
            ["wsl", "-d", name, "--", "bash", "-lc", "true"],
            capture_output=True, timeout=timeout,
        )
        return probe.returncode == 0
    except Exception:
        return False


def _detect_wsl_distro():
    """Detect the WSL distro to install into, fallback to 'Ubuntu'.

    `wsl -l -q` emits UTF-16LE on Windows (null byte between every ASCII char),
    so reading it with ``text=True`` yields e.g. ``'U\\x00b\\x00u\\x00n\\x00t\\x00u'``
    -- a string with embedded nulls. Passing that to ``subprocess.run(["wsl",
    "-d", distro, ...])`` crashes ``CreateProcess`` with ``ValueError: embedded
    null character`` (incident po-2024 c.355 lean4-wsl setup). Decode bytes
    robustly instead: try UTF-16LE first (WSL's actual output), strip the nulls
    as a belt-and-suspenders fallback, then split on newlines.

    Two guards on top of that (#21611): the distributions that are not user
    environments (``docker-desktop``) are dropped, and each remaining
    candidate is **probed** before being retained -- taking the first line of
    the list was enough to pick a container with no bash.
    """
    try:
        result = subprocess.run(
            ["wsl", "-l", "-q"], capture_output=True, timeout=10,
        )
        if result.returncode != 0:
            return "Ubuntu"
        # WSL -l -q is UTF-16LE with BOM on recent Windows; decode defensively.
        raw = result.stdout
        text = None
        if raw[:2] in (b"\xff\xfe", b"\xfe\xff"):
            text = raw.decode("utf-16", errors="ignore")
        elif b"\x00" in raw:
            # UTF-16LE without BOM: every other byte is 0x00 for ASCII distro names.
            text = raw.decode("utf-16-le", errors="ignore")
        else:
            text = raw.decode("utf-8", errors="ignore")
        lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
        candidates = [ln for ln in lines if _is_user_distro(ln)]
        skipped = [ln for ln in lines if not _is_user_distro(ln)]
        if skipped:
            print(f"Distributions WSL ecartees (pas un environnement utilisateur) : "
                  f"{', '.join(skipped)}")
        if not candidates:
            return "Ubuntu"
        for name in candidates:
            if _distro_has_bash(name):
                return name
        # Aucune candidate n'a repondu a la sonde : on retient la premiere
        # distribution utilisable plutot que de revenir a "Ubuntu", qui peut
        # ne pas exister sur le poste.
        print(f"Aucune distribution WSL n'a repondu a la sonde bash ; "
              f"retenue par defaut : {candidates[0]}")
        return candidates[0]
    except Exception:
        pass
    return "Ubuntu"


def step_wsl_install():
    """Step 1: Install Lean 4 stack in WSL."""
    print("=" * 60)
    print("STEP 1: WSL Installation (elan + lean + venv + wrapper)")
    print("=" * 60)
    script = GT_SCRIPTS / "setup_wsl_lean4.sh"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    wsl_script = _win_to_wsl_path(str(script))
    print(f"Running: wsl -d {WSL_DISTRO} -- bash {wsl_script}")
    result = subprocess.run(
        ["wsl", "-d", WSL_DISTRO, "--", "bash", wsl_script],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print(f"FAILED: WSL setup exited with code {result.returncode}")
        return False
    print("OK: WSL installation complete")
    return True


def step_wsl_python_venv():
    """Step 1 bis: create the WSL Python venv the validator actually checks.

    The validator checks the packages of ``~/.python3-wsl-venv``
    (``python-dotenv``, ``openai``, ``anthropic``, ``ipykernel``) and the
    ``python3-wsl`` kernel points at that same venv.  ``setup_wsl_lean4.sh``
    creates ANOTHER venv (``~/.lean4-venv``), so the chain never created
    the one that is validated: the installation was incomplete and the
    validator reported a component that the setup had never installed
    (issue #21614, defect 3).
    """
    print("=" * 60)
    print("STEP 1bis: WSL Python venv (~/.python3-wsl-venv) + dependances")
    print("=" * 60)
    script = LEAN_SCRIPTS / "setup_wsl_python.sh"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    wsl_script = _win_to_wsl_path(str(script))
    print(f"Running: wsl -d {WSL_DISTRO} -- bash {wsl_script}")
    result = subprocess.run(
        ["wsl", "-d", WSL_DISTRO, "--", "bash", wsl_script],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print(f"FAILED: WSL Python venv setup exited with code {result.returncode}")
        return False
    print("OK: WSL Python venv ready")
    return True


def step_register_kernel():
    """Step 2: Register lean4-wsl kernel on Windows."""
    print("=" * 60)
    print("STEP 2: Windows Kernel Registration")
    print("=" * 60)
    if not shutil.which("powershell") and not shutil.which("powershell.exe"):
        print("ERROR: PowerShell not found in PATH. This script must run on Windows.")
        return False
    script = GT_SCRIPTS / "setup_lean4_kernel.ps1"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    print(f"Running: powershell -File {script}")
    result = subprocess.run(
        ["powershell", "-ExecutionPolicy", "Bypass", "-File", str(script)],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print(f"FAILED: Kernel registration exited with code {result.returncode}")
        return False
    print("OK: Kernel registration complete")
    return True


def step_validate():
    """Step 3: Validate the full Lean 4 setup."""
    print("=" * 60)
    print("STEP 3: Validation")
    print("=" * 60)
    script = LEAN_SCRIPTS / "validate_lean_setup.py"
    if not script.exists():
        print(f"ERROR: {script} not found")
        return False
    print(f"Running: python {script}")
    result = subprocess.run(
        [sys.executable, str(script)],
        cwd=str(REPO_ROOT),
    )
    if result.returncode != 0:
        print("FAILED: Validation failed")
        return False
    print("OK: Validation passed")
    return True


def check_wrapper_registration():
    """Check that kernel.json points to the CORRECT Python wrapper (not old bash).

    Classification is delegated to the canonical helper
    ``scripts/lean/lean_kernel_check.inspect_kernel_wrapper`` (issue #1618), which
    probes both the WSL-side (~/.local/share/jupyter) and Windows-side (%APPDATA%)
    kernel.json locations.
    """
    print("=" * 60)
    print("CHECK: kernel.json wrapper registration")
    print("=" * 60)

    status, message = inspect_kernel_wrapper("lean4-wsl")
    prefix = {"ok": "OK:", "error": "ERROR:", "warning": "WARNING:"}[status]
    print(f"{prefix} {message}")
    return status == "ok"


def main():
    parser = argparse.ArgumentParser(
        description="Lean 4 kernel setup orchestrator (single entry point)"
    )
    parser.add_argument("--distro", type=str, default=None,
                        help="WSL distro name (default: auto-detect, fallback Ubuntu)")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--wsl-only", action="store_true", help="WSL install only (step 1)")
    group.add_argument("--register", action="store_true", help="Kernel registration only (step 2)")
    group.add_argument("--validate", action="store_true", help="Validation only (step 3)")
    group.add_argument("--check-wrapper", action="store_true", help="Check kernel.json wrapper")
    args = parser.parse_args()

    global WSL_DISTRO
    WSL_DISTRO = args.distro or _detect_wsl_distro()

    results = []

    if args.check_wrapper:
        ok = check_wrapper_registration()
        sys.exit(0 if ok else 1)

    if args.wsl_only:
        ok = step_wsl_install()
        ok = step_wsl_python_venv() and ok
        sys.exit(0 if ok else 1)

    if args.register:
        ok = step_register_kernel()
        sys.exit(0 if ok else 1)

    if args.validate:
        ok = step_validate()
        sys.exit(0 if ok else 1)

    # Full setup: all 3 steps
    print("Lean 4 Kernel Setup — Full Installation")
    print()

    results.append(("WSL Install", step_wsl_install()))
    if not results[-1][1]:
        print("\nStep 1 FAILED. Fix WSL issues before continuing.")
        sys.exit(1)

    results.append(("WSL Python venv", step_wsl_python_venv()))
    if not results[-1][1]:
        print("\nStep 1bis FAILED. Fix the WSL Python venv before continuing.")
        sys.exit(1)

    results.append(("Kernel Registration", step_register_kernel()))
    results.append(("Validation", step_validate()))
    results.append(("Wrapper Check", check_wrapper_registration()))

    print()
    print("=" * 60)
    print("RESULTS")
    print("=" * 60)
    for name, ok in results:
        status = "OK" if ok else "FAILED"
        print(f"  {name:30s} {status}")
    all_ok = all(ok for _, ok in results)
    print()
    if all_ok:
        print("All steps passed. Lean 4 kernel ready.")
    else:
        print("Some steps failed. See output above.")
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
