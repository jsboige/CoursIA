#!/usr/bin/env python3
"""Setup environment for the SmartContracts notebook series.

This script:
1. Installs Python dependencies from requirements.txt
2. Installs the Solidity compiler via py-solc-x
3. Checks for Foundry tools (forge, cast, anvil)
4. Reports what's available and what's missing

Usage:
    python setup_env.py                  # Full setup (install all from requirements.txt)
    python setup_env.py --check          # Check only (don't install)
    python setup_env.py --phase 1        # Install only Phase 1 deps
    python setup_env.py --with-optional  # Also install optional deps (LLM APIs)
    python setup_env.py --venv           # Create a virtual env first
    python setup_env.py --skip-foundry   # Skip Foundry check

Phases (for --phase):
    0: Utilities (matplotlib, tabulate)
    1: Blockchain Core (web3, py-solc-x, python-dotenv)
    2: Cryptography & ZKP (pycryptodome, py_ecc)
    3: Homomorphic Encryption (phe, tenseal)
    4: MPC (mpyc)
    5: Alternative Chains (xrpl-py, python-bitcoinlib, vyper)

Known limitations:
    - concrete-python: Linux only (no Windows wheels)
    - electionguard: requires pydantic<2, conflicts with web3>=7
      -> Install in a separate venv if needed
"""

import argparse
import importlib
import os
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
REQUIREMENTS_FILE = SCRIPT_DIR / "requirements.txt"
REQUIREMENTS_OPTIONAL_FILE = SCRIPT_DIR / "requirements-optional.txt"

# Phase -> list of (pip_spec, import_name) tuples
# import_name is used to check if already installed
PHASES = {
    0: [  # Utilities
        ("matplotlib>=3.5", "matplotlib"),
        ("tabulate>=0.9", "tabulate"),
    ],
    1: [  # Blockchain Core
        ("web3>=7.0", "web3"),
        ("py-solc-x>=1.1", "solcx"),
        ("python-dotenv>=1.0", "dotenv"),
    ],
    2: [  # Cryptography & ZKP
        ("pycryptodome>=3.20", "Crypto"),
        ("py_ecc>=7.0", "py_ecc"),
    ],
    3: [  # Homomorphic Encryption
        ("phe>=1.5", "phe"),
        ("tenseal>=0.3", "tenseal"),
    ],
    4: [  # MPC
        ("mpyc>=0.10", "mpyc"),
    ],
    5: [  # Alternative Chains
        ("xrpl-py>=3.0", "xrpl"),
        ("python-bitcoinlib>=0.12", "bitcoin"),
        ("vyper>=0.4", "vyper"),
    ],
}

PHASE_NAMES = {
    0: "Utilities",
    1: "Blockchain Core",
    2: "Cryptography & ZKP",
    3: "Homomorphic Encryption",
    4: "MPC",
    5: "Alternative Chains",
}

# Packages that are known to be problematic
SKIP_PACKAGES = set()
if sys.platform == "win32":
    SKIP_PACKAGES.add("concrete-python")  # Linux only

SOLC_VERSION = "0.8.28"


# =============================================================================
# CHECKS
# =============================================================================

def check_python_package(import_name: str) -> tuple:
    """Check if a Python package is importable. Returns (installed, version)."""
    try:
        mod = importlib.import_module(import_name)
        version = getattr(mod, "__version__", "?")
        return True, version
    except ImportError:
        return False, None


def check_tool(name: str) -> tuple:
    """Check if a CLI tool is available. Returns (available, version_str)."""
    try:
        result = subprocess.run(
            [name, "--version"],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return True, result.stdout.strip().split('\n')[0]
        return False, None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False, None


def check_anvil_running() -> bool:
    """Check if anvil is running on localhost:8545."""
    try:
        import urllib.request
        import json as json_mod
        req = urllib.request.Request(
            "http://127.0.0.1:8545",
            method='POST',
            data=b'{"jsonrpc":"2.0","method":"eth_chainId","params":[],"id":1}',
            headers={"Content-Type": "application/json"}
        )
        with urllib.request.urlopen(req, timeout=2) as resp:
            data = json_mod.loads(resp.read())
            return "result" in data
    except Exception:
        return False


# =============================================================================
# INSTALL
# =============================================================================

def pip_install(packages: list, label: str = ""):
    """Install packages via pip. Returns True if successful."""
    if not packages:
        return True
    if label:
        print(f"\n  Installing {label}...")
    cmd = [sys.executable, "-m", "pip", "install", "--quiet"] + packages
    print(f"  > {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if result.returncode != 0:
        # Show only error lines, not warnings
        errors = [l for l in result.stderr.split('\n')
                  if 'ERROR' in l.upper() and 'incompatible' not in l.lower()]
        if errors:
            print(f"  ERRORS:")
            for line in errors[:5]:
                print(f"    {line.strip()}")
        # Show incompatibilities separately
        incompat = [l for l in result.stderr.split('\n') if 'incompatible' in l.lower()]
        if incompat:
            print(f"  Compatibility warnings ({len(incompat)}):")
            for line in incompat[:3]:
                print(f"    {line.strip()}")
        return False
    return True


def install_from_requirements():
    """Install all packages from requirements.txt."""
    if not REQUIREMENTS_FILE.exists():
        print(f"  ERROR: {REQUIREMENTS_FILE} not found")
        return False
    return pip_install(["-r", str(REQUIREMENTS_FILE)], "requirements.txt")


def install_phase(phase: int):
    """Install packages for a specific phase."""
    if phase not in PHASES:
        print(f"  ERROR: Unknown phase {phase}")
        return False

    packages = PHASES[phase]
    missing = []
    for pip_spec, import_name in packages:
        pkg_name = pip_spec.split(">=")[0]
        if pkg_name in SKIP_PACKAGES:
            print(f"    [SKIP]    {pip_spec:30s} (not available on {sys.platform})")
            continue
        ok, _ = check_python_package(import_name)
        if not ok:
            missing.append(pip_spec)

    if missing:
        return pip_install(missing, f"Phase {phase}: {PHASE_NAMES[phase]}")
    return True


def install_solc():
    """Install Solidity compiler via py-solc-x."""
    try:
        import solcx
        installed = [str(v) for v in solcx.get_installed_solc_versions()]
        if SOLC_VERSION in installed:
            print(f"  [OK]      solc {SOLC_VERSION} already installed")
            return True
        print(f"  Installing solc {SOLC_VERSION}...")
        solcx.install_solc(SOLC_VERSION)
        print(f"  [OK]      solc {SOLC_VERSION} installed")
        return True
    except ImportError:
        print("  [SKIP]    py-solc-x not installed yet")
        return False
    except Exception as e:
        print(f"  [FAIL]    solc install failed: {e}")
        return False


def create_venv(venv_path: Path):
    """Create a virtual environment."""
    if venv_path.exists():
        print(f"  Virtual env already exists: {venv_path}")
        return True
    print(f"  Creating virtual env: {venv_path}")
    result = subprocess.run([sys.executable, "-m", "venv", str(venv_path)],
                            capture_output=True, text=True)
    if result.returncode != 0:
        print(f"  ERROR: {result.stderr}")
        return False
    print(f"  Created. Activate with:")
    if sys.platform == "win32":
        print(f"    {venv_path}\\Scripts\\activate")
    else:
        print(f"    source {venv_path}/bin/activate")
    print(f"  Then re-run: python setup_env.py")
    return True


# =============================================================================
# REPORTING
# =============================================================================

def check_all_phases():
    """Check all phases and report status. Returns dict of results."""
    results = {}
    for phase in sorted(PHASES.keys()):
        print(f"\n  Phase {phase}: {PHASE_NAMES[phase]}")
        phase_ok = True
        for pip_spec, import_name in PHASES[phase]:
            pkg_name = pip_spec.split(">=")[0]
            if pkg_name in SKIP_PACKAGES:
                print(f"    [N/A]     {pip_spec:30s} (not on {sys.platform})")
                continue
            ok, version = check_python_package(import_name)
            if ok:
                print(f"    [OK]      {pip_spec:30s} (v{version})")
            else:
                print(f"    [MISSING] {pip_spec:30s}")
                phase_ok = False
            results[pkg_name] = ok
        results[f"phase_{phase}"] = phase_ok
    return results


def print_executability(results: dict):
    """Print which notebooks can run given current deps."""
    foundry_ok = check_tool("forge")[0]
    anvil_ok = check_anvil_running()
    web3_ok = results.get("web3", False)
    crypto_ok = results.get("pycryptodome", False) and results.get("py_ecc", False)
    phe_ok = results.get("phe", False)
    vyper_ok = results.get("vyper", False)
    xrpl_ok = results.get("xrpl-py", False)
    bitcoin_ok = results.get("python-bitcoinlib", False)

    groups = [
        ("SC-0  (Cypherpunk Origins)", results.get("pycryptodome", False)),
        ("SC-1  (Setup Foundry)", foundry_ok),
        ("SC-2 to SC-10 (Solidity)", anvil_ok and web3_ok),
        ("SC-11 (LLM Assisted)", True),  # Has mock fallback
        ("SC-12 to SC-14 (Foundry Testing)", foundry_ok),
        ("SC-15 (Zero-Knowledge Proofs)", crypto_ok),
        ("SC-16 to SC-17 (HE & Voting)", phe_ok),
        ("SC-18 (Vyper)", anvil_ok and vyper_ok),
        ("SC-19 (Ripple XRP)", xrpl_ok),
        ("SC-20 (Bitcoin Scripting)", bitcoin_ok),
        ("SC-21 to SC-23 (Theory)", True),
        ("SC-24 to SC-25 (Deploy)", False),  # Needs API keys + testnet ETH
        ("SC-26 (Final Project)", anvil_ok and phe_ok),
    ]

    ready = sum(1 for _, ok in groups if ok)
    total = len(groups)
    print(f"\n  Notebook executability: {ready}/{total} groups ready")
    for name, ok in groups:
        status = "READY" if ok else "BLOCKED"
        print(f"    [{status:7s}] {name}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Setup SmartContracts notebook environment",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python setup_env.py                # Install everything
  python setup_env.py --check        # Check what's installed
  python setup_env.py --phase 1      # Install blockchain core only
  python setup_env.py --venv         # Create virtualenv first
        """
    )
    parser.add_argument("--check", action="store_true",
                        help="Check only, don't install")
    parser.add_argument("--phase", type=int, choices=list(PHASES.keys()),
                        help="Install only specific phase")
    parser.add_argument("--with-optional", action="store_true",
                        help="Also install optional deps (LLM APIs)")
    parser.add_argument("--venv", action="store_true",
                        help="Create virtual environment first")
    parser.add_argument("--skip-foundry", action="store_true",
                        help="Skip Foundry tools check")
    args = parser.parse_args()

    print("=" * 60)
    print("SmartContracts Series - Environment Setup")
    print(f"Python {sys.version.split()[0]} on {sys.platform}")
    print("=" * 60)

    # Virtual environment
    if args.venv:
        venv_path = SCRIPT_DIR / "venv"
        create_venv(venv_path)
        if not str(sys.prefix).endswith("venv"):
            print("\n  Please activate the venv and re-run this script.")
            return

    # ---- CHECK MODE ----
    if args.check:
        print("\nPython Packages:")
        print("-" * 60)
        results = check_all_phases()

        print("\n\nSolidity Compiler:")
        print("-" * 60)
        try:
            import solcx
            installed = [str(v) for v in solcx.get_installed_solc_versions()]
            if SOLC_VERSION in installed:
                print(f"  [OK]      solc {SOLC_VERSION}")
            else:
                print(f"  [MISSING] solc {SOLC_VERSION} (installed: {installed or 'none'})")
        except ImportError:
            print(f"  [MISSING] py-solc-x not installed")

        if not args.skip_foundry:
            print("\n\nFoundry Tools:")
            print("-" * 60)
            for tool in ["forge", "cast", "anvil"]:
                ok, version = check_tool(tool)
                status = f"[OK]      {tool:10s} ({version})" if ok else f"[MISSING] {tool}"
                print(f"  {status}")

        print("\n\nAnvil Service:")
        print("-" * 60)
        if check_anvil_running():
            print("  [OK]      anvil running on localhost:8545")
        else:
            print("  [OFFLINE] Start with: anvil (in a separate terminal)")

        print("\n\n" + "=" * 60)
        print("Summary")
        print("=" * 60)
        print_executability(results)

        missing = [k for k, v in results.items() if not k.startswith("phase_") and not v]
        if missing:
            print(f"\n  {len(missing)} missing packages. Install with:")
            print(f"    python setup_env.py")
        else:
            print(f"\n  All Python packages installed!")
        print()
        return

    # ---- INSTALL MODE ----
    print("\nInstalling Python packages...")
    print("-" * 60)

    if args.phase is not None:
        # Single phase install
        install_phase(args.phase)
    else:
        # Full install from requirements.txt
        install_from_requirements()

    # Optional deps
    if args.with_optional and REQUIREMENTS_OPTIONAL_FILE.exists():
        pip_install(["-r", str(REQUIREMENTS_OPTIONAL_FILE)], "optional dependencies")

    # Solidity compiler
    print("\n\nSolidity Compiler:")
    print("-" * 60)
    install_solc()

    # Foundry check
    if not args.skip_foundry:
        print("\n\nFoundry Tools:")
        print("-" * 60)
        all_foundry = True
        for tool in ["forge", "cast", "anvil"]:
            ok, version = check_tool(tool)
            if ok:
                print(f"  [OK]      {tool:10s} ({version})")
            else:
                print(f"  [MISSING] {tool}")
                all_foundry = False
        if not all_foundry:
            print("\n  To install Foundry:")
            if sys.platform == "win32":
                print("    Option 1: winget install foundry")
                print("    Option 2 (WSL): curl -L https://foundry.paradigm.xyz | bash && foundryup")
            else:
                print("    curl -L https://foundry.paradigm.xyz | bash && foundryup")

    # Final check
    print("\n\n" + "=" * 60)
    print("Verification")
    print("=" * 60)
    print("\nPython Packages:")
    print("-" * 60)
    results = check_all_phases()

    print("\n" + "=" * 60)
    print("Executability")
    print("=" * 60)
    print_executability(results)

    missing = [k for k, v in results.items() if not k.startswith("phase_") and not v]
    if missing:
        print(f"\n  {len(missing)} packages still missing after install.")
        print(f"  Check errors above for details.")
    else:
        print(f"\n  All packages installed successfully!")

    print()


if __name__ == "__main__":
    main()
