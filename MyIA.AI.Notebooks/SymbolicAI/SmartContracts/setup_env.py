#!/usr/bin/env python3
"""Setup environment for the SmartContracts notebook series.

This script:
1. Creates/activates a virtual environment (optional)
2. Installs Python dependencies from requirements.txt
3. Checks for Foundry tools (forge, cast, anvil)
4. Installs the Solidity compiler via py-solc-x
5. Reports what's available and what's missing

Usage:
    python setup_env.py                  # Full setup (install all)
    python setup_env.py --check          # Check only (don't install)
    python setup_env.py --phase 1        # Install only Phase 1 deps
    python setup_env.py --venv           # Create and use a virtual env
    python setup_env.py --skip-foundry   # Skip Foundry check

Phases:
    1: Blockchain Core (web3, py-solc-x)
    2: Cryptography & ZKP (pycryptodome, py_ecc)
    3: Homomorphic Encryption (phe, tenseal, concrete-python)
    4: MPC & Voting (mpyc, electionguard)
    5: Alternative Chains (xrpl-py, python-bitcoinlib, vyper)
"""

import argparse
import importlib
import os
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
REQUIREMENTS_FILE = SCRIPT_DIR / "requirements.txt"

# Phase -> package mapping (for selective install)
PHASES = {
    1: ["web3>=7.0", "py-solc-x>=1.1"],
    2: ["pycryptodome>=3.20", "py_ecc>=7.0"],
    3: ["phe>=1.5", "tenseal>=0.3", "concrete-python>=2.0"],
    4: ["mpyc>=0.10", "electionguard>=1.4"],
    5: ["xrpl-py>=3.0", "python-bitcoinlib>=0.12", "vyper>=0.4"],
    0: ["matplotlib>=3.5", "tabulate>=0.9"],  # Utilities
}

# Map package names to import names
IMPORT_MAP = {
    "web3": "web3",
    "py-solc-x": "solcx",
    "pycryptodome": "Crypto",
    "py_ecc": "py_ecc",
    "phe": "phe",
    "tenseal": "tenseal",
    "concrete-python": "concrete",
    "mpyc": "mpyc",
    "electionguard": "electionguard",
    "xrpl-py": "xrpl",
    "python-bitcoinlib": "bitcoin",
    "vyper": "vyper",
    "matplotlib": "matplotlib",
    "tabulate": "tabulate",
}

SOLC_VERSION = "0.8.28"


def check_python_package(pkg_spec: str) -> tuple:
    """Check if a Python package is installed. Returns (installed, version)."""
    pkg_name = pkg_spec.split(">=")[0].split("==")[0].strip()
    import_name = IMPORT_MAP.get(pkg_name, pkg_name)
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
        import json
        req = urllib.request.Request(
            "http://127.0.0.1:8545",
            method='POST',
            data=b'{"jsonrpc":"2.0","method":"eth_chainId","params":[],"id":1}',
            headers={"Content-Type": "application/json"}
        )
        with urllib.request.urlopen(req, timeout=2) as resp:
            data = json.loads(resp.read())
            return "result" in data
    except Exception:
        return False


def install_packages(packages: list, pip_args: list = None):
    """Install packages via pip."""
    if pip_args is None:
        pip_args = []
    cmd = [sys.executable, "-m", "pip", "install"] + pip_args + packages
    print(f"  Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if result.returncode != 0:
        print(f"  WARNING: Some packages may have failed to install:")
        for line in result.stderr.split('\n'):
            if 'ERROR' in line or 'error' in line:
                print(f"    {line}")
    return result.returncode == 0


def install_solc():
    """Install Solidity compiler via py-solc-x."""
    try:
        import solcx
        installed = [str(v) for v in solcx.get_installed_solc_versions()]
        if SOLC_VERSION in installed:
            print(f"  solc {SOLC_VERSION} already installed")
            return True
        print(f"  Installing solc {SOLC_VERSION}...")
        solcx.install_solc(SOLC_VERSION)
        print(f"  solc {SOLC_VERSION} installed successfully")
        return True
    except ImportError:
        print("  py-solc-x not installed, skipping solc installation")
        return False
    except Exception as e:
        print(f"  Failed to install solc: {e}")
        return False


def create_venv(venv_path: Path):
    """Create a virtual environment."""
    if venv_path.exists():
        print(f"  Virtual env already exists: {venv_path}")
        return
    print(f"  Creating virtual env: {venv_path}")
    subprocess.run([sys.executable, "-m", "venv", str(venv_path)], check=True)
    print(f"  Created. Activate with:")
    if sys.platform == "win32":
        print(f"    {venv_path}\\Scripts\\activate")
    else:
        print(f"    source {venv_path}/bin/activate")


def main():
    parser = argparse.ArgumentParser(description="Setup SmartContracts environment")
    parser.add_argument("--check", action="store_true", help="Check only, don't install")
    parser.add_argument("--phase", type=int, choices=[0, 1, 2, 3, 4, 5],
                        help="Install only specific phase")
    parser.add_argument("--venv", action="store_true",
                        help="Create and use virtual environment")
    parser.add_argument("--skip-foundry", action="store_true",
                        help="Skip Foundry tools check")
    args = parser.parse_args()

    print("=" * 60)
    print("SmartContracts Series - Environment Setup")
    print("=" * 60)

    # Virtual environment
    if args.venv:
        venv_path = SCRIPT_DIR / "venv"
        create_venv(venv_path)
        print()

    # Check/install Python packages
    print("\nPython Packages:")
    print("-" * 60)

    phases_to_check = [args.phase] if args.phase is not None else sorted(PHASES.keys())
    phase_names = {
        0: "Utilities",
        1: "Blockchain Core",
        2: "Cryptography & ZKP",
        3: "Homomorphic Encryption",
        4: "MPC & Voting",
        5: "Alternative Chains",
    }

    all_missing = []
    for phase in phases_to_check:
        packages = PHASES[phase]
        print(f"\n  Phase {phase}: {phase_names[phase]}")
        phase_missing = []
        for pkg in packages:
            ok, version = check_python_package(pkg)
            if ok:
                print(f"    [OK]      {pkg:30s} (v{version})")
            else:
                print(f"    [MISSING] {pkg:30s}")
                phase_missing.append(pkg)

        if phase_missing and not args.check:
            print(f"\n  Installing Phase {phase} packages...")
            install_packages(phase_missing)
            all_missing.extend(phase_missing)
        elif phase_missing:
            all_missing.extend(phase_missing)

    # Install from requirements.txt if doing full install
    if not args.check and args.phase is None and REQUIREMENTS_FILE.exists():
        print(f"\n  Installing from {REQUIREMENTS_FILE}...")
        install_packages(["-r", str(REQUIREMENTS_FILE)])

    # Solidity compiler
    print("\n\nSolidity Compiler:")
    print("-" * 60)
    if not args.check:
        install_solc()
    else:
        try:
            import solcx
            installed = [str(v) for v in solcx.get_installed_solc_versions()]
            if SOLC_VERSION in installed:
                print(f"  [OK]      solc {SOLC_VERSION}")
            else:
                print(f"  [MISSING] solc {SOLC_VERSION} (installed: {installed})")
        except ImportError:
            print(f"  [MISSING] py-solc-x not installed")

    # Foundry tools
    if not args.skip_foundry:
        print("\n\nFoundry Tools:")
        print("-" * 60)
        for tool in ["forge", "cast", "anvil"]:
            ok, version = check_tool(tool)
            if ok:
                print(f"  [OK]      {tool:10s} ({version})")
            else:
                print(f"  [MISSING] {tool:10s}")

        if not check_tool("forge")[0]:
            print("\n  To install Foundry:")
            if sys.platform == "win32":
                print("    1. Install WSL2 (if not already)")
                print("    2. In WSL: curl -L https://foundry.paradigm.xyz | bash")
                print("    3. In WSL: foundryup")
                print("    4. Or use: winget install foundry")
            else:
                print("    curl -L https://foundry.paradigm.xyz | bash && foundryup")

    # Anvil service
    print("\n\nAnvil Service:")
    print("-" * 60)
    if check_anvil_running():
        print("  [OK]      anvil running on localhost:8545")
    else:
        print("  [OFFLINE] anvil not running")
        print("  Start with: anvil (in a separate terminal)")

    # Summary
    print("\n\n" + "=" * 60)
    print("Summary")
    print("=" * 60)

    if all_missing and args.check:
        print(f"\n  Missing packages: {len(all_missing)}")
        print(f"  Install with: python setup_env.py")
        print(f"  Or: pip install -r {REQUIREMENTS_FILE}")
    elif all_missing:
        print(f"\n  Attempted to install {len(all_missing)} packages.")
        print("  Re-run with --check to verify.")
    else:
        print("\n  All Python packages are installed!")

    # Notebook executability summary
    print("\n  Notebook executability:")
    foundry_ok = check_tool("forge")[0]
    anvil_ok = check_anvil_running()
    crypto_ok = check_python_package("pycryptodome")[0] and check_python_package("py_ecc")[0]
    phe_ok = check_python_package("phe")[0]

    nb_groups = [
        ("SC-0  (Cypherpunk Origins)", check_python_package("pycryptodome")[0]),
        ("SC-1  (Setup Foundry)", foundry_ok),
        ("SC-2 to SC-10 (Solidity)", anvil_ok and check_python_package("web3")[0]),
        ("SC-11 (LLM Assisted)", True),  # Has mock fallback
        ("SC-12 to SC-14 (Foundry Testing)", foundry_ok),
        ("SC-15 (Zero-Knowledge Proofs)", crypto_ok),
        ("SC-16 to SC-17 (HE & Voting)", phe_ok),
        ("SC-18 (Vyper)", anvil_ok and check_python_package("vyper")[0]),
        ("SC-19 (Ripple XRP)", check_python_package("xrpl-py")[0]),
        ("SC-20 (Bitcoin Scripting)", check_python_package("python-bitcoinlib")[0]),
        ("SC-21 to SC-23 (Theory)", True),
        ("SC-24 to SC-25 (Deploy)", False),  # Needs API keys
        ("SC-26 (Final Project)", anvil_ok and phe_ok),
    ]

    for name, ready in nb_groups:
        status = "READY" if ready else "BLOCKED"
        print(f"    [{status:7s}] {name}")

    print()


if __name__ == "__main__":
    main()
