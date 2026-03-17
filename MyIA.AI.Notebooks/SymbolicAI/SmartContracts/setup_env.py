#!/usr/bin/env python3
"""Setup environment for the SmartContracts notebook series.

This script:
1. Installs Python dependencies from requirements.txt
2. Installs the Solidity compiler via py-solc-x
3. Checks for Foundry tools (forge, cast, anvil) - native or via WSL
4. Detects WSL and can set up the full WSL environment
5. Starts anvil via WSL when needed
6. Reports what's available and what's missing

Usage:
    python setup_env.py                  # Full setup (install all from requirements.txt)
    python setup_env.py --check          # Check only (don't install)
    python setup_env.py --phase 1        # Install only Phase 1 deps
    python setup_env.py --with-optional  # Also install optional deps (LLM APIs)
    python setup_env.py --venv           # Create a virtual env first
    python setup_env.py --skip-foundry   # Skip Foundry check
    python setup_env.py --setup           # Cross-platform setup (Foundry + venv + kernel)
    python setup_env.py --setup-wsl      # Set up WSL environment (Windows only, alias for --setup)
    python setup_env.py --start-anvil    # Start anvil via WSL in background

Phases (for --phase):
    0: Utilities (matplotlib, tabulate)
    1: Blockchain Core (web3, py-solc-x, python-dotenv)
    2: Cryptography & ZKP (pycryptodome, py_ecc)
    3: Homomorphic Encryption (phe, tenseal)
    4: MPC (mpyc)
    5: Alternative Chains (xrpl-py, python-bitcoinlib, vyper)

Known limitations:
    - concrete-python: Linux only (no Windows wheels, available in WSL)
    - electionguard: requires pydantic<2, conflicts with web3>=7
      -> Install in a separate venv or via WSL
"""

import argparse
import importlib
import os
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
SCRIPTS_DIR = SCRIPT_DIR / "scripts"
REQUIREMENTS_FILE = SCRIPT_DIR / "requirements.txt"
REQUIREMENTS_OPTIONAL_FILE = SCRIPT_DIR / "requirements-optional.txt"
ENV_FILE = SCRIPT_DIR / ".env"
ENV_EXAMPLE_FILE = SCRIPT_DIR / ".env.example"

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
        ("requests>=2.28", "requests"),
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
    6: [  # LLM Integration
        ("openai>=1.0", "openai"),
    ],
}

PHASE_NAMES = {
    0: "Utilities",
    1: "Blockchain Core",
    2: "Cryptography & ZKP",
    3: "Homomorphic Encryption",
    4: "MPC",
    5: "Alternative Chains",
    6: "LLM Integration",
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


def check_wsl_available() -> tuple:
    """Check if WSL is available and Ubuntu is installed.
    Returns (wsl_ok, distro_name, username)."""
    if sys.platform != "win32":
        return False, None, None
    try:
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--", "whoami"],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            username = result.stdout.strip()
            return True, "Ubuntu", username
        return False, None, None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False, None, None


def check_wsl_foundry() -> tuple:
    """Check if Foundry is installed in WSL. Returns (ok, version)."""
    try:
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--cd", "~", "--", "bash", "-c",
             "$HOME/.foundry/bin/forge --version 2>/dev/null || echo MISSING"],
            capture_output=True, text=True, timeout=10
        )
        output = result.stdout.strip()
        if "MISSING" not in output and result.returncode == 0:
            return True, output.split('\n')[0]
        return False, None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False, None


def check_wsl_venv() -> bool:
    """Check if the SmartContracts WSL venv exists."""
    try:
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--cd", "~", "--", "bash", "-c",
             "test -f $HOME/.smartcontracts-venv/bin/python3 && echo OK || echo MISSING"],
            capture_output=True, text=True, timeout=10
        )
        return "OK" in result.stdout
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return False


def check_wsl_kernel() -> bool:
    """Check if the SmartContracts Jupyter kernel is registered."""
    kernel_path = Path(os.environ.get("APPDATA", "")) / "jupyter" / "kernels" / "smartcontracts"
    return (kernel_path / "kernel.json").exists()


def check_env_file() -> dict:
    """Check which .env keys are configured. Returns dict of key->configured."""
    keys = {
        "SEPOLIA_RPC": False,
        "DEPLOYER_PRIVATE_KEY": False,
        "ANVIL_RPC": False,
        "LLM_API_KEY": False,
        "OPENROUTER_API_KEY": False,
    }
    if not ENV_FILE.exists():
        return keys
    for line in ENV_FILE.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        for key in keys:
            if line.startswith(f"{key}="):
                value = line.split("=", 1)[1].strip()
                # Not set if placeholder or empty
                if value and "YOUR_" not in value and "0x..." not in value:
                    keys[key] = True
    return keys


# =============================================================================
# WSL SETUP & ANVIL
# =============================================================================

def setup_environment():
    """Run cross-platform setup: Foundry + venv + kernel.
    On Windows: runs setup.sh inside WSL.
    On Mac/Linux: runs setup.sh natively.
    """
    setup_script = SCRIPTS_DIR / "setup.sh"

    if not setup_script.exists():
        print(f"  ERROR: {setup_script} not found")
        return False

    print("\n  Running setup script...")
    print("  (Installs Foundry, Python venv, all packages, Jupyter kernel)")
    print("  This may take several minutes on first run.\n")

    if sys.platform == "win32":
        # Windows: run inside WSL
        wsl_path = str(setup_script).replace("\\", "/")
        drive = wsl_path[0].lower()
        wsl_path = f"/mnt/{drive}/{wsl_path[3:]}"
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--cd", "~", "--", "bash", wsl_path],
            timeout=600
        )
    else:
        # Mac/Linux: run natively
        result = subprocess.run(["bash", str(setup_script)], timeout=600)

    if result.returncode != 0:
        print(f"  Setup returned exit code {result.returncode}")
        print("  Check the output above for errors.")
        return False

    print("\n  Setup complete!")
    return True


def start_anvil_wsl(port: int = 8545) -> bool:
    """Start anvil in WSL as a background process."""
    if check_anvil_running():
        print(f"  [OK] anvil already running on port {port}")
        return True

    wsl_ok, _, _ = check_wsl_available()
    if not wsl_ok:
        print("  [FAIL] WSL not available")
        return False

    foundry_ok, _ = check_wsl_foundry()
    if not foundry_ok:
        print("  [FAIL] Foundry not installed in WSL. Run: python setup_env.py --setup-wsl")
        return False

    print(f"  Starting anvil on port {port} via WSL...")
    # Start anvil in background - use nohup so it survives
    subprocess.Popen(
        ["wsl", "-d", "Ubuntu", "--cd", "~", "--", "bash", "-c",
         f"$HOME/.foundry/bin/anvil --host 0.0.0.0 --port {port} "
         f"> /tmp/anvil.log 2>&1"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )

    # Wait for it to be ready
    import time
    for _ in range(10):
        time.sleep(0.5)
        if check_anvil_running():
            print(f"  [OK] anvil started on localhost:{port}")
            return True

    print(f"  [FAIL] anvil did not start. Check WSL: cat /tmp/anvil.log")
    return False


def stop_anvil_wsl() -> bool:
    """Stop anvil running in WSL."""
    try:
        subprocess.run(
            ["wsl", "-d", "Ubuntu", "--cd", "~", "--", "bash", "-c",
             "pkill -f anvil 2>/dev/null"],
            capture_output=True, timeout=5
        )
        print("  anvil stopped")
        return True
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
    # Check native Foundry, then WSL Foundry as fallback
    foundry_ok = check_tool("forge")[0]
    if not foundry_ok and sys.platform == "win32":
        foundry_ok, _ = check_wsl_foundry()

    anvil_ok = check_anvil_running()
    web3_ok = results.get("web3", False)
    crypto_ok = results.get("pycryptodome", False) and results.get("py_ecc", False)
    phe_ok = results.get("phe", False)
    vyper_ok = results.get("vyper", False)
    xrpl_ok = results.get("xrpl-py", False)
    bitcoin_ok = results.get("python-bitcoinlib", False)

    # Check .env for testnet/deploy readiness
    env_keys = check_env_file()
    sepolia_ok = env_keys.get("SEPOLIA_RPC", False) and env_keys.get("DEPLOYER_PRIVATE_KEY", False)

    groups = [
        ("SC-0  (Cypherpunk Origins)", results.get("pycryptodome", False), ""),
        ("SC-1  (Setup Foundry)", foundry_ok, "needs forge (native or WSL)"),
        ("SC-2 to SC-10 (Solidity)", anvil_ok and web3_ok, "needs anvil + web3"),
        ("SC-11 (LLM Assisted)", True, ""),  # Has mock fallback
        ("SC-12 to SC-14 (Foundry Testing)", foundry_ok, "needs forge (native or WSL)"),
        ("SC-15 (Zero-Knowledge Proofs)", crypto_ok, "needs pycryptodome + py_ecc"),
        ("SC-16 to SC-17 (HE & Voting)", phe_ok, "needs phe"),
        ("SC-18 (Vyper)", anvil_ok and vyper_ok, "needs anvil + vyper"),
        ("SC-19 (Ripple XRP)", xrpl_ok, "needs xrpl-py + network"),
        ("SC-20 (Bitcoin Scripting)", bitcoin_ok, "needs python-bitcoinlib"),
        ("SC-21 to SC-23 (Theory)", True, ""),
        ("SC-24 (Testnet Deploy)", sepolia_ok and web3_ok, "needs .env: SEPOLIA_RPC + DEPLOYER_PRIVATE_KEY"),
        ("SC-25 (Mainnet Deploy)", web3_ok, "needs .env: BASE_RPC (has default)"),
        ("SC-26 (Final Project)", anvil_ok and phe_ok, "needs anvil + phe"),
    ]

    ready = sum(1 for _, ok, _ in groups if ok)
    total = len(groups)
    print(f"\n  Notebook executability: {ready}/{total} groups ready")
    for name, ok, hint in groups:
        status = "READY" if ok else "BLOCKED"
        suffix = f"  ({hint})" if not ok and hint else ""
        print(f"    [{status:7s}] {name}{suffix}")


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
  python setup_env.py --setup-wsl    # Full WSL setup (Foundry + venv + kernel)
  python setup_env.py --start-anvil  # Start anvil via WSL
  python setup_env.py --stop-anvil   # Stop anvil
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
    parser.add_argument("--setup", action="store_true",
                        help="Cross-platform setup (Foundry + venv + kernel)")
    parser.add_argument("--setup-wsl", action="store_true",
                        help="Alias for --setup (Windows)")
    parser.add_argument("--start-anvil", action="store_true",
                        help="Start anvil via WSL in background")
    parser.add_argument("--stop-anvil", action="store_true",
                        help="Stop anvil running in WSL")
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

    # ---- SETUP ----
    if args.setup or args.setup_wsl:
        if sys.platform == "win32":
            wsl_ok, distro, user = check_wsl_available()
            if not wsl_ok:
                print("  ERROR: WSL with Ubuntu not found.")
                print("  Install with: wsl --install -d Ubuntu")
                return
            print(f"  WSL detected: {distro} (user: {user})")
        setup_environment()
        return

    # ---- ANVIL MANAGEMENT ----
    if args.start_anvil:
        start_anvil_wsl()
        return

    if args.stop_anvil:
        stop_anvil_wsl()
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
            print("\n\nFoundry Tools (native):")
            print("-" * 60)
            native_foundry = True
            for tool in ["forge", "cast", "anvil"]:
                ok, version = check_tool(tool)
                if ok:
                    print(f"  [OK]      {tool:10s} ({version})")
                else:
                    print(f"  [MISSING] {tool}")
                    native_foundry = False

            # WSL Foundry fallback (Windows only)
            if sys.platform == "win32":
                print("\n\nWSL Environment:")
                print("-" * 60)
                wsl_ok, distro, user = check_wsl_available()
                if wsl_ok:
                    print(f"  [OK]      WSL {distro} (user: {user})")
                    wsl_f_ok, wsl_f_ver = check_wsl_foundry()
                    if wsl_f_ok:
                        print(f"  [OK]      Foundry in WSL ({wsl_f_ver})")
                    else:
                        print(f"  [MISSING] Foundry in WSL")
                    if check_wsl_venv():
                        print(f"  [OK]      SmartContracts venv in WSL")
                    else:
                        print(f"  [MISSING] SmartContracts venv in WSL")
                    if check_wsl_kernel():
                        print(f"  [OK]      Jupyter kernel registered")
                    else:
                        print(f"  [MISSING] Jupyter kernel (run --setup-wsl)")
                else:
                    print(f"  [MISSING] WSL Ubuntu not found")

        print("\n\nAnvil Service:")
        print("-" * 60)
        if check_anvil_running():
            print("  [OK]      anvil running on localhost:8545")
        else:
            print("  [OFFLINE] Start with: python setup_env.py --start-anvil")

        print("\n\nConfiguration (.env):")
        print("-" * 60)
        if ENV_FILE.exists():
            env_keys = check_env_file()
            for key, configured in env_keys.items():
                status = "[OK]     " if configured else "[MISSING]"
                print(f"  {status} {key}")
        else:
            print(f"  [MISSING] .env file not found")
            if ENV_EXAMPLE_FILE.exists():
                print(f"           Copy from .env.example: cp .env.example .env")

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
                print(f"  [MISSING] {tool} (native)")
                all_foundry = False

        # Check WSL fallback on Windows
        if not all_foundry and sys.platform == "win32":
            wsl_ok, _, _ = check_wsl_available()
            if wsl_ok:
                wsl_f_ok, wsl_f_ver = check_wsl_foundry()
                if wsl_f_ok:
                    print(f"\n  Foundry available via WSL: {wsl_f_ver}")
                    print("  Notebooks using forge will work via WSL kernel.")
                    all_foundry = True
                else:
                    print("\n  To install Foundry in WSL:")
                    print("    python setup_env.py --setup-wsl")
            else:
                print("\n  To install Foundry:")
                print("    Option 1 (recommended): python setup_env.py --setup-wsl")
                print("    Option 2: curl -L https://foundry.paradigm.xyz | bash && foundryup")

        elif not all_foundry:
            print("\n  To install Foundry:")
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
