#!/usr/bin/env python3
"""Validate and test SmartContracts notebook series (SC-0 to SC-26).

This script performs:
1. Structural validation (cells, format, navigation, metadata)
2. Dependency checking (per-notebook requirements)
3. Dry-run execution (cells that don't need external services)
4. Full execution (with anvil/foundry/testnet when available)

Usage:
    python scripts/validate_sc_notebooks.py                    # Full validation
    python scripts/validate_sc_notebooks.py --quick            # Structure only
    python scripts/validate_sc_notebooks.py --check-deps       # Check dependencies
    python scripts/validate_sc_notebooks.py --execute          # Execute safe cells
    python scripts/validate_sc_notebooks.py --execute --anvil  # Execute with anvil
    python scripts/validate_sc_notebooks.py --notebook SC-15   # Single notebook
    python scripts/validate_sc_notebooks.py --fix              # Auto-fix issues
"""

import argparse
import importlib
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# =============================================================================
# CONFIGURATION
# =============================================================================

SC_BASE = Path("d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts")

# All 27 notebooks in order, with their execution profiles
NOTEBOOKS = [
    # (directory, name, profile)
    # Profiles:
    #   "standalone"  = pure Python, no external service needed
    #   "anvil"       = needs anvil running (web3.py + py-solcx)
    #   "foundry"     = needs forge/cast CLI tools
    #   "crypto"      = needs crypto libraries (pycryptodome, py_ecc, phe, etc.)
    #   "network"     = needs network access (testnet, API keys)
    #   "llm"         = needs LLM API or local LLM (graceful fallback)
    #   "theoretical" = mostly markdown/theoretical, minimal code
    ("00-Foundations", "SC-0-Cypherpunk-Origins", "standalone"),
    ("00-Foundations", "SC-1-Setup-Foundry", "foundry"),
    ("00-Foundations", "SC-2-Setup-Web3py", "anvil"),
    ("01-Solidity-Foundation", "SC-3-Solidity-Basics", "anvil"),
    ("01-Solidity-Foundation", "SC-4-Functions-State", "anvil"),
    ("01-Solidity-Foundation", "SC-5-Inheritance", "anvil"),
    ("01-Solidity-Foundation", "SC-6-Errors-Events", "anvil"),
    ("02-Solidity-Advanced", "SC-7-Token-Standards", "anvil"),
    ("02-Solidity-Advanced", "SC-8-DeFi-Primitives", "anvil"),
    ("02-Solidity-Advanced", "SC-9-DAO-Governance", "anvil"),
    ("02-Solidity-Advanced", "SC-10-Account-Abstraction", "anvil"),
    ("02-Solidity-Advanced", "SC-11-LLM-Assisted", "llm"),
    ("03-Foundry-Testing", "SC-12-Foundry-Testing", "foundry"),
    ("03-Foundry-Testing", "SC-13-Fuzz-Invariants", "foundry"),
    ("03-Foundry-Testing", "SC-14-Formal-Verification", "foundry"),
    ("04-Privacy-Cryptography", "SC-15-Zero-Knowledge-Proofs", "crypto"),
    ("04-Privacy-Cryptography", "SC-16-Homomorphic-Encryption", "crypto"),
    ("04-Privacy-Cryptography", "SC-17-E2E-Verifiable-Voting", "crypto"),
    ("05-Alternative-Chains", "SC-18-Vyper", "anvil"),
    ("05-Alternative-Chains", "SC-19-Ripple-XRP", "network"),
    ("05-Alternative-Chains", "SC-20-Bitcoin-Scripting", "standalone"),
    ("05-Alternative-Chains", "SC-21-Move-Sui", "theoretical"),
    ("05-Alternative-Chains", "SC-22-Solana-Anchor", "theoretical"),
    ("06-Real-World", "SC-23-Cross-Chain", "theoretical"),
    ("06-Real-World", "SC-24-Testnet-Deploy", "network"),
    ("06-Real-World", "SC-25-Mainnet-Deploy", "network"),
    ("06-Real-World", "SC-26-Final-Project", "anvil"),
]

# Dependencies per profile
PROFILE_DEPS = {
    "standalone": {
        "python": ["hashlib", "pycryptodome"],
        "tools": [],
        "services": [],
    },
    "anvil": {
        "python": ["web3", "solcx"],
        "tools": ["anvil"],
        "services": ["http://127.0.0.1:8545"],
    },
    "foundry": {
        "python": [],
        "tools": ["forge", "cast", "anvil"],
        "services": [],
    },
    "crypto": {
        "python": ["pycryptodome", "py_ecc", "phe"],
        "tools": [],
        "services": [],
    },
    "llm": {
        "python": ["openai", "anthropic"],
        "tools": [],
        "services": [],
    },
    "network": {
        "python": ["web3", "xrpl"],
        "tools": [],
        "services": [],
    },
    "theoretical": {
        "python": [],
        "tools": [],
        "services": [],
    },
}

# Per-notebook specific Python imports needed (overrides profile defaults)
NOTEBOOK_IMPORTS = {
    "SC-0-Cypherpunk-Origins": ["hashlib", "Crypto"],
    "SC-2-Setup-Web3py": ["web3", "solcx"],
    "SC-3-Solidity-Basics": ["web3", "solcx"],
    "SC-4-Functions-State": ["web3", "solcx"],
    "SC-5-Inheritance": ["web3", "solcx"],
    "SC-6-Errors-Events": ["web3", "solcx"],
    "SC-7-Token-Standards": ["web3", "solcx"],
    "SC-8-DeFi-Primitives": ["web3", "solcx"],
    "SC-9-DAO-Governance": ["web3", "solcx"],
    "SC-10-Account-Abstraction": ["web3", "solcx"],
    "SC-11-LLM-Assisted": ["openai", "anthropic", "requests"],
    "SC-15-Zero-Knowledge-Proofs": ["Crypto", "py_ecc"],
    "SC-16-Homomorphic-Encryption": ["phe"],
    "SC-17-E2E-Verifiable-Voting": ["phe", "Crypto"],
    "SC-18-Vyper": ["vyper", "web3"],
    "SC-19-Ripple-XRP": ["xrpl"],
    "SC-20-Bitcoin-Scripting": ["bitcoin"],
    "SC-24-Testnet-Deploy": ["web3"],
    "SC-25-Mainnet-Deploy": ["web3"],
    "SC-26-Final-Project": ["web3", "solcx", "phe"],
}


# =============================================================================
# ANSI COLORS
# =============================================================================

class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    BOLD = '\033[1m'
    END = '\033[0m'

    @classmethod
    def disable(cls):
        for attr in ['GREEN', 'RED', 'YELLOW', 'BLUE', 'CYAN', 'BOLD', 'END']:
            setattr(cls, attr, '')


# =============================================================================
# DATACLASSES
# =============================================================================

@dataclass
class CellInfo:
    index: int
    cell_type: str
    cell_id: str
    source_len: int
    has_output: bool
    is_exercise: bool
    is_nav: bool
    source_format: str  # "list" or "string"
    first_line: str


@dataclass
class NotebookValidation:
    name: str
    path: str
    profile: str
    exists: bool = True
    cell_count: int = 0
    code_cells: int = 0
    markdown_cells: int = 0
    has_navigation_header: bool = False
    has_navigation_footer: bool = False
    has_title: bool = False
    has_objectives: bool = False
    has_duration: bool = False
    has_prerequisites: bool = False
    has_web3_setup: bool = False
    has_compile_deploy: bool = False
    string_format_cells: int = 0
    consecutive_code_cells: int = 0
    empty_cells: int = 0
    exercise_cells: int = 0
    exposed_solutions: int = 0
    errors: List[str] = field(default_factory=list)
    warnings: List[str] = field(default_factory=list)
    deps_available: Dict[str, bool] = field(default_factory=dict)


# =============================================================================
# VALIDATION FUNCTIONS
# =============================================================================

def source_text(cell) -> str:
    """Get cell source as a single string."""
    src = cell.get('source', '')
    if isinstance(src, list):
        return ''.join(src)
    return src


def is_nav_cell(text: str) -> bool:
    """Check if text contains navigation links."""
    return bool(re.search(r'\[<<\s', text) or re.search(r'\s>>\]', text))


def has_exposed_solution(text: str) -> bool:
    """Check if a code cell contains a full solution (not an exercise skeleton).

    Excludes:
    - Exercise skeletons (TODO, NotImplementedError, # Votre code)
    - Instructional examples in Python strings (triple-quoted Solidity)
    """
    # Heuristics: has TODO/raise NotImplementedError -> exercise, not solution
    if 'TODO' in text or 'NotImplementedError' in text or '# Votre code' in text:
        return False
    # Solidity code in Python string literals is instructional, not a solution
    if re.search(r"=\s*['\"]'''|=\s*'''|=\s*\"\"\"", text):
        return False
    # Check for suspiciously complete test implementations (actual executable code)
    if re.search(r'function\s+test_\w+.*\{[^}]+assertEq\s*\(', text, re.DOTALL):
        return True
    return False


def validate_notebook(nb_dir: str, nb_name: str, profile: str) -> NotebookValidation:
    """Validate a single notebook's structure and content."""
    nb_path = SC_BASE / nb_dir / f"{nb_name}.ipynb"
    result = NotebookValidation(name=nb_name, path=str(nb_path), profile=profile)

    if not nb_path.exists():
        result.exists = False
        result.errors.append("Notebook file not found")
        return result

    try:
        with open(nb_path, 'r', encoding='utf-8') as f:
            nb = json.load(f)
    except json.JSONDecodeError as e:
        result.errors.append(f"Invalid JSON: {e}")
        return result

    cells = nb.get('cells', [])
    result.cell_count = len(cells)

    if result.cell_count == 0:
        result.errors.append("Notebook has no cells")
        return result

    prev_type = None
    consecutive_code = 0

    for i, cell in enumerate(cells):
        cell_type = cell.get('cell_type', 'unknown')
        text = source_text(cell)
        src = cell.get('source', '')

        # Count cell types
        if cell_type == 'code':
            result.code_cells += 1
        elif cell_type == 'markdown':
            result.markdown_cells += 1

        # Check source format
        if isinstance(src, str) and src:
            result.string_format_cells += 1

        # Check empty cells
        if not text.strip():
            result.empty_cells += 1

        # Check consecutive code cells
        if cell_type == 'code' and prev_type == 'code':
            consecutive_code += 1
            if consecutive_code > result.consecutive_code_cells:
                result.consecutive_code_cells = consecutive_code
        else:
            consecutive_code = 0
        prev_type = cell_type

        # Check for exercises
        if 'TODO' in text or 'NotImplementedError' in text:
            result.exercise_cells += 1

        # Check for exposed solutions (in exercise cells)
        if cell_type == 'code' and has_exposed_solution(text):
            result.exposed_solutions += 1

    # Check first cell for title/nav
    first_text = source_text(cells[0])
    if first_text.startswith('# SC-') or first_text.startswith('# '):
        result.has_title = True
    if is_nav_cell(first_text):
        result.has_navigation_header = True

    # Check last few cells for footer nav
    for cell in cells[-3:]:
        text = source_text(cell)
        if is_nav_cell(text):
            result.has_navigation_footer = True
            break

    # Check for pedagogical elements (scan all markdown cells)
    full_md = '\n'.join(source_text(c) for c in cells if c.get('cell_type') == 'markdown')
    if re.search(r'objectif|apprentissage|learning', full_md, re.IGNORECASE):
        result.has_objectives = True
    if re.search(r'dur[ée]e|minutes|min\b', full_md, re.IGNORECASE):
        result.has_duration = True
    if re.search(r'pr[ée]requis|prerequisite', full_md, re.IGNORECASE):
        result.has_prerequisites = True

    # Check for web3 setup (relevant for anvil-profile notebooks)
    full_code = '\n'.join(source_text(c) for c in cells if c.get('cell_type') == 'code')
    if 'from web3 import Web3' in full_code or 'import web3' in full_code:
        result.has_web3_setup = True
    if 'compile_and_deploy' in full_code:
        result.has_compile_deploy = True

    # Generate errors/warnings
    if result.string_format_cells > 0:
        result.errors.append(f"{result.string_format_cells} cells have STRING format (should be LIST)")
    if not result.has_title:
        result.errors.append("Missing title (first cell should start with '# SC-')")
    if not result.has_navigation_header:
        result.warnings.append("Missing navigation header")
    if not result.has_navigation_footer:
        result.warnings.append("Missing navigation footer")
    if not result.has_objectives:
        result.warnings.append("Missing learning objectives section")
    if not result.has_duration:
        result.warnings.append("Missing estimated duration")
    if result.empty_cells > 0:
        result.warnings.append(f"{result.empty_cells} empty cells")
    if result.consecutive_code_cells > 2:
        result.warnings.append(f"{result.consecutive_code_cells} consecutive code cells without markdown")
    if result.exposed_solutions > 0:
        result.errors.append(f"{result.exposed_solutions} potentially exposed solutions")

    # Profile-specific checks
    if profile == "anvil" and not result.has_web3_setup:
        result.errors.append("Anvil notebook missing web3.py setup cell")
    if profile == "anvil" and not result.has_compile_deploy:
        result.warnings.append("Anvil notebook missing compile_and_deploy helper")

    return result


# =============================================================================
# DEPENDENCY CHECKING
# =============================================================================

def check_python_import(module_name: str) -> Tuple[bool, str]:
    """Check if a Python module is importable."""
    # Map package names to import names
    import_map = {
        "pycryptodome": "Crypto",
        "py_ecc": "py_ecc",
        "python-bitcoinlib": "bitcoin",
        "py-solc-x": "solcx",
        "xrpl-py": "xrpl",
    }
    actual_import = import_map.get(module_name, module_name)

    try:
        mod = importlib.import_module(actual_import)
        version = getattr(mod, "__version__", "?")
        return True, f"v{version}"
    except ImportError:
        return False, "not installed"
    except Exception as e:
        return False, str(e)


def check_tool(tool_name: str) -> Tuple[bool, str]:
    """Check if a CLI tool is available."""
    try:
        result = subprocess.run(
            [tool_name, "--version"],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return True, result.stdout.strip().split('\n')[0]
        return False, result.stderr.strip()[:80]
    except FileNotFoundError:
        return False, "not installed"
    except subprocess.TimeoutExpired:
        return False, "timeout"
    except Exception as e:
        return False, str(e)[:80]


def check_service(url: str) -> Tuple[bool, str]:
    """Check if a network service is reachable."""
    try:
        import urllib.request
        req = urllib.request.Request(url, method='POST',
                                     data=b'{"jsonrpc":"2.0","method":"eth_chainId","params":[],"id":1}',
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=3) as resp:
            data = json.loads(resp.read())
            chain_id = int(data.get('result', '0x0'), 16)
            return True, f"chain_id={chain_id}"
    except Exception as e:
        return False, str(e)[:60]


def check_all_dependencies() -> Dict[str, Dict[str, Tuple[bool, str]]]:
    """Check all dependencies across all profiles."""
    results = {"python": {}, "tools": {}, "services": {}}

    # Collect all unique deps
    all_python = set()
    all_tools = set()
    all_services = set()
    for nb_name, imports in NOTEBOOK_IMPORTS.items():
        all_python.update(imports)
    for profile in PROFILE_DEPS.values():
        all_tools.update(profile["tools"])
        all_services.update(profile["services"])

    print(f"\n{Colors.BOLD}Checking Python packages...{Colors.END}")
    for pkg in sorted(all_python):
        ok, info = check_python_import(pkg)
        results["python"][pkg] = (ok, info)
        status = f"{Colors.GREEN}OK{Colors.END}" if ok else f"{Colors.RED}MISSING{Colors.END}"
        print(f"  {pkg:25s} : {status} ({info})")

    print(f"\n{Colors.BOLD}Checking CLI tools...{Colors.END}")
    for tool in sorted(all_tools):
        ok, info = check_tool(tool)
        results["tools"][tool] = (ok, info)
        status = f"{Colors.GREEN}OK{Colors.END}" if ok else f"{Colors.RED}MISSING{Colors.END}"
        print(f"  {tool:25s} : {status} ({info})")

    print(f"\n{Colors.BOLD}Checking services...{Colors.END}")
    for svc in sorted(all_services):
        ok, info = check_service(svc)
        results["services"][svc] = (ok, info)
        status = f"{Colors.GREEN}OK{Colors.END}" if ok else f"{Colors.YELLOW}OFFLINE{Colors.END}"
        print(f"  {svc:45s} : {status} ({info})")

    return results


# =============================================================================
# FIX FUNCTIONS
# =============================================================================

def make_source_list(text: str) -> list:
    """Convert text to LIST format source."""
    lines = text.split('\n')
    result = []
    for i, line in enumerate(lines):
        if i < len(lines) - 1:
            result.append(line + '\n')
        elif line:
            result.append(line)
    return result


def fix_notebook(nb_dir: str, nb_name: str) -> List[str]:
    """Fix common issues in a notebook. Returns list of fixes applied."""
    nb_path = SC_BASE / nb_dir / f"{nb_name}.ipynb"
    fixes = []

    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    modified = False

    # Fix STRING format cells
    for cell in nb['cells']:
        src = cell.get('source', '')
        if isinstance(src, str) and src:
            cell['source'] = make_source_list(src)
            modified = True
            fixes.append(f"Fixed STRING format in cell {cell.get('id', '?')}")

    # Fix empty source
    for cell in nb['cells']:
        if cell.get('source') is None:
            cell['source'] = []
            modified = True
            fixes.append("Fixed None source")

    # Remove empty cells
    original_count = len(nb['cells'])
    nb['cells'] = [c for c in nb['cells'] if source_text(c).strip() or c.get('cell_type') == 'code']
    if len(nb['cells']) < original_count:
        removed = original_count - len(nb['cells'])
        fixes.append(f"Removed {removed} empty cells")
        modified = True

    if modified:
        with open(nb_path, 'w', encoding='utf-8', newline='\n') as f:
            json.dump(nb, f, ensure_ascii=False, indent=1)
            f.write('\n')

    return fixes


# =============================================================================
# EXECUTION
# =============================================================================

def get_executable_cells(nb_path: Path, profile: str, anvil_available: bool) -> List[Tuple[int, str]]:
    """Get list of (index, source) for cells that can be safely executed.

    Skips:
    - Exercise cells (TODO, NotImplementedError)
    - Cells requiring unavailable services
    - pip install cells
    """
    with open(nb_path, 'r', encoding='utf-8') as f:
        nb = json.load(f)

    executable = []
    for i, cell in enumerate(nb['cells']):
        if cell.get('cell_type') != 'code':
            continue
        text = source_text(cell)
        if not text.strip():
            continue

        # Skip exercises
        if 'NotImplementedError' in text or '# TODO' in text:
            continue

        # Skip pip install
        if text.strip().startswith('!pip') or text.strip().startswith('# !pip'):
            continue

        # Skip cells that require anvil if not available
        if not anvil_available and profile == "anvil":
            if 'w3.eth' in text or 'transact(' in text or 'compile_and_deploy' in text:
                continue
            if "Web3.HTTPProvider" in text or "w3.is_connected" in text:
                continue

        executable.append((i, text))

    return executable


def execute_cells_subprocess(nb_path: Path, cells: List[Tuple[int, str]], timeout: int = 30) -> List[dict]:
    """Execute cells in a subprocess and collect results."""
    results = []
    for idx, source in cells:
        try:
            proc = subprocess.run(
                [sys.executable, "-c", source],
                capture_output=True, text=True, timeout=timeout,
                cwd=str(nb_path.parent),
            )
            results.append({
                "cell_index": idx,
                "success": proc.returncode == 0,
                "stdout": proc.stdout[:500] if proc.stdout else "",
                "stderr": proc.stderr[:500] if proc.stderr else "",
            })
        except subprocess.TimeoutExpired:
            results.append({
                "cell_index": idx,
                "success": False,
                "stdout": "",
                "stderr": f"Timeout after {timeout}s",
            })
        except Exception as e:
            results.append({
                "cell_index": idx,
                "success": False,
                "stdout": "",
                "stderr": str(e)[:500],
            })
    return results


# =============================================================================
# REPORTING
# =============================================================================

def print_validation_report(validations: List[NotebookValidation]):
    """Print a comprehensive validation report."""
    print(f"\n{'='*80}")
    print(f"{Colors.BOLD}SmartContracts Series Validation Report{Colors.END}")
    print(f"{'='*80}\n")

    total_errors = 0
    total_warnings = 0
    total_cells = 0

    for v in validations:
        if not v.exists:
            print(f"  {Colors.RED}MISSING{Colors.END}  {v.name}")
            total_errors += 1
            continue

        status_icon = f"{Colors.GREEN}OK{Colors.END}" if not v.errors else f"{Colors.RED}FAIL{Colors.END}"
        if v.warnings and not v.errors:
            status_icon = f"{Colors.YELLOW}WARN{Colors.END}"

        print(f"  {status_icon:>20s}  {v.name:40s}  [{v.profile:12s}]  "
              f"{v.cell_count:3d} cells ({v.code_cells}C/{v.markdown_cells}M)")

        for err in v.errors:
            print(f"         {Colors.RED}ERROR: {err}{Colors.END}")
            total_errors += 1
        for warn in v.warnings:
            print(f"         {Colors.YELLOW}WARN:  {warn}{Colors.END}")
            total_warnings += 1

        total_cells += v.cell_count

    # Summary
    print(f"\n{'='*80}")
    ok_count = sum(1 for v in validations if v.exists and not v.errors)
    warn_count = sum(1 for v in validations if v.exists and v.warnings and not v.errors)
    fail_count = sum(1 for v in validations if not v.exists or v.errors)
    missing_count = sum(1 for v in validations if not v.exists)

    print(f"\n{Colors.BOLD}Summary:{Colors.END}")
    print(f"  Notebooks : {len(validations)} total, "
          f"{Colors.GREEN}{ok_count} OK{Colors.END}, "
          f"{Colors.YELLOW}{warn_count} warnings{Colors.END}, "
          f"{Colors.RED}{fail_count} errors{Colors.END}"
          f"{f', {missing_count} missing' if missing_count else ''}")
    print(f"  Cells     : {total_cells} total")
    print(f"  Issues    : {total_errors} errors, {total_warnings} warnings")

    # Exercises summary
    total_exercises = sum(v.exercise_cells for v in validations if v.exists)
    print(f"  Exercises : {total_exercises} cells with TODO/NotImplementedError")

    # Profile breakdown
    profiles = {}
    for v in validations:
        if v.exists:
            profiles.setdefault(v.profile, []).append(v.name)
    print(f"\n{Colors.BOLD}Profiles:{Colors.END}")
    for profile, nbs in sorted(profiles.items()):
        print(f"  {profile:15s} : {len(nbs)} notebooks")

    return total_errors == 0


def print_deps_matrix(validations: List[NotebookValidation], deps: Dict):
    """Print which notebooks can be executed given current dependencies."""
    print(f"\n{Colors.BOLD}Executability Matrix:{Colors.END}")

    anvil_ok = deps["services"].get("http://127.0.0.1:8545", (False, ""))[0]
    forge_ok = deps["tools"].get("forge", (False, ""))[0]

    for v in validations:
        if not v.exists:
            continue

        can_execute = True
        blockers = []

        if v.profile == "anvil" and not anvil_ok:
            can_execute = False
            blockers.append("anvil")
        if v.profile == "foundry" and not forge_ok:
            can_execute = False
            blockers.append("forge")

        # Check notebook-specific imports
        for imp in NOTEBOOK_IMPORTS.get(v.name, []):
            ok = deps["python"].get(imp, (False, ""))[0]
            if not ok:
                can_execute = False
                blockers.append(imp)

        if v.profile in ("network",):
            can_execute = False
            blockers.append("network access")

        status = f"{Colors.GREEN}READY{Colors.END}" if can_execute else f"{Colors.YELLOW}BLOCKED{Colors.END}"
        blocker_str = f" (needs: {', '.join(blockers)})" if blockers else ""
        print(f"  {status:>20s}  {v.name}{blocker_str}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Validate SmartContracts notebooks")
    parser.add_argument("--quick", action="store_true", help="Structure validation only")
    parser.add_argument("--check-deps", action="store_true", help="Check all dependencies")
    parser.add_argument("--execute", action="store_true", help="Execute safe cells")
    parser.add_argument("--anvil", action="store_true", help="Include anvil-dependent cells")
    parser.add_argument("--fix", action="store_true", help="Auto-fix issues")
    parser.add_argument("--notebook", type=str, help="Validate single notebook (e.g., SC-15)")
    parser.add_argument("--no-color", action="store_true", help="Disable color output")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    args = parser.parse_args()

    if args.no_color:
        Colors.disable()

    # Filter notebooks if --notebook specified
    notebooks = NOTEBOOKS
    if args.notebook:
        pattern = args.notebook.upper()
        notebooks = [(d, n, p) for d, n, p in NOTEBOOKS if pattern in n.upper()]
        if not notebooks:
            print(f"{Colors.RED}No notebook matching '{args.notebook}'{Colors.END}")
            sys.exit(1)

    # Dependency check
    deps = None
    if args.check_deps or args.execute:
        deps = check_all_dependencies()

    # Structural validation
    print(f"\n{Colors.BOLD}Validating {len(notebooks)} notebooks...{Colors.END}")
    validations = []
    for nb_dir, nb_name, profile in notebooks:
        v = validate_notebook(nb_dir, nb_name, profile)
        validations.append(v)

    all_ok = print_validation_report(validations)

    if deps:
        print_deps_matrix(validations, deps)

    # Auto-fix
    if args.fix:
        print(f"\n{Colors.BOLD}Applying fixes...{Colors.END}")
        for nb_dir, nb_name, profile in notebooks:
            nb_path = SC_BASE / nb_dir / f"{nb_name}.ipynb"
            if not nb_path.exists():
                continue
            fixes = fix_notebook(nb_dir, nb_name)
            if fixes:
                for fix in fixes:
                    print(f"  {Colors.GREEN}FIXED{Colors.END}: {nb_name} - {fix}")
            else:
                if args.verbose:
                    print(f"  {nb_name}: no fixes needed")
        print("Re-validating...")
        validations = [validate_notebook(d, n, p) for d, n, p in notebooks]
        all_ok = print_validation_report(validations)

    # Execution
    if args.execute:
        anvil_ok = deps["services"].get("http://127.0.0.1:8545", (False, ""))[0] if deps else False
        use_anvil = args.anvil and anvil_ok

        print(f"\n{Colors.BOLD}Executing safe cells...{Colors.END}")
        if use_anvil:
            print(f"  {Colors.GREEN}anvil detected - including blockchain cells{Colors.END}")
        else:
            print(f"  {Colors.YELLOW}No anvil - skipping blockchain cells{Colors.END}")

        for nb_dir, nb_name, profile in notebooks:
            nb_path = SC_BASE / nb_dir / f"{nb_name}.ipynb"
            if not nb_path.exists():
                continue

            cells = get_executable_cells(nb_path, profile, use_anvil)
            if not cells:
                if args.verbose:
                    print(f"  {nb_name}: no executable cells (profile={profile})")
                continue

            print(f"\n  {Colors.CYAN}{nb_name}{Colors.END}: executing {len(cells)} cells...")
            results = execute_cells_subprocess(nb_path, cells, timeout=60)

            ok = sum(1 for r in results if r["success"])
            fail = len(results) - ok
            if fail == 0:
                print(f"    {Colors.GREEN}{ok}/{len(results)} cells passed{Colors.END}")
            else:
                print(f"    {Colors.RED}{fail}/{len(results)} cells FAILED{Colors.END}")
                for r in results:
                    if not r["success"] and r["stderr"]:
                        print(f"      Cell {r['cell_index']}: {r['stderr'][:100]}")

    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
