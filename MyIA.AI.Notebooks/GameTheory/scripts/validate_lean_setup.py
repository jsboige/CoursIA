#!/usr/bin/env python3
"""
Script de validation de l'environnement Lean pour GameTheory
Adapte de la serie Lean existante

Usage:
    python scripts/validate_lean_setup.py
    python scripts/validate_lean_setup.py --wsl  # Test dans WSL
"""

import subprocess
import sys
import os
import shutil
from pathlib import Path
import argparse


class Colors:
    GREEN = '\033[92m'
    RED = '\033[91m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    END = '\033[0m'
    BOLD = '\033[1m'


def print_section(title):
    print(f"\n{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.BLUE}{title:^60}{Colors.END}")
    print(f"{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}\n")


def print_ok(msg):
    print(f"{Colors.GREEN}[OK]{Colors.END} {msg}")


def print_error(msg):
    print(f"{Colors.RED}[X]{Colors.END} {msg}")


def print_warning(msg):
    print(f"{Colors.YELLOW}[!]{Colors.END} {msg}")


def check_python():
    """Verifie Python >= 3.8"""
    version = f"{sys.version_info.major}.{sys.version_info.minor}"
    if sys.version_info >= (3, 8):
        print_ok(f"Python {version}")
        return True
    else:
        print_error(f"Python {version} (3.8+ requis)")
        return False


def check_command(cmd, name, version_flag="--version"):
    """Verifie si une commande existe et retourne sa version"""
    import platform

    # Sur Linux/WSL, sourcer .elan/env pour elan/lean/lake
    if platform.system() == "Linux" and cmd in ["elan", "lean", "lake", "repl"]:
        try:
            bash_cmd = f"source ~/.elan/env 2>/dev/null && {cmd} {version_flag}"
            result = subprocess.run(
                ["bash", "-c", bash_cmd],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                version = result.stdout.strip().split('\n')[0]
                print_ok(f"{name}: {version}")
                return True
        except Exception:
            pass

    # Methode standard
    path = shutil.which(cmd)
    if path:
        try:
            result = subprocess.run(
                [cmd, version_flag],
                capture_output=True,
                text=True,
                timeout=5
            )
            version = result.stdout.strip().split('\n')[0]
            print_ok(f"{name}: {version}")
            return True
        except Exception as e:
            print_warning(f"{name}: Trouve mais erreur version ({e})")
            return True
    else:
        print_error(f"{name}: Non trouve")
        return False


def check_python_package(pkg_name, import_name=None):
    """Verifie si un package Python est installe"""
    if import_name is None:
        import_name = pkg_name.replace("-", "_")

    try:
        mod = __import__(import_name)
        version = getattr(mod, "__version__", "unknown")
        print_ok(f"{pkg_name}: {version}")
        return True
    except ImportError:
        print_error(f"{pkg_name}: Non installe")
        return False


def check_jupyter_kernel(kernel_name):
    """Verifie si un kernel Jupyter est enregistre"""
    try:
        result = subprocess.run(
            ["jupyter", "kernelspec", "list"],
            capture_output=True,
            text=True,
            timeout=10
        )
        if kernel_name.lower() in result.stdout.lower():
            print_ok(f"Kernel Jupyter: {kernel_name}")
            return True
        else:
            print_error(f"Kernel Jupyter: {kernel_name} non trouve")
            return False
    except Exception as e:
        print_error(f"Kernel Jupyter: Erreur verification ({e})")
        return False


def check_social_choice_lean():
    """Verifie que le projet Lake social_choice_lean existe"""
    project_path = Path(__file__).parent.parent / "social_choice_lean"
    lakefile = project_path / "lakefile.lean"

    if lakefile.exists():
        print_ok(f"social_choice_lean: Projet Lake trouve")
        return True
    else:
        print_error(f"social_choice_lean: Projet Lake manquant ({project_path})")
        return False


def check_lean_runner():
    """Verifie lean_runner.py dans la serie Lean"""
    lean_runner_path = Path(__file__).parent.parent.parent / "SymbolicAI" / "Lean" / "lean_runner.py"

    if not lean_runner_path.exists():
        print_error(f"lean_runner.py: Manquant ({lean_runner_path})")
        return False

    # Essayer d'importer
    sys.path.insert(0, str(lean_runner_path.parent))
    try:
        import lean_runner
        print_ok(f"lean_runner.py: OK ({lean_runner_path.stat().st_size} bytes)")
        return True
    except Exception as e:
        print_error(f"lean_runner.py: Erreur import ({e})")
        return False


def validate_windows():
    """Validation pour environnement Windows"""
    print_section("VALIDATION ENVIRONNEMENT GAMETHEORY LEAN")

    checks = []

    # Composants de base
    checks.append(check_python())
    checks.append(check_command("elan", "elan"))
    checks.append(check_command("lean", "Lean 4"))
    checks.append(check_command("lake", "Lake"))

    # Packages Python
    checks.append(check_python_package("lean4-jupyter", "lean4_jupyter"))
    checks.append(check_python_package("nashpy"))
    checks.append(check_python_package("numpy"))
    checks.append(check_python_package("sympy"))

    # Kernels Lean
    checks.append(check_jupyter_kernel("lean4"))
    checks.append(check_jupyter_kernel("lean4-wsl"))

    # Projets Lean
    checks.append(check_social_choice_lean())
    checks.append(check_lean_runner())

    # Resultat
    total = len(checks)
    success = sum(checks)

    print_section("RESULTAT")

    if success == total:
        print_ok(f"Tous les composants OK ({success}/{total})")
        return True
    else:
        print_warning(f"Composants OK: {success}/{total}")
        print("\nPour installer les composants manquants:")
        print("  1. Executez dans WSL: bash scripts/setup_wsl_lean4.sh")
        print("  2. Executez PowerShell: .\\scripts\\setup_lean4_kernel.ps1")
        print("  3. Redemarrez VSCode")
        return False


def validate_wsl():
    """Validation pour environnement WSL"""
    print_section("VALIDATION ENVIRONNEMENT WSL")

    checks = []

    # Composants de base
    checks.append(check_python())
    checks.append(check_command("elan", "elan"))
    checks.append(check_command("lean", "Lean 4"))
    checks.append(check_command("repl", "REPL"))

    # Venv Python WSL
    venv_path = Path.home() / ".lean4-venv"
    if venv_path.exists():
        print_ok(f"Venv Lean4: {venv_path}")
        checks.append(True)
    else:
        print_error(f"Venv Lean4: Manquant ({venv_path})")
        checks.append(False)

    # Wrapper
    wrapper_path = Path.home() / ".lean4-kernel-wrapper.py"
    if wrapper_path.exists():
        print_ok(f"Kernel wrapper: {wrapper_path}")
        checks.append(True)
    else:
        print_error(f"Kernel wrapper: Manquant ({wrapper_path})")
        checks.append(False)

    # Packages dans venv
    venv_python = venv_path / "bin" / "python3"
    if venv_python.exists():
        for pkg in ["lean4_jupyter", "ipykernel"]:
            try:
                result = subprocess.run(
                    [str(venv_python), "-c", f"import {pkg.replace('-', '_')}"],
                    capture_output=True,
                    timeout=5
                )
                if result.returncode == 0:
                    print_ok(f"{pkg} (venv)")
                    checks.append(True)
                else:
                    print_error(f"{pkg} (venv): Non installe")
                    checks.append(False)
            except Exception as e:
                print_error(f"{pkg} (venv): Erreur ({e})")
                checks.append(False)

    # Resultat
    total = len(checks)
    success = sum(checks)

    print_section("RESULTAT WSL")

    if success == total:
        print_ok(f"Tous les composants WSL OK ({success}/{total})")
        return True
    else:
        print_warning(f"Composants WSL OK: {success}/{total}")
        print("\nPour installer les composants manquants:")
        print("  bash scripts/setup_wsl_lean4.sh")
        return False


def main():
    parser = argparse.ArgumentParser(description="Valide l'environnement Lean pour GameTheory")
    parser.add_argument("--wsl", action="store_true", help="Valider dans WSL")
    args = parser.parse_args()

    print(f"{Colors.BOLD}VALIDATION ENVIRONNEMENT LEAN 4 - GAMETHEORY{Colors.END}")
    print(f"Script: {__file__}")

    if args.wsl:
        success = validate_wsl()
    else:
        success = validate_windows()

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
