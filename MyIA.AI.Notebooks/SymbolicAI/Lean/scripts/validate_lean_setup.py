#!/usr/bin/env python3
"""
Script de validation complet de l'environnement Lean
Verifie tous les composants et la configuration

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


# Le nom de DISTRIBUTION n'est pas le nom de MODULE (#21614, defaut 4) :
# `python-dotenv` s'importe sous `dotenv`. La transformation automatique
# `-` -> `_` produisait `python_dotenv`, un module qui n'existe pas : le
# check concluait "Non installe" pour un paquet present et importable --
# un faux negatif qui retirait une composante sur deux, sur chaque poste.
PKG_IMPORTS = {
    "python-dotenv": "dotenv",
    "openai": "openai",
    "anthropic": "anthropic",
    "ipykernel": "ipykernel",
}


def print_section(title):
    print(_safe(f"\n{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}"))
    print(_safe(f"{Colors.BOLD}{Colors.BLUE}{title:^60}{Colors.END}"))
    print(_safe(f"{Colors.BOLD}{Colors.BLUE}{'='*60}{Colors.END}\n"))


def print_ok(msg):
    print(_safe(f"{Colors.GREEN}✓{Colors.END} {msg}"))


def print_error(msg):
    print(_safe(f"{Colors.RED}✗{Colors.END} {msg}"))


def print_warning(msg):
    print(_safe(f"{Colors.YELLOW}⚠{Colors.END} {msg}"))


# Encodage console (#21614, defaut 1)
# -------------------------------------
# Le validateur imprime des glyphes Unicode (✓ ✗ ⚠ ═) et des tirets
# cadratins ; sur une console Windows cp1252 (sortie redirigee, code page
# par defaut) `print` leve UnicodeEncodeError et le validateur MEURT a la
# premiere ligne de resultat -- il ne rend jamais son verdict, ce qui est
# precisement ce qu'on lui demande.
#
# On garde l'encodage de la console : un `reconfigure(encoding="utf-8")`
# y ecrirait des octets UTF-8 dans un consommateur cp1252, donc du
# mojibake partout. On remplace ce qui ne passe pas, et on met stdout en
# `errors="replace"` pour qu'aucune autre chaine ne puisse tuer le verdict.
def _safe(text: str) -> str:
    """Return `text` encodable par la sortie courante, sans jamais lever."""
    encoding = getattr(sys.stdout, "encoding", None) or "ascii"
    try:
        text.encode(encoding)
        return text
    except (UnicodeEncodeError, LookupError):
        return text.encode(encoding, errors="replace").decode(encoding, errors="replace")


def _configure_stdout() -> None:
    """Rend stdout et stderr tolerants aux caracteres non encodables."""
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:
            continue
        try:
            reconfigure(errors="replace")
        except (ValueError, OSError):
            pass


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
    if platform.system() == "Linux" and cmd in ["elan", "lean", "lake"]:
        try:
            # Essayer avec source .elan/env
            bash_cmd = f"source ~/.elan/env 2>/dev/null && {cmd} {version_flag}"
            result = subprocess.run(
                ["bash", "-c", bash_cmd],
                capture_output=True,
                text=True, encoding="utf-8", errors="replace",
                timeout=10
            )
            if result.returncode == 0:
                version = result.stdout.strip().split('\n')[0]
                print_ok(f"{name}: {version}")
                return True
        except Exception as e:
            pass

    # Méthode standard
    path = shutil.which(cmd)
    if path:
        try:
            result = subprocess.run(
                [cmd, version_flag],
                capture_output=True,
                text=True, encoding="utf-8", errors="replace",
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
        import_name = PKG_IMPORTS.get(pkg_name, pkg_name.replace("-", "_"))

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
            text=True, encoding="utf-8", errors="replace",
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


def _load_inspect_kernel_wrapper():
    """Import the canonical wrapper check from scripts/lean/lean_kernel_check.py.

    Returns None if the shared helper cannot be located (graceful degradation).
    """
    return _load_kernel_helper("inspect_kernel_wrapper")


def _load_kernel_helper(name):
    """Import one helper from the canonical scripts/lean/lean_kernel_check.py.

    Returns None if the shared helper cannot be located (graceful degradation).
    """
    here = Path(__file__).resolve()
    for parent in here.parents:
        candidate = parent / "scripts" / "lean" / "lean_kernel_check.py"
        if candidate.exists():
            sys.path.insert(0, str(candidate.parent))
            try:
                module = __import__("lean_kernel_check")
                return getattr(module, name)
            except Exception:
                return None
    return None


_inspect_kernel_wrapper = _load_inspect_kernel_wrapper()
_kernel_drives_wsl = _load_kernel_helper("kernel_drives_wsl")


def check_kernel_wrapper(kernel_name="lean4-wsl"):
    """Verifie que kernel.json pointe vers le bon wrapper Python (v5), pas l'ancien bash.

    Detecte la regression du 2026-05-27 (issue #1618). La logique canonique vit dans
    scripts/lean/lean_kernel_check.py (source unique partagee avec setup_lean4_all.py
    et le validateur GameTheory).
    """
    if _inspect_kernel_wrapper is None:
        print_warning("kernel.json: helper lean_kernel_check introuvable (check ignore)")
        return True
    status, message = _inspect_kernel_wrapper(kernel_name)
    {"ok": print_ok, "error": print_error, "warning": print_warning}[status](message)
    return status == "ok"


def check_env_file():
    """Verifie le fichier .env"""
    env_path = Path(__file__).parent.parent / ".env"

    if not env_path.exists():
        print_error(f".env: Fichier manquant ({env_path})")
        return False

    # Verifier les cles importantes
    with open(env_path, 'r') as f:
        content = f.read()

    keys = ["OPENAI_API_KEY", "ANTHROPIC_API_KEY", "GITHUB_TOKEN"]
    found_keys = [k for k in keys if k in content and not content.split(k)[1].split('\n')[0].strip().startswith('#')]

    if found_keys:
        print_ok(f".env: Present avec {len(found_keys)}/{len(keys)} cles")
        return True
    else:
        print_warning(f".env: Present mais aucune cle API configuree")
        return False


def check_lean_runner():
    """Verifie lean_runner.py"""
    lean_runner_path = Path(__file__).parent.parent / "lean_runner.py"

    if not lean_runner_path.exists():
        print_error("lean_runner.py: Manquant")
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


def check_lean_toolchain():
    """Composants Lean 4, selon le cote ou la chaine est reellement installee.

    Sur un poste installe en WSL -- le kernel ``lean4-wsl`` est enregistre
    cote Windows mais appelle ``wsl.exe`` -- la chaine elan/lean/lake vit
    dans la distro. Compter les binaires Windows comme des composants
    MANQUANTS produisait un verdict incoherent avec ce que le setup
    installe (issue #21614, defaut 2 : « 3/13 » sur un poste sain).

    Trois cas, dans cet ordre :

    1. la chaine Windows est complete -> 3 composants, comme avant ;
    2. la chaine Windows est absente mais le poste est un poste WSL -> la
       chaine est validee par le mode ``--wsl`` ; elle n'est donc pas un
       composant manquant de cette section (verdict explicite) ;
    3. sinon -> les 3 composants Windows sont Manquants (verdict honnete).
    """
    present = [shutil.which(cmd) for cmd in ("elan", "lean", "lake")]
    if all(present):
        return [check_command("elan", "elan"),
                check_command("lean", "Lean 4"),
                check_command("lake", "Lake")]
    if _kernel_drives_wsl is not None and _kernel_drives_wsl("lean4-wsl"):
        print_ok("Chaine Lean 4 : poste installe en WSL (kernel lean4-wsl -> wsl.exe) "
                 "-- validee cote WSL par le mode --wsl, hors perimetre de cette section")
        return []
    return [check_command("elan", "elan"),
            check_command("lean", "Lean 4"),
            check_command("lake", "Lake")]


def validate_windows():
    """Validation pour environnement Windows"""
    print_section("VALIDATION ENVIRONNEMENT WINDOWS")

    checks = []

    # Composants de base
    checks.append(check_python())
    checks.extend(check_lean_toolchain())

    # Packages Python
    checks.append(check_python_package("lean4-jupyter", "lean4_jupyter"))
    checks.append(check_python_package("python-dotenv", "dotenv"))
    checks.append(check_python_package("openai"))
    checks.append(check_python_package("anthropic"))

    # Kernels
    checks.append(check_jupyter_kernel("lean4"))
    checks.append(check_jupyter_kernel("python3-wsl"))
    checks.append(check_kernel_wrapper("lean4-wsl"))

    # Fichiers projet
    checks.append(check_env_file())
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
        print("  1. Ouvrir Lean-01-Setup-Lean-Python.ipynb")
        print("  2. Executer toutes les cellules")
        return False


def validate_wsl():
    """Validation pour environnement WSL"""
    print_section("VALIDATION ENVIRONNEMENT WSL")

    checks = []

    # Composants de base
    checks.append(check_python())
    checks.append(check_command("elan", "elan"))
    checks.append(check_command("lean", "Lean 4"))

    # Kernel wrapper (regression check #1618)
    checks.append(check_kernel_wrapper("lean4-wsl"))

    # Venv Python WSL
    venv_path = Path.home() / ".python3-wsl-venv"
    if venv_path.exists():
        print_ok(f"Venv Python WSL: {venv_path}")
        checks.append(True)
    else:
        print_error(f"Venv Python WSL: Manquant ({venv_path})")
        checks.append(False)

    # Packages dans venv
    venv_python = venv_path / "bin" / "python3"
    if venv_python.exists():
        for pkg in PKG_IMPORTS:
            try:
                result = subprocess.run(
                    [str(venv_python), "-c", f"import {PKG_IMPORTS[pkg]}"],
                    capture_output=True,
                    timeout=5
                )
                if result.returncode == 0:
                    print_ok(f"{pkg} (venv WSL)")
                    checks.append(True)
                else:
                    print_error(f"{pkg} (venv WSL): Non installe")
                    checks.append(False)
            except Exception as e:
                print_error(f"{pkg} (venv WSL): Erreur ({e})")
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
        print("  bash scripts/setup_wsl_python.sh")
        return False


def main():
    # Verdict lisible meme sur une console cp1252 (#21614, defaut 1) :
    # configure AVANT tout print.
    _configure_stdout()

    parser = argparse.ArgumentParser(description="Valide l'environnement Lean")
    parser.add_argument("--wsl", action="store_true", help="Valider dans WSL")
    args = parser.parse_args()

    print(f"{Colors.BOLD}VALIDATION ENVIRONNEMENT LEAN 4{Colors.END}")
    print(f"Script: {__file__}")

    if args.wsl:
        success = validate_wsl()
    else:
        success = validate_windows()

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
