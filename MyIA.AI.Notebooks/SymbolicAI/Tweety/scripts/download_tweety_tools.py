#!/usr/bin/env python3
"""
Script de téléchargement autonome pour les dépendances TweetyProject.

Ce script télécharge automatiquement :
- Les JARs TweetyProject depuis Maven Central
- Les fichiers de ressources (exemples .txt, .aba, .aspic)
- Clingo (ASP solver) pour Windows/Linux
- SPASS (modal logic prover) pour Linux uniquement
- JDK Zulu 17 portable
- Les bibliothèques natives SAT (Minisat, Lingeling, Picosat)

Usage:
    python download_tweety_tools.py [--all] [--jars] [--resources] [--clingo] [--jdk] [--native-sat]
    python download_tweety_tools.py --help

Note: EProver doit être installé manuellement depuis https://eprover.org/
"""

import argparse
import os
import pathlib
import platform
import shutil
import stat
import sys
import tarfile
import urllib.request
import zipfile
from typing import Dict, List, Optional

try:
    from tqdm.auto import tqdm
    HAS_TQDM = True
except ImportError:
    HAS_TQDM = False
    print("Warning: tqdm not installed, progress bars will be disabled")
    print("Install with: pip install tqdm")

try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False
    print("Warning: requests not installed, falling back to urllib")
    print("Install with: pip install requests")


# ============================================================================
# CONFIGURATION
# ============================================================================

TWEETY_VERSION = "1.28"  # Version TweetyProject à télécharger

# URLs de téléchargement
TWEETY_MAVEN_BASE = "https://repo1.maven.org/maven2/org/tweetyproject/"
TWEETY_GITHUB_RAW = "https://raw.githubusercontent.com/TweetyProjectTeam/TweetyProject/main/"

CLINGO_VERSION = "5.4.0"
CLINGO_RELEASES = "https://github.com/potassco/clingo/releases/download"

SPASS_URL = "https://www.spass-prover.org/download/binaries/"

JDK_URLS = {
    "Windows": "https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-win_x64.zip",
    "Linux": "https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-linux_x64.tar.gz",
    "Darwin": "https://cdn.azul.com/zulu/bin/zulu17.50.19-ca-jdk17.0.11-macosx_aarch64.tar.gz",
}

# Modules Tweety requis (tous les notebooks)
REQUIRED_MODULES = [
    "arg.adf", "arg.aba", "arg.bipolar", "arg.aspic", "arg.dung", "arg.weighted",
    "arg.social", "arg.setaf", "arg.rankings", "arg.prob", "arg.extended",
    "arg.delp", "arg.deductive", "arg.caf",
    "beliefdynamics", "agents.dialogues", "action", "preferences",
    "logics.pl", "logics.fol", "logics.ml", "logics.dl", "logics.cl",
    "logics.qbf", "logics.pcl", "logics.rcl", "logics.rpcl", "logics.mln", "logics.bpm",
    "lp.asp", "math", "commons", "agents"
]

# Ajouter arg.eaf pour Tweety 1.29+
if TWEETY_VERSION >= "1.29":
    REQUIRED_MODULES.append("arg.eaf")

REQUIRED_MODULES = sorted(set(REQUIRED_MODULES))

# Fichiers de ressources à télécharger
RESOURCE_FILES = {
    # DeLP Files
    "birds.txt": "org-tweetyproject-arg-delp/src/main/resources/birds.txt",
    "birds2.txt": "org-tweetyproject-arg-delp/src/main/resources/birds2.txt",
    "nixon.txt": "org-tweetyproject-arg-delp/src/main/resources/nixon.txt",
    "counterarg.txt": "org-tweetyproject-arg-delp/src/main/resources/counterarg.txt",
    # ABA Files
    "example1.aba": "org-tweetyproject-arg-aba/src/main/resources/example1.aba",
    "example2.aba": "org-tweetyproject-arg-aba/src/main/resources/example2.aba",
    "example5.aba": "org-tweetyproject-arg-aba/src/main/resources/example5.aba",
    "smp_fol.aba": "org-tweetyproject-arg-aba/src/main/resources/smp_fol.aba",
    # ASPIC Files
    "ex1.aspic": "org-tweetyproject-arg-aspic/src/main/resources/ex1.aspic",
    "ex5_fol.aspic": "org-tweetyproject-arg-aspic/src/main/resources/ex5_fol.aspic",
    # Propositional Logic
    "examplebeliefbase.proplogic": "org-tweetyproject-logics-pl/src/main/resources/examplebeliefbase.proplogic",
    "examplebeliefbase_multiple.proplogic": "org-tweetyproject-logics-pl/src/main/resources/examplebeliefbase_multiple.proplogic",
    "examplebeliefbase_xor.proplogic": "org-tweetyproject-logics-pl/src/main/resources/examplebeliefbase_xor.proplogic",
    "dimacs_ex4.cnf": "org-tweetyproject-logics-pl/src/main/resources/dimacs_ex4.cnf",
    # Description Logic
    "examplebeliefbase.dlogic": "org-tweetyproject-logics-dl/src/main/resources/examplebeliefbase.dlogic",
    # First Order Logic
    "examplebeliefbase2.fologic": "org-tweetyproject-logics-fol/src/main/resources/examplebeliefbase2.fologic",
    # Modal Logic
    "examplebeliefbase.mlogic": "org-tweetyproject-logics-ml/src/main/resources/examplebeliefbase.mlogic",
    "examplebeliefbase2.mlogic": "org-tweetyproject-logics-ml/src/main/resources/examplebeliefbase2.mlogic",
    # QBF
    "tweety-example.qbf": "org-tweetyproject-logics-qbf/src/main/resources/tweety-example.qbf",
    "qdimacs-example1.qdimacs": "org-tweetyproject-logics-qbf/src/main/resources/qdimacs-example1.qdimacs",
    "qcir-example1.qcir": "org-tweetyproject-logics-qbf/src/main/resources/qcir-example1.qcir",
    "qcir-example2-sat.qcir": "org-tweetyproject-logics-qbf/src/main/resources/qcir-example2-sat.qcir",
}


# ============================================================================
# FONCTIONS UTILITAIRES
# ============================================================================

def get_script_dir() -> pathlib.Path:
    """Retourne le répertoire du script (ou le répertoire courant si exécuté depuis un notebook)."""
    try:
        return pathlib.Path(__file__).parent.resolve()
    except NameError:
        # Exécuté depuis un notebook ou un REPL
        return pathlib.Path.cwd()


def download_with_progress(url: str, dest: pathlib.Path, desc: str = "Downloading") -> bool:
    """Télécharge un fichier avec barre de progression."""
    try:
        if HAS_REQUESTS:
            return download_with_requests(url, dest, desc)
        else:
            return download_with_urllib(url, dest, desc)
    except Exception as e:
        print(f"  ERROR: {e}")
        return False


def download_with_urllib(url: str, dest: pathlib.Path, desc: str) -> bool:
    """Télécharge avec urllib.request (fallback)."""
    print(f"  Downloading: {url}")
    urllib.request.urlretrieve(url, dest)
    print(f"  Saved to: {dest}")
    return True


def download_with_requests(url: str, dest: pathlib.Path, desc: str) -> bool:
    """Télécharge avec requests (avec barre de progression si tqdm disponible)."""
    response = requests.get(url, stream=True)
    response.raise_for_status()
    total_size = int(response.headers.get('content-length', 0))

    dest.parent.mkdir(parents=True, exist_ok=True)

    mode = 'wb'
    with open(dest, mode) as f:
        if HAS_TQDM and total_size > 0:
            with tqdm(total=total_size, unit='B', unit_scale=True, desc=desc) as pbar:
                for chunk in response.iter_content(chunk_size=8192):
                    if chunk:
                        f.write(chunk)
                        pbar.update(len(chunk))
        else:
            print(f"  Downloading: {url}")
            for chunk in response.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk)
            print(f"  Saved to: {dest}")

    return True


def download_jar(module_name: str, dest_dir: pathlib.Path, version: str) -> bool:
    """Télécharge un JAR Tweety depuis Maven Central."""
    jar_name = f"org.tweetyproject.{module_name}-{version}-with-dependencies.jar"
    jar_path = dest_dir / jar_name

    if jar_path.exists():
        print(f"  ✓ Already exists: {jar_name}")
        return True

    # Construction URL Maven (structure standard)
    path_parts = module_name.replace('.', '/')
    url = f"{TWEETY_MAVEN_BASE}{module_name}/{version}/{jar_name}"

    if download_with_progress(url, jar_path, desc=f"{module_name}"):
        print(f"  ✓ Downloaded: {jar_name}")
        return True
    else:
        print(f"  ✗ Failed: {jar_name}")
        return False


# ============================================================================
# TÉLÉCHARGEMENT JARs TWEETY
# ============================================================================

def download_tweety_jars(lib_dir: Optional[pathlib.Path] = None) -> bool:
    """Télécharge tous les JARs TweetyProject requis."""
    print("\n" + "=" * 70)
    print("DOWNLOADING TWEETYPROJECT JARS")
    print("=" * 70)

    if lib_dir is None:
        lib_dir = get_script_dir().parent / "libs"

    lib_dir.mkdir(exist_ok=True)
    print(f"Target directory: {lib_dir}")
    print(f"Tweety version: {TWEETY_VERSION}")
    print(f"Required modules: {len(REQUIRED_MODULES)}")

    success_count = 0
    failed_modules = []

    for module in REQUIRED_MODULES:
        if download_jar(module, lib_dir, TWEETY_VERSION):
            success_count += 1
        else:
            failed_modules.append(module)

    print(f"\n✓ Successfully downloaded: {success_count}/{len(REQUIRED_MODULES)} JARs")

    if failed_modules:
        print(f"✗ Failed modules: {', '.join(failed_modules)}")
        return False

    return True


# ============================================================================
# TÉLÉCHARGEMENT RESSOURCES
# ============================================================================

def download_resource_files(resource_dir: Optional[pathlib.Path] = None) -> bool:
    """Télécharge les fichiers de ressources depuis GitHub."""
    print("\n" + "=" * 70)
    print("DOWNLOADING RESOURCE FILES")
    print("=" * 70)

    if resource_dir is None:
        resource_dir = get_script_dir().parent / "resources"

    resource_dir.mkdir(exist_ok=True)
    print(f"Target directory: {resource_dir}")
    print(f"Files to download: {len(RESOURCE_FILES)}")

    success_count = 0
    failed_files = []

    for local_name, github_path in RESOURCE_FILES.items():
        dest = resource_dir / local_name
        url = TWEETY_GITHUB_RAW + github_path

        if dest.exists():
            print(f"  ✓ Already exists: {local_name}")
            success_count += 1
            continue

        if download_with_progress(url, dest, desc=local_name):
            success_count += 1
        else:
            failed_files.append(local_name)

    print(f"\n✓ Successfully downloaded: {success_count}/{len(RESOURCE_FILES)} files")

    if failed_files:
        print(f"✗ Failed files: {', '.join(failed_files)}")
        return False

    return True


# ============================================================================
# TÉLÉCHARGEMENT CLINGO
# ============================================================================

def download_clingo(ext_tools_dir: Optional[pathlib.Path] = None) -> bool:
    """Télécharge Clingo (ASP solver) pour Windows ou Linux."""
    print("\n" + "=" * 70)
    print("DOWNLOADING CLINGO (ASP SOLVER)")
    print("=" * 70)

    system = platform.system()

    if ext_tools_dir is None:
        ext_tools_dir = get_script_dir().parent / "ext_tools"

    clingo_dir = ext_tools_dir / "clingo"
    clingo_dir.mkdir(exist_ok=True)

    exe_name = "clingo.exe" if system == "Windows" else "clingo"
    clingo_exe = clingo_dir / exe_name

    # Vérifier si déjà installé
    if clingo_exe.exists():
        print(f"  ✓ Already exists: {clingo_exe}")
        return True

    # Vérifier dans le PATH
    if shutil.which("clingo") or shutil.which("clingo.exe"):
        print(f"  ✓ Found in system PATH")
        return True

    print(f"Target directory: {clingo_dir}")
    print(f"Clingo version: {CLINGO_VERSION}")

    if system == "Windows":
        url = f"{CLINGO_RELEASES}/v{CLINGO_VERSION}/clingo-{CLINGO_VERSION}-win64.zip"
        archive = clingo_dir / "clingo.zip"

        if not download_with_progress(url, archive, desc="Clingo"):
            return False

        # Extraire
        print("  Extracting...")
        with zipfile.ZipFile(archive, 'r') as zip_ref:
            zip_ref.extractall(clingo_dir)

        # Trouver et déplacer l'exécutable
        for exe in clingo_dir.rglob("clingo.exe"):
            shutil.move(str(exe), str(clingo_exe))
            break

        # Nettoyer
        archive.unlink(missing_ok=True)
        for d in clingo_dir.glob("clingo-*"):
            if d.is_dir():
                shutil.rmtree(d, ignore_errors=True)

        print(f"  ✓ Installed: {clingo_exe}")
        return True

    elif system == "Linux":
        url = f"{CLINGO_RELEASES}/v{CLINGO_VERSION}/clingo-{CLINGO_VERSION}-linux-x86_64.tar.gz"
        archive = clingo_dir / "clingo.tar.gz"

        if not download_with_progress(url, archive, desc="Clingo"):
            return False

        # Extraire
        print("  Extracting...")
        with tarfile.open(archive, 'r:gz') as tar_ref:
            tar_ref.extractall(clingo_dir)

        # Trouver et déplacer l'exécutable
        for exe in clingo_dir.rglob("clingo"):
            shutil.move(str(exe), str(clingo_exe))
            os.chmod(clingo_exe, stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
            break

        # Nettoyer
        archive.unlink(missing_ok=True)
        for d in clingo_dir.glob("clingo-*"):
            if d.is_dir():
                shutil.rmtree(d, ignore_errors=True)

        print(f"  ✓ Installed: {clingo_exe}")
        return True

    else:
        print(f"  ! Automatic download not available for {system}")
        print(f"    Install manually from: https://potassco.org/")
        return False


# ============================================================================
# TÉLÉCHARGEMENT SPASS
# ============================================================================

def download_spass(ext_tools_dir: Optional[pathlib.Path] = None) -> bool:
    """Télécharge SPASS pour Linux uniquement (Windows nécessite installation manuelle)."""
    print("\n" + "=" * 70)
    print("DOWNLOADING SPASS (MODAL LOGIC PROVER)")
    print("=" * 70)

    system = platform.system()

    if ext_tools_dir is None:
        ext_tools_dir = get_script_dir().parent / "ext_tools"

    spass_dir = ext_tools_dir / "spass"
    spass_dir.mkdir(exist_ok=True)

    if system == "Windows":
        print("  ! SPASS for Windows requires manual installation")
        print("    The installer (spass30windows.exe) cannot be automated")
        print()
        print("    Manual installation steps:")
        print("    1. Download from: https://www.spass-prover.org/download/binaries/")
        print("    2. Run the installer")
        print("    3. Copy SPASS.exe to: {}".format(spass_dir))
        print("    4. Copy SPASS-3.0/ folder to: {}".format(spass_dir))
        print()
        print("    Alternatively, use the binary already included in the repository")
        print("    if you have cloned it from version control.")
        return False

    elif system == "Linux":
        arch = "64" if platform.architecture()[0] == "64bit" else "32"
        url = f"{SPASS_URL}spass35pclinux{arch}.tgz"
        archive = spass_dir / "spass.tgz"

        if not download_with_progress(url, archive, desc="SPASS"):
            return False

        # Extraire
        print("  Extracting...")
        with tarfile.open(archive, 'r:gz') as tar_ref:
            tar_ref.extractall(spass_dir)

        archive.unlink(missing_ok=True)

        print(f"  ✓ Installed: {spass_dir}")
        return True

    else:
        print(f"  ! SPASS not available for {system}")
        return False


# ============================================================================
# TÉLÉCHARGEMENT JDK PORTABLE
# ============================================================================

def download_jdk(jdk_dir: Optional[pathlib.Path] = None) -> bool:
    """Télécharge le JDK Zulu 17 portable."""
    print("\n" + "=" * 70)
    print("DOWNLOADING ZULU JDK 17 PORTABLE")
    print("=" * 70)

    system = platform.system()

    if jdk_dir is None:
        jdk_dir = get_script_dir().parent / "jdk-17-portable"

    jdk_dir.mkdir(exist_ok=True)

    if system not in JDK_URLS:
        print(f"  ! JDK download not available for {system}")
        return False

    url = JDK_URLS[system]
    ext = ".zip" if system == "Windows" else ".tar.gz"
    archive = jdk_dir / f"zulu-jdk17{ext}"

    print(f"Target directory: {jdk_dir}")
    print(f"System: {system}")

    if not download_with_progress(url, archive, desc="Zulu JDK 17"):
        return False

    # Extraire
    print("  Extracting (this may take a while)...")

    if system == "Windows":
        with zipfile.ZipFile(archive, 'r') as zip_ref:
            zip_ref.extractall(jdk_dir)
    else:
        with tarfile.open(archive, 'r:gz') as tar_ref:
            tar_ref.extractall(jdk_dir)

    archive.unlink(missing_ok=True)

    # Trouver le dossier JDK extrait
    zulu_dirs = list(jdk_dir.glob("zulu*"))
    if zulu_dirs:
        print(f"  ✓ Installed: {zulu_dirs[0]}")
        return True

    print("  ! JDK directory not found after extraction")
    return False


# ============================================================================
# TÉLÉCHARGEMENT SAT NATIVE LIBS
# ============================================================================

def download_native_sat_libs(native_dir: Optional[pathlib.Path] = None) -> bool:
    """
    Télécharge les bibliothèques natives SAT pour Tweety.

    Note: Ces bibliothèques sont généralement incluses dans le dépôt.
    Cette fonction télécharge depuis TweetyProject si absentes.
    """
    print("\n" + "=" * 70)
    print("DOWNLOADING NATIVE SAT LIBRARIES")
    print("=" * 70)

    if native_dir is None:
        native_dir = get_script_dir().parent / "libs" / "native"

    native_dir.mkdir(parents=True, exist_ok=True)

    print(f"Target directory: {native_dir}")
    print("Note: Native libs are usually included in the repository.")
    print("      This function downloads from GitHub if missing.")

    # Les bibliothèques natives sont dans le dépôt TweetyProject
    base_url = "https://raw.githubusercontent.com/TweetyProjectTeam/TweetyProject/main/"

    # Fichiers à télécharger (Windows DLLs)
    dlls = {
        "lingeling.dll": "org.tweetyproject.logics.pl.sat/src/main/resources/native/windows/lingeling.dll",
        "minisat.dll": "org.tweetyproject.logics.pl.sat/src/main/resources/native/windows/minisat.dll",
        "picosat.dll": "org.tweetyproject.logics.pl.sat/src/main/resources/native/windows/picosat.dll",
    }

    success_count = 0

    for dll_name, github_path in dlls.items():
        dest = native_dir / dll_name

        if dest.exists():
            print(f"  ✓ Already exists: {dll_name}")
            success_count += 1
            continue

        url = base_url + github_path
        if download_with_progress(url, dest, desc=dll_name):
            success_count += 1

    print(f"\n✓ Downloaded: {success_count}/{len(dlls)} libraries")
    return success_count == len(dlls)


# ============================================================================
# FONCTION PRINCIPALE
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Download TweetyProject dependencies",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Download everything
  python download_tweety_tools.py --all

  # Download only JARs
  python download_tweety_tools.py --jars

  # Download JARs and resources
  python download_tweety_tools.py --jars --resources

  # Download external tools (Clingo, SPASS for Linux)
  python download_tweety_tools.py --clingo --spass

  # Download JDK
  python download_tweety_tools.py --jdk
        """
    )

    parser.add_argument("--all", action="store_true", help="Download all dependencies")
    parser.add_argument("--jars", action="store_true", help="Download TweetyProject JARs")
    parser.add_argument("--resources", action="store_true", help="Download resource files")
    parser.add_argument("--clingo", action="store_true", help="Download Clingo ASP solver")
    parser.add_argument("--spass", action="store_true", help="Download SPASS (Linux only)")
    parser.add_argument("--jdk", action="store_true", help="Download Zulu JDK 17")
    parser.add_argument("--native-sat", action="store_true", help="Download native SAT libraries")
    parser.add_argument("--no-interactive", action="store_true", help="Disable progress bars")

    args = parser.parse_args()

    # Si aucun argument spécifié, afficher l'aide
    if not any(vars(args).values()):
        parser.print_help()
        return 0

    # Désactiver tqdm si demandé
    if args.no_interactive:
        global HAS_TQDM
        HAS_TQDM = False

    results = []

    # Exécuter les téléchargements demandés
    if args.all:
        results.append(("JARs", download_tweety_jars()))
        results.append(("Resources", download_resource_files()))
        results.append(("Clingo", download_clingo()))
        results.append(("SPASS", download_spass()))
        results.append(("JDK", download_jdk()))
        results.append(("Native SAT", download_native_sat_libs()))
    else:
        if args.jars:
            results.append(("JARs", download_tweety_jars()))
        if args.resources:
            results.append(("Resources", download_resource_files()))
        if args.clingo:
            results.append(("Clingo", download_clingo()))
        if args.spass:
            results.append(("SPASS", download_spass()))
        if args.jdk:
            results.append(("JDK", download_jdk()))
        if args.native_sat:
            results.append(("Native SAT", download_native_sat_libs()))

    # Résumé
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    for name, success in results:
        status = "✓ SUCCESS" if success else "✗ FAILED"
        print(f"{name:20s}: {status}")

    all_success = all(r[1] for r in results)

    if all_success:
        print("\n✓ All downloads completed successfully!")
        return 0
    else:
        print("\n✗ Some downloads failed. Please check the errors above.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
