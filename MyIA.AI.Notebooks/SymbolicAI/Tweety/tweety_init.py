"""
Module d'initialisation partagé pour les notebooks Tweety.

Ce module centralise la configuration JVM et la détection des outils externes
pour éviter la duplication de code entre les notebooks.

Usage dans un notebook:
    from tweety_init import init_tweety, EXTERNAL_TOOLS, get_tool_path
    jvm_ready = init_tweety()
"""

import os
import pathlib
import platform
import shutil
import sys

# Configuration des outils externes
EXTERNAL_TOOLS = {
    "CLINGO": "",
    "SPASS": "",
    "EPROVER": "",
    "SAT_SOLVER_PYTHON": "",
    "MARCO": "",
}

def get_tool_path(tool_name):
    """Retourne le chemin valide d'un outil ou None."""
    path_str = EXTERNAL_TOOLS.get(tool_name, "")
    if not path_str:
        return None
    if shutil.which(path_str):
        return path_str
    path_obj = pathlib.Path(path_str)
    if path_obj.is_file():
        return str(path_obj.resolve())
    if path_obj.is_dir():
        return str(path_obj.resolve())
    return None


def _detect_tools():
    """Auto-détection des outils externes."""
    system = platform.system()
    exe_suffix = ".exe" if system == "Windows" else ""

    # 1. Clingo (ASP solver) - Tweety attend le REPERTOIRE
    for cp in [shutil.which("clingo"),
               pathlib.Path(f"ext_tools/clingo/clingo{exe_suffix}"),
               pathlib.Path(f"../ext_tools/clingo/clingo{exe_suffix}")]:
        if cp and (isinstance(cp, str) or cp.exists()):
            parent = pathlib.Path(cp).parent if isinstance(cp, str) else cp.parent
            EXTERNAL_TOOLS["CLINGO"] = str(parent.resolve())
            break

    # 2. SPASS (Modal logic prover) - dans SPASS-3.0/
    for sp in [shutil.which("SPASS"),
               pathlib.Path(f"ext_tools/spass/SPASS-3.0/SPASS{exe_suffix}"),
               pathlib.Path(f"../ext_tools/spass/SPASS-3.0/SPASS{exe_suffix}")]:
        if sp and (isinstance(sp, str) or sp.exists()):
            EXTERNAL_TOOLS["SPASS"] = str(pathlib.Path(sp).resolve()) if isinstance(sp, pathlib.Path) else sp
            break

    # 3. EProver (FOL theorem prover)
    for ep in [shutil.which("eprover"),
               pathlib.Path(f"../ext_tools/EProver/eprover{exe_suffix}"),
               pathlib.Path(f"ext_tools/EProver/eprover{exe_suffix}")]:
        if ep:
            ep_path = pathlib.Path(ep) if isinstance(ep, str) else ep
            if ep_path.exists():
                EXTERNAL_TOOLS["EPROVER"] = str(ep_path.resolve())
                break

    # 4. SAT Solver Python (CaDiCaL, Glucose via pySAT)
    for sat in [pathlib.Path("../ext_tools/sat_solver.py"),
                pathlib.Path("ext_tools/sat_solver.py")]:
        if sat.exists():
            EXTERNAL_TOOLS["SAT_SOLVER_PYTHON"] = str(sat.resolve())
            break

    # 5. MARCO (MUS enumerator avec Z3)
    for mp in [pathlib.Path("../ext_tools/marco.py"),
               pathlib.Path("ext_tools/marco.py")]:
        if mp.exists():
            EXTERNAL_TOOLS["MARCO"] = str(mp.resolve())
            break


def _find_jdk_portable():
    """Recherche le JDK portable dans l'arborescence."""
    for jdk_path in [pathlib.Path("jdk-17-portable"),
                     pathlib.Path("../Argument_Analysis/jdk-17-portable")]:
        if jdk_path.exists():
            zulu_dirs = list(jdk_path.glob("zulu*"))
            if zulu_dirs:
                return zulu_dirs[0]
    return None


def _find_libs_dir():
    """Recherche le dossier libs contenant les JARs Tweety."""
    for lib_path in [pathlib.Path("libs"),
                     pathlib.Path("../Argument_Analysis/libs")]:
        if lib_path.exists():
            return lib_path
    return None


def init_tweety(verbose=True):
    """
    Initialise l'environnement Tweety (JVM + outils externes).

    Args:
        verbose: Afficher les messages de progression

    Returns:
        bool: True si la JVM est prête, False sinon
    """
    import jpype
    import jpype.imports

    if verbose:
        print("--- Initialisation Tweety ---")

    # Détection des outils
    _detect_tools()

    # Vérifier si JVM déjà démarrée
    if jpype.isJVMStarted():
        if verbose:
            print("JVM deja en cours d'execution.")
        return True

    # Recherche JDK portable
    jdk_portable = _find_jdk_portable()
    if jdk_portable:
        os.environ["JAVA_HOME"] = str(jdk_portable.resolve())
        if verbose:
            print(f"JDK portable: {jdk_portable.name}")

    if not os.environ.get("JAVA_HOME"):
        if verbose:
            print("ERREUR: JAVA_HOME non defini et JDK portable non trouve.")
        return False

    # Recherche JARs
    lib_dir = _find_libs_dir()
    if not lib_dir:
        if verbose:
            print("ERREUR: Dossier libs non trouve.")
        return False

    jar_files = list(lib_dir.glob("*.jar"))
    if not jar_files:
        if verbose:
            print("ERREUR: Aucun JAR trouve dans libs/")
        return False

    # Recherche des bibliothèques natives (DLL/SO pour SAT solvers)
    native_libs_dir = lib_dir / "native"
    if not native_libs_dir.exists():
        native_libs_dir = pathlib.Path("../Argument_Analysis/libs/native")

    # IMPORTANT: Mettre le dossier native EN PREMIER dans le classpath
    # Cela permet à getResource() de trouver les DLL dans le dossier
    # au lieu du JAR, ce qui résout le bug de chargement des solvers natifs
    classpath_items = []
    if native_libs_dir.exists():
        classpath_items.append(str(native_libs_dir.resolve()))
    classpath_items.extend(str(j.resolve()) for j in jar_files)
    classpath = os.pathsep.join(classpath_items)

    jvm_args = []
    if native_libs_dir.exists():
        jvm_args.append(f"-Djava.library.path={native_libs_dir.resolve()}")
        if verbose:
            print(f"Bibliotheques natives: {native_libs_dir.name}/")

    try:
        jpype.startJVM(*jvm_args, classpath=[classpath])
        if verbose:
            print(f"JVM demarree avec {len(jar_files)} JARs.")
        return True
    except Exception as e:
        if verbose:
            print(f"Erreur demarrage JVM: {e}")
        return False


def print_tools_summary():
    """Affiche un résumé des outils disponibles."""
    print("\n--- Outils disponibles ---")
    count = 0
    for tool, path in EXTERNAL_TOOLS.items():
        if path:
            short_path = path.split(os.sep)[-1] if len(path) > 30 else path
            print(f"  {tool}: {short_path}")
            count += 1
        else:
            print(f"  {tool}: non configure")
    print(f"\nOutils: {count}/{len(EXTERNAL_TOOLS)}")


# Auto-détection au chargement du module
_detect_tools()
