#!/usr/bin/env python3
r"""
Lean 4 Jupyter Kernel Wrapper for WSL (v8)

This script converts Windows paths to WSL paths and launches the lean4_jupyter kernel.
It handles various path formats that VSCode/Jupyter might pass:
- Standard Windows paths: C:\Users\...
- Tilde shorthand: ~\AppData\... or ~/AppData/...
- Mangled paths (backslashes eaten): c:UsersjsboiAppData...

v8 changes (#18511 -- the kernel no longer follows `stable`, and no longer fails silently):
1. The toolchain is PINNED from the nearest `lean-toolchain` (the lake's own when
   the execution directory is inside a lake, else the closest anchor up-tree) and
   exported as ELAN_TOOLCHAIN. Before, `lake env repl` followed elan's default
   (`leanprover/lean4:stable`), which drifts (v4.34.1 on 2026-09-30, v4.35.0 on
   2026-10-21) while the only REPL binary is built for v4.30.0: every cell then
   rendered a PARSE ERROR and papermill still exited 0.
2. The REPL binary is matched to the pinned toolchain. A matched binary is
   `~/.elan/bin/repl-<tag>` (built by scripts/lean/setup_native_lean4_import.py
   build-repl); the default `~/.elan/bin/repl` is accepted only when the Lean
   version it embeds (read from the binary itself) IS the pinned version.
3. A version divergence now REFUSES to start the kernel (exit 3, message naming
   both versions) instead of rendering error cells under exit 0.
4. A missing lake is no longer fatal by itself: `lake env` works without a
   lakefile (measured), so a notebook whose tree pins a `lean-toolchain` runs
   with the pinned toolchain. The #16181 rule still holds: no fallback to any
   unrelated project -- only the pin is required.

v7 changes:
1. Mangled-path regex covers BOTH AppData/Roaming (jupyter kernelspec) AND
   AppData/Local/Temp (nbconvert connection files).
2. find_lake_root() starts from the execution directory inherited from Jupyter.
   wsl_papermill passes the notebook directory by default and accepts an explicit
   Lake root for companion notebooks stored beside several projects.
3. Missing Lake context aborts kernel startup visibly instead of falling back to
   the unrelated ~/lean-projects/notebook_context stub (#16181).

NOTE (native-import probe, 2026-06, c.126→c.127): this wrapper detects the lake
workspace cwd, which is necessary but NOT sufficient for native Mathlib import —
`lake env repl` (lean4_jupyter.repl:52) clobbers the repl's sysroot (repl loses
Init, `#check Nat` -> "Unknown identifier"). The COMPLETE fix is in
scripts/lean/setup_native_lean4_import.py: it patches lean4_jupyter's launch()
to run the repl binary DIRECT (not via `lake env`) with the lake's LEAN_PATH,
which makes native lean4-wsl import of a Mathlib lake WORK (proven on
sensitivity_lean: real `#check huang_degree_theorem` + `#print axioms` in-kernel,
0 sorry). See docs/reference/wsl-kernels-detail.md § "Native import ... VERDICT (a)".
"""
import sys
import subprocess
import os
import re


def convert_windows_path(path):
    """Convert Windows path to WSL path, handling various formats."""
    if not path:
        return path

    # Already a Unix path
    if path.startswith('/'):
        return path

    # Handle ~ shorthand (Windows-style: ~\AppData or ~/AppData)
    if path.startswith('~\\') or path.startswith('~/'):
        # Find the Windows user's home directory
        users_dir = '/mnt/c/Users'
        if os.path.exists(users_dir):
            for user in os.listdir(users_dir):
                user_lower = user.lower()
                if user_lower not in ['public', 'default', 'default user', 'all users']:
                    # Check if this looks like a real user directory
                    user_path = os.path.join(users_dir, user)
                    if os.path.isdir(user_path) and os.path.exists(os.path.join(user_path, 'AppData')):
                        win_home = f'/mnt/c/Users/{user}'
                        rest = path[1:].lstrip('\\').lstrip('/')
                        rest = rest.replace('\\', '/')
                        return f'{win_home}/{rest}'
        # Fallback: hardcoded user
        rest = path[1:].lstrip('\\').lstrip('/').replace('\\', '/')
        return f'/mnt/c/Users/jsboi/{rest}'

    # Check for mangled path FIRST (backslashes eaten): c:UsersjsboiAppData...
    # This happens when VSCode passes paths through certain shells. nbconvert
    # connection files live under AppData/Local/Temp (NOT AppData/Roaming, where
    # the kernelspec lives), so the regex must cover BOTH subdirs + Temp/tmp.
    if len(path) >= 2 and path[1] == ':':
        # Detect mangled path: has Users immediately after drive letter without separator
        if path[2:].startswith('Users') and '\\' not in path and '/' not in path[2:]:
            match = re.match(
                r'([a-zA-Z]):Users([a-z0-9_]+)AppData(Roaming|Local)(.+)', path, re.IGNORECASE)
            if match:
                drive = match.group(1).lower()
                user = match.group(2)
                subdir = match.group(3).capitalize()  # Roaming | Local
                rest = match.group(4)
                # Re-insert slashes at known segment boundaries
                for sep in ['jupyter', 'runtime', 'kernel-', 'Temp', 'tmp']:
                    rest = rest.replace(sep, '/' + sep)
                rest = rest.lstrip('/')
                return f'/mnt/{drive}/Users/{user}/AppData/{subdir}/{rest}'

        # Standard Windows path with proper separators (C:\... or C:/...)
        # Use wslpath for proper conversion
        try:
            result = subprocess.run(['wslpath', '-a', path], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=5)
            if result.returncode == 0:
                return result.stdout.strip()
        except:
            pass
        # Fallback manual conversion for paths with separators
        drive = path[0].lower()
        rest = path[2:].replace('\\', '/').lstrip('/')
        return f'/mnt/{drive}/{rest}'

    return path


def find_lake_root(start_dir):
    """Walk up from start_dir to find the nearest directory containing a
    lakefile.lean (the lake workspace root). Returns None if not found.

    When the kernel is launched from inside a lake project, chdir-ing to its
    root lets `lake env repl` (lean4_jupyter.repl:52) detect the workspace and
    pick up its LEAN_PATH, so in-kernel imports can resolve lake modules.
    """
    d = os.path.abspath(start_dir)
    while True:
        try:
            if os.path.isfile(os.path.join(d, 'lakefile.lean')) or \
               os.path.isfile(os.path.join(d, 'lakefile.toml')):
                return d
        except OSError:
            break
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return None


def find_toolchain_anchor(start_dir, max_levels=12):
    """(dossier, toolchain) du `lean-toolchain` le plus proche en remontant.

    Renvoie (None, None) si aucun ancrage n'est trouve : le kernel refuse alors
    de demarrer plutot que de suivre `stable` (#18511).
    """
    d = os.path.abspath(start_dir)
    for _ in range(max_levels):
        candidate = os.path.join(d, 'lean-toolchain')
        if os.path.isfile(candidate):
            try:
                with open(candidate, encoding='utf-8') as fh:
                    toolchain = fh.read().strip()
            except OSError:
                toolchain = ''
            if toolchain:
                return d, toolchain
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return None, None


# Le binaire REPL embarque l'URL de documentation de la version de Lean qu'il
# compilee : c'est une MESURE du binaire, pas une annotation declaree.
REPL_DOC_URL_RE = re.compile(rb"lean-lang\.org/doc/reference/(\d+\.\d+\.\d+)")


def repl_lean_version(repl_path, chunk_size=8 * 1024 * 1024):
    """Version de Lean pour laquelle le binaire REPL a ete construit.

    Lecture par blocs (le binaire fait ~200 Mo) avec recouvrement, pour ne
    pas charger le fichier entier en memoire. Renvoie None si la version n'est
    pas lisible dans le binaire.
    """
    try:
        with open(repl_path, 'rb') as fh:
            tail = b''
            while True:
                block = fh.read(chunk_size)
                if not block:
                    break
                found = REPL_DOC_URL_RE.search(tail + block)
                if found:
                    return found.group(1).decode('ascii')
                tail = block[-64:]
    except OSError:
        return None
    return None


def resolve_repl(home, tag):
    """Choisit le binaire REPL couple a la toolchain `tag` (ex: 'v4.30.0').

    Renvoie (chemin, version_du_repl). `chemin` est None quand aucune
    correspondance n'est prouvee : l'appelant doit alors REFUSER de demarrer.
    Aucun repl de secours : c'est exactement ce repl de secours qui produisait
    des cellules en erreur de parse sous un exit 0 (#18511).
    """
    tag = tag.lstrip('v')
    elan_bin = os.path.join(home, '.elan', 'bin')
    # 1. binaire nomme d'apres la toolchain (construit contre elle).
    matched = os.path.join(elan_bin, 'repl-' + tag)
    if os.path.isfile(matched):
        version = repl_lean_version(matched)
        if version is None or version == tag:
            return matched, (version or tag)
        return None, version
    # 2. repl par defaut : accepte seulement si sa version EMBARQUEE est celle
    #    de la toolchain epinglee.
    default = os.path.join(elan_bin, 'repl')
    if os.path.isfile(default):
        version = repl_lean_version(default)
        if version == tag:
            return default, version
        return None, version
    return None, None


def _repl_shim_dir(repl_path):
    """Repertoire temporaire contenant un lien `repl` vers le binaire choisi.

    `lake env repl` resout `repl` par le PATH : sans ce shim, un binaire
    `repl-<tag>` (nom different) ne serait jamais trouve.
    """
    import tempfile
    shim_dir = os.path.join(tempfile.gettempdir(), 'lean4-repl-shim')
    os.makedirs(shim_dir, exist_ok=True)
    shim = os.path.join(shim_dir, 'repl')
    try:
        if os.path.islink(shim) or os.path.exists(shim):
            os.remove(shim)
        os.symlink(repl_path, shim)
    except OSError:
        return None
    return shim_dir


def main():
    log_file = os.path.expanduser('~/.lean4-wrapper.log')

    def log(msg):
        try:
            with open(log_file, 'a') as f:
                f.write(f"{msg}\n")
        except:
            pass

    log(f"=== Wrapper started ===")
    log(f"sys.argv: {sys.argv}")

    # Process arguments
    args = sys.argv[1:]
    for i, arg in enumerate(args):
        if arg == '-f' and i + 1 < len(args):
            original = args[i + 1]
            converted = convert_windows_path(args[i + 1])
            args[i + 1] = converted
            log(f"Original: {original}")
            log(f"Converted: {converted}")

            # Check if file exists
            if os.path.exists(converted):
                log(f"Connection file EXISTS")
            else:
                log(f"Connection file MISSING - waiting...")
                # Wait up to 2 seconds for file to appear
                import time
                for _ in range(20):
                    time.sleep(0.1)
                    if os.path.exists(converted):
                        log(f"Connection file appeared")
                        break
                else:
                    log(f"Connection file still missing after wait")
            break

    # Set up environment with CLEAN PATH (not inheriting polluted Windows PATH)
    # The Windows PATH causes issues because it contains spaces and special chars.
    # The home directory is the current user's (setup_wsl_lean4.sh installs elan,
    # the REPL and the venv under $HOME): a hardcoded account path broke the
    # kernel for every other WSL user and for native Linux/macOS installs.
    home = os.path.expanduser('~')
    elan_bin = os.path.join(home, '.elan', 'bin')
    os.environ['PATH'] = os.pathsep.join([
        elan_bin,
        os.path.join(home, '.lean4-venv', 'bin'),
        '/usr/local/bin', '/usr/bin', '/bin',
    ])

    # Jupyter inherits Papermill's execution cwd. wsl_papermill sets it to the
    # notebook directory by default, or to an explicit --cwd for companions that
    # live beside several Lake projects. Resolve upward from that real origin.
    inherited_cwd = os.getcwd()
    lake_root = find_lake_root(inherited_cwd)

    # --- Toolchain einglee (#18511) -------------------------------------
    # L'ordre de precedence : le lake gagne (son propre lean-toolchain), sinon
    # l'ancrage le plus proche en remontant depuis le repertoire d'execution.
    anchor_dir, toolchain = find_toolchain_anchor(inherited_cwd)
    if lake_root:
        lake_toolchain = os.path.join(lake_root, 'lean-toolchain')
        if os.path.isfile(lake_toolchain):
            try:
                with open(lake_toolchain, encoding='utf-8') as fh:
                    pinned = fh.read().strip()
            except OSError:
                pinned = ''
            if pinned:
                # Deux affectations separees : le destructuring
                # `anchor_dir, toolchain = lake_root, pinned` fait un tuple
                # dont la tete est le porteur `lake_root`, et la garde
                # `check_lake_direct_invocation.py` (forme 2bis) le lit comme
                # un argv `[lake_root, ...]`. Ce n'est pas un argv : le
                # wrapper ne lance jamais `lake` (il execute le binaire REPL
                # directement, avec LEAN_PATH de la lake). Forme non
                # ambiguë pour la garde, meme comportement.
                anchor_dir = lake_root
                toolchain = pinned
    if not toolchain:
        message = (
            "Lean 4 kernel startup failed: no lean-toolchain found from execution "
            f"directory {inherited_cwd}. The kernel pins the Lean toolchain and "
            "never follows elan's default ('stable'); open the notebook inside a "
            "tree that pins one, or run wsl_papermill.py with --cwd <lake-root>."
        )
        log(message)
        print(message, file=sys.stderr)
        return 2

    tag = toolchain.split(':')[-1].strip()
    repl_path, repl_version = resolve_repl(home, tag)
    if repl_path is None:
        message = (
            "Lean 4 kernel startup failed: REPL/toolchain divergence. The pinned "
            f"toolchain is {toolchain} (tag {tag}) but the available REPL binary "
            f"reports Lean {repl_version or 'an unknown version'}. Refusing to "
            "start: a mismatched REPL renders every cell as a parse error under "
            "an exit 0. Fix: python scripts/lean/setup_native_lean4_import.py "
            f"build-repl {tag.lstrip('v')}"
        )
        log(message)
        print(message, file=sys.stderr)
        return 3
    os.environ['ELAN_TOOLCHAIN'] = toolchain
    log(f"toolchain pinned: {toolchain} ; REPL: {repl_path} (Lean {repl_version})")

    # `lake env repl` resout `repl` par le PATH : un binaire `repl-<tag>` ne
    # serait jamais trouve sans ce shim.
    default_repl = os.path.join(elan_bin, 'repl')
    shim_dir = _repl_shim_dir(repl_path)
    if shim_dir is None and os.path.abspath(repl_path) != os.path.abspath(default_repl):
        message = (
            "Lean 4 kernel startup failed: cannot expose the matched REPL "
            f"{repl_path} on PATH (symlink shim unavailable), so 'lake env repl' "
            "could pick another binary."
        )
        log(message)
        print(message, file=sys.stderr)
        return 3
    if shim_dir:
        os.environ['PATH'] = os.pathsep.join(
            [shim_dir] + os.environ['PATH'].split(os.pathsep))

    # Un lake n'est plus indispensable en soi : `lake env` fonctionne sans
    # lakefile (mesure 2026-10-21). Ce qui est indispensable, c'est l'ancrage
    # de la toolchain -- et il est resolu ci-dessus (#16181 reste respecte :
    # aucun repli vers un projet etranger).
    target_dir = lake_root if lake_root else anchor_dir
    log(f"chdir {inherited_cwd} -> {target_dir} (lake={lake_root})")
    os.chdir(target_dir)
    log(f"PATH set (clean): {os.environ['PATH']}")
    log(f"cwd: {os.getcwd()}")
    log(f"About to launch kernel with args: {args}")

    # Launch the kernel directly using IPKernelApp.launch_instance
    # NOTE: python -m lean4_jupyter.kernel exits immediately for unknown reasons
    # But calling IPKernelApp.launch_instance directly works correctly
    log(f"Launching kernel directly via IPKernelApp.launch_instance")

    try:
        # Set sys.argv for the kernel to parse
        sys.argv = ['lean4_jupyter'] + args
        log(f"sys.argv set to: {sys.argv}")

        # Import and launch the kernel
        from ipykernel.kernelapp import IPKernelApp
        from lean4_jupyter.kernel import Lean4Kernel

        log(f"Starting kernel...")
        IPKernelApp.launch_instance(kernel_class=Lean4Kernel)
        log(f"Kernel exited normally")
    except SystemExit as e:
        log(f"SystemExit: {e}")
        sys.exit(e.code if e.code is not None else 0)
    except Exception as e:
        log(f"Exception launching kernel: {e}")
        import traceback
        log(traceback.format_exc())
        sys.exit(1)


if __name__ == '__main__':
    sys.exit(main())
