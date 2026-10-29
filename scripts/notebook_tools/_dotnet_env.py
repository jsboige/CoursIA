"""DOTNET_ROOT repair for .NET Interactive kernel launches (#17361).

``#r "nuget: ..."`` restores shell out to ``dotnet restore`` through the
``DOTNET_ROOT`` host (``FSharp.DependencyManager.Nuget``). A root that ships
runtimes but no ``sdk/`` cannot restore at all: the kernel surfaces
``PackageRestoreResult..ctor`` ("Must provide errors when succeeded is false")
and nothing reaches the NuGet cache. A warm global cache hides the defect --
the restore short-circuits -- so the failure reads as package-dependent and
intermittent (#17361; measured 2026-09-28 on myia-po-2027: a never-cached
package fails on the runtime-only root and succeeds as soon as an SDK-bearing
root has populated the cache).

Leaf module on purpose: both ``dotnet_executor.py`` (which imports
``notebook_helpers``) and ``notebook_helpers.py`` need it, so it must not
import either.
"""
import os
import shutil
from pathlib import Path


def has_sdk(root):
    """True when ``root`` holds a non-empty ``sdk`` directory."""
    sdk_dir = Path(root) / "sdk"
    try:
        return sdk_dir.is_dir() and next(iter(sdk_dir.iterdir()), None) is not None
    except OSError:
        return False


def sdk_root_candidates():
    """Roots worth probing for an SDK: the ``dotnet`` on PATH first (it is the
    one the CLI itself uses), then the per-user install location, then the
    platform default install locations.

    The per-user root is ``dotnet-install``'s default ``-InstallDir``. It is
    neither the ``dotnet`` on PATH nor the ProgramFiles install, so a list
    built from those two alone can never repair such an installation --
    measured 2026-10-29 on myia-po-2028, where it is the *only* root carrying
    an SDK (8.0.426 / 9.0.319 / 10.0.402) while ``C:\\Program Files\\dotnet``
    ships runtimes only.
    """
    candidates = []
    dotnet_on_path = shutil.which("dotnet")
    if dotnet_on_path:
        candidates.append(str(Path(dotnet_on_path).resolve().parent))
    if os.name == "nt":
        local_appdata = os.environ.get("LOCALAPPDATA")
        if local_appdata:
            candidates.append(str(Path(local_appdata) / "Microsoft" / "dotnet"))
        program_files = os.environ.get("ProgramFiles", r"C:\Program Files")
        candidates.append(str(Path(program_files) / "dotnet"))
    else:
        candidates.extend(("/usr/share/dotnet", "/usr/local/share/dotnet"))
    # A repeated candidate buys a second probe and nothing else. The usual
    # source is a host whose ``dotnet`` on PATH *is* the ProgramFiles install:
    # the list read ``['C:\\Program Files\\dotnet', 'C:\\Program Files\\dotnet']``
    # on 2026-10-29.
    seen, unique = set(), []
    for candidate in candidates:
        key = os.path.normcase(os.path.normpath(candidate))
        if key not in seen:
            seen.add(key)
            unique.append(candidate)
    return unique


def effective_root():
    """The root the host would actually resolve for this process.

    ``DOTNET_ROOT`` when set and non-empty. Otherwise the directory holding the
    ``dotnet`` on PATH: with the variable unset the host resolves its runtime
    relative to its own location, so that directory *is* the effective root and
    it must be judged like any other. ``None`` when neither is knowable.
    """
    configured = os.environ.get("DOTNET_ROOT")
    if configured:
        return configured
    dotnet_on_path = shutil.which("dotnet")
    if dotnet_on_path:
        return str(Path(dotnet_on_path).resolve().parent)
    return None


def sdk_bearing_dotnet_root():
    """Return a ``DOTNET_ROOT`` carrying an SDK, or ``None`` when unneeded.

    Returns the repaired root only when the effective one lacks an SDK and a
    valid alternative is discoverable, ``None`` otherwise. Callers pass it to
    ``KernelManager.start_kernel(env=...)`` -- only the kernel subprocess env
    is concerned, the machine-level variable is never written.

    An unset or empty ``DOTNET_ROOT`` is *not* a reason to stand down: the host
    then resolves itself, and a self-resolution onto a runtime-only root fails
    the restore exactly as a configured one does (#17361). Standing down there
    was the defect measured on myia-po-2028.
    """
    root = effective_root()
    if root is None or has_sdk(root):
        return None
    for candidate in sdk_root_candidates():
        if has_sdk(candidate):
            return candidate
    return None