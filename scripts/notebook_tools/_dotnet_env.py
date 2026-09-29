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
    one the CLI itself uses), then the platform default install locations."""
    candidates = []
    dotnet_on_path = shutil.which("dotnet")
    if dotnet_on_path:
        candidates.append(str(Path(dotnet_on_path).resolve().parent))
    if os.name == "nt":
        program_files = os.environ.get("ProgramFiles", r"C:\Program Files")
        candidates.append(str(Path(program_files) / "dotnet"))
    else:
        candidates.extend(("/usr/share/dotnet", "/usr/local/share/dotnet"))
    return candidates


def sdk_bearing_dotnet_root():
    """Return a ``DOTNET_ROOT`` carrying an SDK, or ``None`` when unneeded.

    Returns the repaired root only when the configured one lacks an SDK and a
    valid alternative is discoverable, ``None`` otherwise. Callers pass it to
    ``KernelManager.start_kernel(env=...)`` -- only the kernel subprocess env
    is concerned, the machine-level variable is never written.
    """
    configured = os.environ.get("DOTNET_ROOT")
    if not configured or has_sdk(configured):
        return None
    for candidate in sdk_root_candidates():
        if has_sdk(candidate):
            return candidate
    return None