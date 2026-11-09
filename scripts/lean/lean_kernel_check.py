#!/usr/bin/env python3
"""Canonical kernel.json wrapper check for the lean4-wsl Jupyter kernel.

Single source of truth for detecting the 2026-05-27 regression (issue #1618)
where ``kernel.json`` pointed to the OLD bash wrapper
``~/lean4-jupyter-wrapper.sh`` instead of the CORRECT Python wrapper
``~/.lean4-kernel-wrapper.py`` (v5). The bash wrapper lacks Windows->WSL path
conversion and NTFS permission handling, so the kernel times out at startup.

Before this module the same check lived (divergently) in three places:
  - scripts/lean/setup_lean4_all.py            (check_wrapper_registration)
  - SymbolicAI/Lean/scripts/validate_lean_setup.py (check_kernel_wrapper)
  - GameTheory/scripts/validate_lean_setup.py  (was MISSING entirely)

``inspect_kernel_wrapper`` is print-agnostic: it returns a structured result so
each caller can format it with its own style (unicode / ASCII / section header).

Usage as a module:
    from lean_kernel_check import inspect_kernel_wrapper
    status, message = inspect_kernel_wrapper("lean4-wsl")

Usage as a CLI:
    python scripts/lean/lean_kernel_check.py            # check lean4-wsl
    python scripts/lean/lean_kernel_check.py --kernel lean4-wsl
"""

import argparse
import json
import os
import sys
from pathlib import Path

OLD_BASH_WRAPPER = "lean4-jupyter-wrapper.sh"
CORRECT_PY_WRAPPER = ".lean4-kernel-wrapper.py"

# Repo reference copy of the wrapper -- the canonical source (#13180). The
# deployed copy (WSL ~/.lean4-kernel-wrapper.py) is a SYNC TARGET; nothing in
# the repo deploys or overwrites it, so the two can drift silently.
REPO_WRAPPER_REFERENCE = (
    Path(__file__).resolve().parent.parent.parent
    / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "scripts"
    / "lean4-kernel-wrapper.py"
)


def windows_kernel_json_candidates(kernel_name="lean4-wsl",
                                   windows_users_root="/mnt/c/Users"):
    """Return the Windows-side kernel.json locations, from EITHER side.

    The kernel that Jupyter actually drives is registered on the Windows side
    (``%APPDATA%/jupyter/kernels/<name>/kernel.json``); the WSL-side Jupyter
    registers its own copy under ``~/.local/share/jupyter``.  When the
    validator runs INSIDE WSL (``--wsl``), ``%APPDATA%`` is not exported, so
    the Windows registration was invisible and the check reported "aucun
    kernel.json trouve" for a kernel that WAS registered (issue #21614,
    defect 3).

    From inside WSL the Windows profile is reachable under
    ``/mnt/c/Users/<user>/AppData/Roaming``; that path is what this function
    probes, so the check works on both sides without an interop call.
    """
    candidates = []
    appdata = os.environ.get("APPDATA")
    if appdata:
        candidates.append(Path(appdata) / "jupyter" / "kernels" / kernel_name / "kernel.json")
    root = Path(windows_users_root)
    if root.is_dir():
        for profile in sorted(root.iterdir()):
            if not profile.is_dir():
                continue
            candidates.append(
                profile / "AppData" / "Roaming" / "jupyter" / "kernels"
                / kernel_name / "kernel.json"
            )
    return candidates


def _safe_exists(path) -> bool:
    """True si le chemin existe -- sans lever sur un profil inaccessible.

    Depuis WSL, le probe `/mnt/c/Users/<profil>/...` rencontre des profils
    Windows que l'utilisateur WSL ne peut pas statuer (`DefaultAppPool` par
    exemple) : `Path.exists()` leve alors `PermissionError` au lieu de
    renvoyer False, et le validateur meurt sur un chemin qui n'est meme pas
    le sien (mesure #21614, run WSL du 2026-10-21).
    """
    try:
        return Path(path).exists()
    except OSError:
        return False


def candidate_kernel_json_paths(kernel_name="lean4-wsl"):
    """Return the kernel.json locations to probe, in priority order.

    Covers both the WSL-side install (~/.local/share/jupyter) and the
    Windows-side registration (%APPDATA%/jupyter, or /mnt/c/Users/<u>/
    AppData/Roaming when running inside WSL -- issue #21614).
    """
    candidates = [
        Path.home() / ".local" / "share" / "jupyter" / "kernels" / kernel_name / "kernel.json",
    ]
    candidates.extend(windows_kernel_json_candidates(kernel_name))
    return candidates


def inspect_kernel_wrapper(kernel_name="lean4-wsl", kernel_json_path=None):
    """Inspect kernel.json and classify the wrapper it points to.

    Returns a ``(status, message)`` tuple where ``status`` is one of:
      - "ok"      : kernel.json points to the correct Python wrapper (v5)
      - "error"   : kernel.json points to the old bash wrapper (regression #1618)
      - "warning" : kernel.json not found, unreadable, or unknown argv

    ``kernel_json_path`` overrides the auto-detected location (used by tests).
    """
    if kernel_json_path is not None:
        kernel_json = Path(kernel_json_path)
        candidates = [kernel_json]
    else:
        candidates = candidate_kernel_json_paths(kernel_name)
        kernel_json = next((p for p in candidates if _safe_exists(p)), None)

    if kernel_json is None or not _safe_exists(kernel_json):
        probed = [str(p) for p in candidates]
        return ("warning", f"kernel.json: aucun ({kernel_name}) trouve dans {probed}")

    try:
        with open(kernel_json, "r", encoding="utf-8") as f:
            spec = json.load(f)
        argv = " ".join(str(a) for a in spec.get("argv", []))
    except Exception as exc:  # noqa: BLE001 - report any read/parse failure as a warning
        return ("warning", f"kernel.json ({kernel_name}): erreur lecture ({exc})")

    if OLD_BASH_WRAPPER in argv:
        return (
            "error",
            f"kernel.json ({kernel_name}): pointe vers l'ancien wrapper bash "
            f"({OLD_BASH_WRAPPER}) — regression #1618. Re-executer "
            "`python scripts/lean/setup_lean4_all.py --register` pour pointer "
            f"vers ~/{CORRECT_PY_WRAPPER} (v5).",
        )
    if CORRECT_PY_WRAPPER in argv:
        return ("ok", f"kernel.json ({kernel_name}): wrapper Python v5 correct")
    return ("warning", f"kernel.json ({kernel_name}): wrapper inconnu — argv={argv[:120]}")


def wsl_to_unc(wsl_path: str, distro: str) -> Path:
    """/home/j/x.py + Ubuntu -> \\\\wsl$\\Ubuntu\\home/j/x.py (Windows-readable)."""
    return Path(r"\\wsl$" + "\\" + distro + wsl_path.replace("/", "\\"))


def _load_argv(kernel_json: Path):
    with open(kernel_json, "r", encoding="utf-8") as f:
        spec = json.load(f)
    return [str(a) for a in spec.get("argv", [])]


def kernel_drives_wsl(kernel_name="lean4-wsl", kernel_json_path=None):
    """True si le kernel.json enregistre pilote la chaine Lean a travers WSL.

    Sur un poste installe en WSL, le kernel ``lean4-wsl`` est enregistre
    COTE WINDOWS mais son argv appelle ``wsl.exe`` : la chaine elan/lean/
    lake n'existe donc que dans la distro. C'est le marqueur qui permet au
    validateur de ne pas compter les binaires Windows comme des composants
    manquants (issue #21614, defaut 2).

    Renvoie False si aucun kernel.json n'est trouve ou illisible.
    """
    if kernel_json_path is not None:
        kernel_json = Path(kernel_json_path)
        candidates = [kernel_json]
    else:
        candidates = candidate_kernel_json_paths(kernel_name)
    kernel_json = next((p for p in candidates if _safe_exists(p)), None)
    if kernel_json is None:
        return False
    try:
        with open(kernel_json, "r", encoding="utf-8") as f:
            spec = json.load(f)
        argv = " ".join(str(a) for a in spec.get("argv", []))
    except Exception:  # noqa: BLE001 - un kernel.json illisible ne prouve rien
        return False
    return "wsl" in argv.lower()


def inspect_wrapper_content_drift(kernel_json_path, repo_reference=None):
    """Compare the DEPLOYED wrapper content against the repo reference copy (#13180).

    Returns ``(status, message)``:
      - "ok"      : deployed byte-identical to the repo reference
      - "warning" : drift detected, or either side unreadable (WSL down, CI, ...)

    Never "error": a machine-local hotfix on the deployed copy is legal -- the
    guard makes the drift VISIBLE, it does not block (same posture as the
    dead_scope signal, #12740).
    """
    repo_ref = Path(repo_reference) if repo_reference else REPO_WRAPPER_REFERENCE
    kj = Path(kernel_json_path)
    if not kj.is_file():
        return ("warning", "kernel.json absent — drift non vérifiable")
    if not repo_ref.is_file():
        return ("warning", f"copie repo de référence introuvable: {repo_ref}")

    try:
        argv = _load_argv(kj)
    except (OSError, ValueError):
        return ("warning", f"kernel.json illisible: {kj}")

    wrapper_arg = next(
        (a for a in argv if a.endswith(CORRECT_PY_WRAPPER)), None)
    if wrapper_arg is None:
        return ("warning", "argv sans wrapper déployé — drift non vérifiable")

    if wrapper_arg.startswith("/") and "wsl" in " ".join(argv).lower():
        distro = "Ubuntu"
        for i, a in enumerate(argv[:-1]):
            if a == "-d" and argv[i + 1] and not argv[i + 1].startswith("-"):
                distro = argv[i + 1]
                break
        deployed = wsl_to_unc(wrapper_arg, distro)
    else:
        deployed = Path(wrapper_arg)

    try:
        deployed_bytes = deployed.read_bytes()
    except OSError:
        return ("warning", f"copie déployée illisible ({deployed}) — drift non vérifiable")
    repo_bytes = repo_ref.read_bytes()
    if deployed_bytes == repo_bytes:
        return ("ok", f"wrapper déployé = repo canonique ({len(repo_bytes)} octets, {repo_ref.name})")

    deployed_lines = deployed_bytes.count(b"\n")
    repo_lines = repo_bytes.count(b"\n")
    return (
        "warning",
        f"DRIFT wrapper #13180: déployé {len(deployed_bytes)} o / {deployed_lines} lignes "
        f"≠ repo {len(repo_bytes)} o / {repo_lines} lignes — re-sync depuis {repo_ref} "
        f"(cf issue #13180, procédure §wrapper-sync docs/reference/wsl-kernels-detail.md)",
    )


def main():
    parser = argparse.ArgumentParser(
        description="Verifie que kernel.json pointe vers le bon wrapper Lean 4 (issue #1618)."
    )
    parser.add_argument("--kernel", default="lean4-wsl", help="Nom du kernel (defaut: lean4-wsl)")
    args = parser.parse_args()

    status, message = inspect_kernel_wrapper(args.kernel)
    prefix = {"ok": "OK:", "error": "ERROR:", "warning": "WARNING:"}[status]
    print(f"{prefix} {message}")

    # Content drift is advisory: visible, never blocking (#13180).
    if status == "ok":
        candidates = candidate_kernel_json_paths(args.kernel)
        kj = next((p for p in candidates if _safe_exists(p)), None)
        if kj is not None:
            drift_status, drift_message = inspect_wrapper_content_drift(kj)
            d_prefix = {"ok": "OK:", "warning": "WARNING:"}[drift_status]
            print(f"{d_prefix} {drift_message}")

    sys.exit(0 if status == "ok" else 1)


if __name__ == "__main__":
    main()
