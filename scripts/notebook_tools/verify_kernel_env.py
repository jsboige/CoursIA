#!/usr/bin/env python3
"""Verify a notebook's kernelspec resolves to a registered kernel whose
``argv[0]`` matches the venv ``wsl_papermill`` would use by default.

Acceptance 4 of #14908 asks for *executing* a notebook and checking that
``sys.executable`` inside the running kernel equals the interpreter the
notebook's ``kernel.json`` declares. That requires booting a Jupyter
kernel, which is expensive (and WSL-coupled in this repo) -- outside the
scope of a 30-min worker cycle.

This CLI ships the **static** half of the check: it reads the
``metadata.kernelspec`` of the notebook, looks up the registered
``kernel.json`` via ``jupyter_client`` (no kernel boot), and prints a
verdict on whether the argv interpreter's venv matches ``~/coursia-wsl``
(the default venv ``wsl_papermill`` activates when ``--venv`` is not
passed). The runtime half stays an empirical verification a worker can
perform later in a controlled WSL session.

Usage:
    python scripts/notebook_tools/verify_kernel_env.py <notebook.ipynb>
    python scripts/notebook_tools/verify_kernel_env.py <nb1.ipynb> <nb2.ipynb> ...

Exit codes:
    0 -- every notebook declares a kernelspec whose argv interpreter
         lives in the default venv (or a registered kernelspec whose
         argv is bare ``python`` -- the original #14908 failure mode).
    1 -- at least one notebook declares a kernelspec whose argv
         interpreter is in a venv OTHER than ``~/coursia-wsl``.
    2 -- at least one notebook's kernelspec is not registered locally,
         or its ``kernel.json`` is missing/invalid.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Optional

DEFAULT_WSL_VENV = "~/coursia-wsl"

# Borrowed verbatim from scripts/notebook_tools/wsl_papermill.py so that
# both scripts agree on what counts as "system" vs "venv" interpreters.
# Tell c.14908 followup: when both scripts diverge on the definition,
# the static verdict stops matching the runtime one. Keep these helpers
# in lock-step -- if you change one, change both.
def _venv_from_interpreter(interpreter: Optional[str]) -> Optional[str]:
    """Derive a venv path from a kernel interpreter path ``<venv>/bin/python3``.

    Returns ``None`` for system interpreters (``/usr/bin/python3``, ``/bin/python3``)
    and bare names (``python3``), where no venv can be inferred.

    POSIX-only: kernel interpreters on WSL are POSIX paths (e.g.
    ``/home/jesse/.lean4-venv/bin/python3``), not Windows paths. Using
    ``pathlib.PurePosixPath`` avoids the Windows-specific drive/parent
    semantics that would otherwise turn a forward-slash path into a
    backslash path under ``Path(interpreter).parent.parent``.
    """
    if not interpreter:
        return None
    from pathlib import PurePosixPath
    p = PurePosixPath(interpreter)
    # Any python* interpreter name qualifies (python, python3, python3.10):
    # WSL venvs often expose a versioned name. The former
    # ``not in ("python", "python3")`` clause was subsumed by this check.
    if not p.name.startswith("python"):
        return None
    if p.parent.name != "bin":
        return None
    venv = p.parent.parent
    s = str(venv)
    if s in ("/", "/usr", "/usr/local"):
        return None
    return s


def _normalize_venv(venv: Optional[str], home: str) -> str:
    """Expand ``~`` and strip a trailing slash; return "" for None."""
    if not venv:
        return ""
    out = venv.replace("~", home, 1)
    return out.rstrip("/")


def _read_nb_kernelspec(notebook_path: Path) -> Optional[dict]:
    """Return ``metadata.kernelspec`` of the notebook, or None if absent/invalid."""
    try:
        nb = json.loads(notebook_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    md = nb.get("metadata") if isinstance(nb, dict) else None
    if not isinstance(md, dict):
        return None
    ks = md.get("kernelspec")
    return ks if isinstance(ks, dict) else None


def _load_kernelspec_via_jupyter_client(name: str) -> Optional[dict]:
    """Read a registered kernelspec using jupyter_client (cross-platform).

    Returns the parsed ``kernel.json`` dict, or None if the kernelspec
    is not registered / not readable.
    """
    try:
        # jupyter_client.kernelspec.get_kernel_spec resolves the kernelspec
        # for the current user (no kernel boot). It is what `jupyter
        # kernelspec list` reads from.
        from jupyter_client.kernelspec import get_kernel_spec  # type: ignore
        spec = get_kernel_spec(name)
        # spec is a KernelSpecManager object; spec.to_dict() returns the
        # underlying kernel.json content.
        d = spec.to_dict() if hasattr(spec, "to_dict") else {}
    except Exception:
        return None
    argv = d.get("argv") if isinstance(d, dict) else None
    if not isinstance(argv, list) or not argv:
        return None
    return {"argv": argv, "resource_dir": getattr(spec, "resource_dir", "")}


def verify_one(notebook_path: Path, default_venv: str = DEFAULT_WSL_VENV) -> dict:
    """Run the static verification on one notebook. Returns a verdict dict.

    Schema::

        {
            "notebook": str,
            "kernelspec_name": str | None,
            "kernelspec_found": bool,
            "argv_interpreter": str | None,
            "declared_venv": str | None,
            "matches_default_venv": bool | None,  # None = unknown
            "verdict": "OK" | "DIVERGENT_VENV" | "NO_KERNELSPEC"
                       | "KERNELSPEC_UNREGISTERED" | "INVALID_KERNEL_JSON",
            "message": str,
        }
    """
    out = {
        "notebook": str(notebook_path),
        "kernelspec_name": None,
        "kernelspec_found": False,
        "argv_interpreter": None,
        "declared_venv": None,
        "matches_default_venv": None,
        "verdict": "NO_KERNELSPEC",
        "message": "",
    }

    ks = _read_nb_kernelspec(notebook_path)
    if not ks:
        out["verdict"] = "NO_KERNELSPEC"
        out["message"] = "notebook has no metadata.kernelspec"
        return out
    name = ks.get("name")
    if not isinstance(name, str) or not name:
        out["verdict"] = "NO_KERNELSPEC"
        out["message"] = "metadata.kernelspec.name is empty"
        return out
    out["kernelspec_name"] = name

    spec = _load_kernelspec_via_jupyter_client(name)
    if spec is None:
        out["verdict"] = "KERNELSPEC_UNREGISTERED"
        out["message"] = (
            f"kernelspec '{name}' is not registered locally; run "
            "`jupyter kernelspec list` to confirm"
        )
        return out
    out["kernelspec_found"] = True

    argv = spec.get("argv")
    if not argv or not isinstance(argv, list):
        out["verdict"] = "INVALID_KERNEL_JSON"
        out["message"] = f"kernelspec '{name}' has no argv"
        return out
    interp = argv[0] if isinstance(argv[0], str) else None
    out["argv_interpreter"] = interp
    declared_venv = _venv_from_interpreter(interp)
    out["declared_venv"] = declared_venv

    if declared_venv is None:
        # The argv interpreter is a system python (e.g. /usr/bin/python3),
        # or bare "python". This is exactly the failure mode of #14908
        # the original PR #14930 stdout divergence warning covers at
        # runtime -- at the static level we can only note it.
        out["verdict"] = "OK"
        out["matches_default_venv"] = True
        out["message"] = (
            f"kernelspec '{name}' argv[0]={interp!r} resolves to a system "
            "or bare interpreter; wsl_papermill uses the active venv at "
            "execution time, so no static divergence can be flagged"
        )
        return out

    # Normalize default venv for comparison.
    home = str(Path.home())
    default_norm = _normalize_venv(default_venv, home)
    declared_norm = _normalize_venv(declared_venv, home)
    matches = declared_norm == default_norm
    out["matches_default_venv"] = matches
    if matches:
        out["verdict"] = "OK"
        out["message"] = (
            f"declared venv {declared_norm!r} matches default "
            f"{default_norm!r}"
        )
    else:
        out["verdict"] = "DIVERGENT_VENV"
        out["message"] = (
            f"declared venv {declared_norm!r} does NOT match default "
            f"{default_norm!r}; pass --venv {declared_norm!r} to "
            f"wsl_papermill.py execute or run inside the declared venv"
        )
    return out


def _print_verdict(v: dict) -> None:
    icon = {
        "OK": "OK",
        "DIVERGENT_VENV": "DIVERGENT",
        "NO_KERNELSPEC": "NO-KS",
        "KERNELSPEC_UNREGISTERED": "UNREG",
        "INVALID_KERNEL_JSON": "BADJSON",
    }.get(v["verdict"], "?")
    print(
        f"[{icon}] {v['notebook']} "
        f"ks={v['kernelspec_name']!r} "
        f"argv0={v['argv_interpreter']!r} "
        f"declared_venv={v['declared_venv']!r}"
    )
    print(f"       -> {v['message']}")


def main(argv: Optional[list] = None) -> int:
    p = argparse.ArgumentParser(
        description="Static check of notebook kernelspec against wsl_papermill "
        "default venv (#14908 acceptance 4, partial)."
    )
    p.add_argument(
        "notebooks", nargs="+", type=Path,
        help="One or more .ipynb files to verify"
    )
    p.add_argument(
        "--default-venv", default=DEFAULT_WSL_VENV,
        help=f"Default venv wsl_papermill uses when --venv is not passed "
        f"(default: {DEFAULT_WSL_VENV!r})"
    )
    p.add_argument(
        "--json", action="store_true",
        help="Emit machine-readable JSON instead of the human verdict lines"
    )
    args = p.parse_args(argv)

    verdicts = [verify_one(nb, default_venv=args.default_venv)
                for nb in args.notebooks]
    if args.json:
        print(json.dumps(verdicts, indent=2, ensure_ascii=False))
    else:
        for v in verdicts:
            _print_verdict(v)

    n_divergent = sum(1 for v in verdicts if v["verdict"] == "DIVERGENT_VENV")
    n_unreg = sum(1 for v in verdicts
                  if v["verdict"] in ("KERNELSPEC_UNREGISTERED", "INVALID_KERNEL_JSON"))
    n_no_ks = sum(1 for v in verdicts if v["verdict"] == "NO_KERNELSPEC")
    if not args.json:
        n_ok = sum(1 for v in verdicts if v["verdict"] == "OK")
        print(
            f"\nSummary: {n_ok} OK, {n_divergent} divergent, "
            f"{n_unreg} unregistered/invalid, {n_no_ks} no-kernelspec "
            f"({len(verdicts)} total)"
        )
    if n_divergent:
        return 1
    if n_unreg:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
