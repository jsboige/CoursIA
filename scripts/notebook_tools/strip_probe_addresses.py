#!/usr/bin/env python3
"""Strip the .NET Interactive `probeAddresses` HTTP-bootstrap banner from notebooks.

The .NET Interactive kernel (`dotnet-interactive`) injects a JavaScript
HTTP-bootstrap script — `probeAddresses(...)` / `loadDotnetInteractiveApi()` —
as a `text/html` `display_data` output on the **first executed code cell** of
every C#/F#/PowerShell notebook. That script embeds the worker's **full host
network interface list**, including LAN IPv4 (192.168.x.x), WSL/Docker bridges
(172.x.x.x), link-local IPv6 (fe80::) and the host's **public globally-routable
IPv6** (e.g. `2a01:e0a:...`). On a public repository this leaks the maintainer's
real internet-facing addresses (ISP + geo, potentially reachable).

The banner is **dead noise** in a static notebook — it only acts inside a live
kernel session — so it has zero pedagogical value and is safe to remove. The
strip is **output-only**: no source cell is modified, `execution_count` is left
intact, and only the offending `display_data` output is dropped. This is the
exact shape of the manual scrub in #2733, but as a reusable, automatable tool.

This is the **durable fix** for the structural leak documented in #6309: the
prior scrub (#2733, 51 notebooks) was non-durable because the kernel re-injects
the banner on every first-execution, so every .NET notebook created or
re-executed since has re-acquired it (183 notebooks as of 2026-07-12). Wiring
this tool into the pre-commit hook (H.3) or a papermill post-processor makes the
leak un-committable. See #6309 for the kernel-flag investigation proving no
dotnet-interactive option suppresses the banner (`--http-local-only` binds the
listener to localhost but the JS still embeds every interface).

Usage:
    python strip_probe_addresses.py --scan                      # Report scope (no changes)
    python strip_probe_addresses.py --strip --path nb.ipynb      # Strip one notebook
    python strip_probe_addresses.py --strip                      # Strip all affected
    python strip_probe_addresses.py --strip --dry-run            # Show what would change
    python strip_probe_addresses.py --verify                     # Exit 1 if any banner remains

Exit codes:
    0 — No banner found (scan), or all strips applied successfully
    1 — Banner(s) still present (--verify), or parse error on a notebook
    2 — CLI / usage error

References: #2727 (original scrub, non-durable), #2733 (merge), #6309 (regression + durable fix).
"""

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

# Markers identifying the dotnet-interactive HTTP-bootstrap display_data output.
# A display_data output is the banner iff its text/html payload contains any of these.
BANNER_MARKERS = ("probeAddresses", "loadDotnetInteractiveApi", "probingAddresses")

# Network-address markers (used to score severity; a banner with these is a real IP leak).
IP_MARKERS = ("192.168.", "172.16.", "172.17.", "172.18.", "172.19.",
              "172.20.", "172.21.", "172.22.", "172.23.", "172.24.",
              "172.25.", "172.26.", "172.27.", "172.28.", "172.29.",
              "172.30.", "172.31.", "fe80::", "2a01:", "2a00:", "2001:")


def _is_banner_output(output: dict) -> bool:
    """True iff a single cell output is the probeAddresses bootstrap display_data."""
    if output.get("output_type") != "display_data":
        return False
    data = output.get("data", {})
    html = data.get("text/html", "")
    if isinstance(html, list):
        html = "".join(html)
    return any(marker in html for marker in BANNER_MARKERS)


def _has_ip_leak(output: dict) -> bool:
    """True iff the banner output embeds real host network addresses."""
    blob = json.dumps(output, ensure_ascii=False)
    return any(marker in blob for marker in IP_MARKERS)


def scan_notebook(nb_path: Path) -> dict:
    """Return banner locations + IP-leak flag for one notebook.

    Keys: path, banner_cells (list of cell idx), ip_leak (bool).
    """
    try:
        notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as e:
        return {"path": str(nb_path), "banner_cells": [], "ip_leak": False,
                "error": f"Cannot parse: {e}"}

    banner_cells = []
    ip_leak = False
    for i, cell in enumerate(notebook.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        for output in cell.get("outputs", []):
            if _is_banner_output(output):
                banner_cells.append(i)
                if _has_ip_leak(output):
                    ip_leak = True
    return {"path": str(nb_path), "banner_cells": banner_cells, "ip_leak": ip_leak}


def strip_notebook(nb_path: Path, dry_run: bool = False) -> dict:
    """Strip the banner display_data outputs from one notebook in place.

    Returns dict: path, stripped_cells (list), ip_leak (bool), written (bool).
    Source cells and execution_count are NEVER modified — output-only strip.
    """
    info = scan_notebook(nb_path)
    if not info["banner_cells"]:
        return {**info, "stripped_cells": [], "written": False}

    notebook = json.loads(nb_path.read_text(encoding="utf-8"))
    stripped = []
    for i in info["banner_cells"]:
        cell = notebook["cells"][i]
        before = len(cell.get("outputs", []))
        cell["outputs"] = [o for o in cell.get("outputs", []) if not _is_banner_output(o)]
        removed = before - len(cell["outputs"])
        if removed:
            stripped.append(i)

    if dry_run:
        return {**info, "stripped_cells": stripped, "written": False}

    # Preserve nbformat sorting/indentation conventions.
    nbformat_minor = notebook.get("nbformat_minor", 5)
    nb_path.write_text(
        json.dumps(notebook, ensure_ascii=False, indent=1) + "\n",
        encoding="utf-8",
    )
    return {**info, "stripped_cells": stripped, "written": True}


def iter_notebooks():
    """Yield all tracked .ipynb notebooks under NOTEBOOKS_DIR."""
    for nb_path in sorted(NOTEBOOKS_DIR.rglob("*.ipynb")):
        if any(part in {"_output", ".ipynb_checkpoints", "obj", "bin", "__pycache__"}
               for part in nb_path.parts):
            continue
        yield nb_path


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Strip the .NET Interactive probeAddresses banner from notebooks (#6309).",
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--scan", action="store_true",
                      help="Report scope (notebooks carrying the banner) without changes.")
    mode.add_argument("--strip", action="store_true",
                      help="Strip the banner display_data outputs (output-only).")
    mode.add_argument("--verify", action="store_true",
                      help="Exit 1 if any banner remains (for CI / pre-commit gate).")
    parser.add_argument("--path", type=str, default=None,
                        help="Operate on a single notebook path instead of all.")
    parser.add_argument("--dry-run", action="store_true",
                        help="With --strip: show what would change without writing.")
    args = parser.parse_args()

    targets = [Path(args.path)] if args.path else list(iter_notebooks())

    if args.scan:
        affected = []
        ip_leak_count = 0
        for nb in targets:
            if not nb.exists():
                continue
            info = scan_notebook(nb)
            if info["banner_cells"]:
                affected.append(info)
                if info["ip_leak"]:
                    ip_leak_count += 1
        print(f"Notebooks carrying the probeAddresses banner: {len(affected)}")
        print(f"  with host network addresses (IP leak): {ip_leak_count}")
        if affected:
            print("\nAffected notebooks:")
            for info in affected:
                tag = " [IP-LEAK]" if info["ip_leak"] else ""
                print(f"  {info['path']}{tag}")
        return 0

    if args.verify:
        remaining = 0
        for nb in targets:
            if not nb.exists():
                continue
            info = scan_notebook(nb)
            if info["banner_cells"]:
                remaining += 1
                print(f"  BANNER REMAINS: {info['path']} (cells {info['banner_cells']})")
        if remaining:
            print(f"\n{remaining} notebook(s) still carry the banner. "
                  f"Run `strip_probe_addresses.py --strip` to remove.")
            return 1
        print("No probeAddresses banner found in any checked notebook.")
        return 0

    if args.strip:
        stripped_count = 0
        for nb in targets:
            if not nb.exists():
                print(f"  SKIP (not found): {nb}")
                continue
            result = strip_notebook(nb, dry_run=args.dry_run)
            if result["stripped_cells"]:
                action = "would strip" if args.dry_run else "stripped"
                tag = " [IP-LEAK]" if result["ip_leak"] else ""
                print(f"  {action}: {nb}{tag} (cells {result['stripped_cells']})")
                stripped_count += 1
        verb = "would be stripped" if args.dry_run else "stripped"
        print(f"\n{stripped_count} notebook(s) {verb}.")
        return 0

    return 2


if __name__ == "__main__":
    sys.exit(main())
