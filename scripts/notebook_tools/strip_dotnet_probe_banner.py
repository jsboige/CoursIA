#!/usr/bin/env python3
"""Durable fixer for the dotnet-interactive `probeAddresses` banner leak (issue #6309).

Background
----------
`.NET Interactive` (dotnet-interactive kernel) injects a `probeAddresses`
HTTP-bootstrap script as a `display_data` output (text/html) on the first
executed code cell of every .NET notebook. That script embeds the worker's full
network interface list (LAN IPv4 192.168.x, WSL/Docker 172.x, link-local IPv6
fe80::, and the host's public globally-routable IPv6 2a01:e0a:...). On a public
repo this leaks the maintainer's real internet-facing host addresses.

The banner is kernel-injected infrastructure noise (a JS bootstrap that only
acts inside a live kernel session) with ZERO pedagogical value. It is NOT a
cell's real execution output (stdout/stderr/figures/errors stay intact).

This is the DURABLE companion to the non-durable manual scrub #2733 (which
cleaned 51 notebooks by hand but the kernel re-injected on every re-exec).
No dotnet-interactive flag suppresses it (--http-local-only binds the listener
but the JS probe still enumerates all interfaces client-side; verified firsthand
po-2024, see #6309 comment). So the fix MUST be output-side, automated at the
commit gate.

What this script does
---------------------
For each .ipynb, removes any `display_data` output whose `data` dict contains
one of the banner markers (`probeAddresses`, `probingAddresses`,
`loadDotnetInteractiveApi`). Surgical:
  - source: untouched
  - execution_count: untouched
  - stream / execute_result / error / other display_data outputs: untouched
  - only the kernel-injected banner display_data is removed

This is output-normalization of kernel infrastructure leakage (same class as
the `metadata.papermill.input/output_path` -> basename exception in
secrets-hygiene rule 6), NOT a scrub of real execution proof. Precedent:
#2733 (merged 2026-06-09, output-only scrub of this exact banner).

Usage
-----
  python strip_dotnet_probe_banner.py --check [path]   # report only, exit 1 if any leak
  python strip_dotnet_probe_banner.py --fix   [path]   # strip banners in place
  python strip_dotnet_probe_banner.py --check MyIA.AI.Notebooks/GameTheory/foo.ipynb

Exit codes: 0 = clean (or fixed), 1 = leaks found (--check) / fix errors.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

BANNER_MARKERS = ("probeAddresses", "probingAddresses", "loadDotnetInteractiveApi")
IP_LEAK_RE = None  # imported lazily for the --check report


def _has_banner(output: dict) -> bool:
    """True if a single output object is the kernel-injected probe banner."""
    if output.get("output_type") != "display_data":
        return False
    data = output.get("data", {})
    # search all mime representations (text/html primarily, but be robust)
    blob = json.dumps(data, ensure_ascii=False)
    return any(marker in blob for marker in BANNER_MARKERS)


def _cell_leak_info(cell: dict) -> tuple[int, int]:
    """Return (n_banner_outputs, n_total_outputs) for a code cell."""
    outputs = cell.get("outputs", []) or []
    n_banner = sum(1 for o in outputs if _has_banner(o))
    return n_banner, len(outputs)


def _strip_cell(cell: dict) -> int:
    """Remove banner display_data outputs from a cell; return count removed."""
    outputs = cell.get("outputs", []) or []
    kept = [o for o in outputs if not _has_banner(o)]
    removed = len(outputs) - len(kept)
    if removed:
        cell["outputs"] = kept
    return removed


def _iter_notebooks(root: Path):
    for p in root.rglob("*.ipynb"):
        # skip vendored / archive / submodule noise
        parts = p.parts
        if any(seg in parts for seg in (
            ".lake", "_archive", "node_modules", ".git",
            "foundry-lib", "_peters",
        )):
            continue
        if "/.git/" in str(p):
            continue
        yield p


def _load(p: Path) -> tuple[dict | None, str | None]:
    """Return (notebook, raw_text). raw_text is None on parse error."""
    try:
        raw = p.read_text(encoding="utf-8")
        return json.loads(raw), raw
    except Exception as e:  # noqa: BLE001
        print(f"  ERROR parse {p}: {e}", file=sys.stderr)
        return None, None


def _detect_ensure_ascii(raw: str, nb: dict) -> bool:
    """Detect the original file's `ensure_ascii` setting so we preserve it.

    Re-serializing with the wrong setting churns the whole file (escaped
    è <-> raw UTF-8 è) instead of a surgical banner removal. Detection:
      - raw has non-ASCII bytes  -> original was ensure_ascii=False (raw UTF-8)
      - raw pure ASCII but content has non-ASCII chars -> ensure_ascii=True (escaped)
      - both ASCII -> either works; use False (repo standard, raw UTF-8)
    """
    try:
        raw.encode("ascii")
        raw_is_ascii = True
    except UnicodeEncodeError:
        raw_is_ascii = False
    if not raw_is_ascii:
        return False  # raw UTF-8
    # raw is ASCII: was it escaped? check if parsed content holds non-ASCII
    blob = json.dumps(nb, ensure_ascii=False)
    try:
        blob.encode("ascii")
        return False  # no non-ASCII anywhere
    except UnicodeEncodeError:
        return True  # content has non-ASCII but raw was ASCII -> was escaped


def _save(p: Path, nb: dict, raw: str) -> None:
    # LF, no BOM, indent=1 (nbformat convention used across this repo).
    # Preserve the original ensure_ascii setting (escaped vs raw UTF-8).
    ensure_ascii = _detect_ensure_ascii(raw, nb)
    data = json.dumps(nb, ensure_ascii=ensure_ascii, indent=1)
    # normalize newlines to LF
    data = data.replace("\r\n", "\n").replace("\r", "\n")
    p.write_bytes(data.encode("utf-8") + b"\n")


def run(root: Path, fix: bool) -> int:
    leaks = []  # (path, n_banner_cells, n_banner_outputs, had_real_ips)
    fixed = 0
    errors = 0
    for p in _iter_notebooks(root):
        nb, raw = _load(p)
        if nb is None:
            errors += 1
            continue
        banner_cells = 0
        banner_outputs = 0
        had_ips = False
        for c in nb.get("cells", []):
            if c.get("cell_type") != "code":
                continue
            n_banner, _n_total = _cell_leak_info(c)
            if n_banner:
                banner_cells += 1
                banner_outputs += n_banner
                # crude IP check on the banner blob for the report
                for o in c.get("outputs", []):
                    if _has_banner(o):
                        blob = json.dumps(o.get("data", {}), ensure_ascii=False)
                        if ("192.168." in blob or "fe80::" in blob
                                or "2a01:" in blob or "172." in blob):
                            had_ips = True
        if banner_outputs == 0:
            continue
        rel = p.relative_to(root)
        leaks.append((rel, banner_cells, banner_outputs, had_ips))
        if fix:
            try:
                removed = 0
                for c in nb.get("cells", []):
                    if c.get("cell_type") == "code":
                        removed += _strip_cell(c)
                if removed:
                    _save(p, nb, raw)
                    fixed += 1
            except Exception as e:  # noqa: BLE001
                print(f"  ERROR fix {p}: {e}", file=sys.stderr)
                errors += 1

    # report
    with_ips = sum(1 for _, _, _, h in leaks if h)
    print(f"Notebooks carrying probeAddresses banner: {len(leaks)}")
    print(f"  of which with machine-local/public IPs: {with_ips}")
    if leaks:
        # family breakdown (top-level under MyIA.AI.Notebooks)
        families: dict[str, int] = {}
        for rel, *_ in leaks:
            parts = Path(rel).parts
            fam = parts[1] if len(parts) > 1 and parts[0] == "MyIA.AI.Notebooks" else parts[0]
            families[fam] = families.get(fam, 0) + 1
        print("  family breakdown:")
        for fam, n in sorted(families.items(), key=lambda kv: -kv[1]):
            print(f"    {fam}: {n}")
    if fix:
        print(f"Fixed: {fixed}")
    if errors:
        print(f"Errors: {errors}", file=sys.stderr)
    if leaks and not fix:
        return 1
    return 0 if errors == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("path", nargs="?", default=".", help="file or dir to scan")
    ap.add_argument("--check", action="store_true", help="report only (exit 1 if leaks)")
    ap.add_argument("--fix", action="store_true", help="strip banner outputs in place")
    a = ap.parse_args()
    if a.check and a.fix:
        print("--check and --fix are mutually exclusive", file=sys.stderr)
        return 2
    if not a.check and not a.fix:
        a.check = True  # default to check
    root = Path(a.path)
    if root.is_file():
        # single-file mode: wrap as a 1-element scan
        tmp = root.parent
        # restrict to the single file via a tiny filter
        leaks = []
        nb, raw = _load(root)
        if nb is not None:
            for c in nb.get("cells", []):
                if c.get("cell_type") == "code":
                    n_banner, _ = _cell_leak_info(c)
                    if n_banner:
                        leaks.append(n_banner)
        print(f"{root}: {sum(leaks)} banner outputs in {len(leaks)} cells")
        if a.fix and nb is not None and leaks:
            removed = 0
            for c in nb.get("cells", []):
                if c.get("cell_type") == "code":
                    removed += _strip_cell(c)
            if removed:
                _save(root, nb, raw)
            print(f"  fixed: removed {removed} banner outputs")
        return 1 if (leaks and not a.fix) else 0
    return run(root, fix=a.fix)


if __name__ == "__main__":
    raise SystemExit(main())
