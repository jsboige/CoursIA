#!/usr/bin/env python3
"""setup_shared_mathlib_scan.py — discovery companion for setup_shared_mathlib.sh.

Cross-platform Python helper used by `setup_shared_mathlib.sh --scan` to
enumerate Lean projects, group them by (toolchain, transitive deps) and
estimate the storage savings from mutualising their mathlib checkouts.

Mirrors the PowerShell discovery in `setup_shared_mathlib.ps1` (mode Scan)
without the NTFS-junction specific parts. Output is TSV on stdout:

    rel<TAB>projdir<TAB>toolchain<TAB>mathlibrev<TAB>groupkey<TAB>mathlibdir<TAB>hascheckout<TAB>issymlink

Exit code:
    0  always (informational scan, never fails the script).

Why this lives in its own file:
    Avoids the MSYS Git Bash + `set -euo pipefail` heredoc-to-Python stdin
    redirection quirk documented in c.1331+102-L1 (where `python3 file > out`
    inside a `set -e` function silently produced a 0-byte output file).
"""

from __future__ import annotations

import json
import os
import subprocess
import sys


def main() -> int:
    repo_root = os.environ.get("REPO_ROOT", "")
    if not repo_root:
        print("ERROR: REPO_ROOT env var not set.", file=sys.stderr)
        return 0  # advisory only

    out = subprocess.run(
        ["git", "-C", repo_root, "ls-files", "--cached", "--others",
         "--exclude-standard", "--", "*lake-manifest.json"],
        capture_output=True, text=True, check=False,
    )
    if out.returncode != 0:
        print(f"WARN: git ls-files failed: {out.stderr[:200]}", file=sys.stderr)
        return 0

    manifests = [m for m in out.stdout.splitlines() if m and ".lake/" not in m]

    # os.path.join on MSYS / Git Bash returns '\\' separators which break
    # when input paths are POSIX-style (the case when called from bash with
    # REPO_ROOT=/c/...). Manual join keeps the slash convention.
    def pj(*parts: str) -> str:
        return "/".join(p.strip("/") for p in parts if p)

    for rel in manifests:
        # rel is the path to lake-manifest.json (relative to repo root).
        # Strip the suffix to get the project dir.
        relpath_no_manifest = (
            rel[: -len("/lake-manifest.json")]
            if rel.endswith("/lake-manifest.json")
            else rel
        )
        projdir = pj(repo_root, relpath_no_manifest)
        manifest_path = pj(projdir, "lake-manifest.json")
        if not os.path.isfile(manifest_path):
            continue
        try:
            with open(manifest_path) as f:
                manifest = json.load(f)
        except Exception:
            continue
        packages = sorted(
            ((p.get("name", ""), p.get("rev", "")) for p in manifest.get("packages", [])),
            key=lambda x: x[0],
        )
        mathlib_pkg = next(((n, r) for (n, r) in packages if n == "mathlib"), None)
        if mathlib_pkg is None:
            continue
        toolchain_path = pj(projdir, "lean-toolchain")
        if os.path.isfile(toolchain_path):
            with open(toolchain_path) as f:
                toolchain = f.read().strip()
        else:
            toolchain = "<missing>"
        pairs = ";".join(f"{n}={r}" for (n, r) in packages)
        group_key = f"{toolchain}|{pairs}"
        mathlibdir = pj(projdir, ".lake/packages/mathlib")
        hascheckout = 1 if os.path.exists(mathlibdir) else 0
        issymlink = 1 if os.path.islink(mathlibdir) else 0
        print(
            "\t".join(
                [
                    relpath_no_manifest,
                    projdir,
                    toolchain,
                    mathlib_pkg[1],
                    group_key,
                    mathlibdir,
                    str(hascheckout),
                    str(issymlink),
                ]
            )
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())