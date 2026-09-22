#!/usr/bin/env python3
"""Extract a clean source-only notebook from an executed probe notebook.

Usage:
    python scripts/notebook_tools/extract_probes_source.py <input.ipynb> <output.source.ipynb>

Strips:
- All code-cell `outputs: []` and sets `execution_count = None`.
- Papermill metadata keys (`papermill`, `tags`, `jupyter`, `dotnet_interactive`)
  on every cell, and from notebook-level `metadata`.
- Top-level `metadata.kernelspec` (papermill artifact).
- Papermill error-banner markdown cells (cells containing
  'An Exception was encountered' or 'papermill-error-cell').

Used in PR #17422 (RFC dotnet-restore-bug-17361) to keep a stable
pre-execution reference for future probes, without committing a notebook
that would be auto-flagged by pre-commit H.3.

Tells respectes:
- c.1494 strict (encoding=utf-8)
- c.builder-newline (trailing newline)
- c.gh-posting-hygiene (no -f body=@, --body-file only)
- c.1148 strict (>100 chars body, non-PAYLOAD-TRAP)
"""
import argparse
import hashlib
import json
import os
import sys


def sha256_short(path: str, n: int = 16) -> str:
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:n]


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input", help="executed probe notebook (.ipynb)")
    ap.add_argument("output", help="source-only notebook (.source.ipynb)")
    args = ap.parse_args()

    if not os.path.isfile(args.input):
        print(f"[err] {args.input} not found", file=sys.stderr)
        return 2

    nb = json.load(open(args.input, encoding="utf-8"))

    new_cells = []
    for c in nb.get("cells", []):
        src = "".join(c.get("source", []))
        if c["cell_type"] == "code":
            c["execution_count"] = None
            c["outputs"] = []
        meta = c.get("metadata", {}) or {}
        for k in ("papermill", "tags", "jupyter", "dotnet_interactive"):
            meta.pop(k, None)
        if c["cell_type"] == "markdown":
            if "An Exception was encountered" in src or "papermill-error-cell" in src:
                continue
        new_cells.append(c)

    nb["cells"] = new_cells
    nb_meta = nb.get("metadata", {}) or {}
    for k in ("kernelspec", "papermill", "language_info"):
        nb_meta.pop(k, None)

    os.makedirs(os.path.dirname(os.path.abspath(args.output)), exist_ok=True)
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    # Tell c.builder-newline: trailing newline
    with open(args.output, "ab") as f:
        f.write(b"\n")

    src_sha = sha256_short(args.output)
    in_sha = sha256_short(args.input)
    print(f"[ok] {args.input} -> {args.output}")
    print(f"     input  size: {os.path.getsize(args.input):>6} o, sha: {in_sha}")
    print(f"     output size: {os.path.getsize(args.output):>6} o, sha: {src_sha}")
    print(f"     distinct sha: {src_sha != in_sha}")
    print(f"     cells kept: {len(new_cells)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
