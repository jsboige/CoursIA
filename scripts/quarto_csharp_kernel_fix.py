#!/usr/bin/env python3
"""Normalize ``kernelspec.language`` of .NET C# notebooks before Quarto render.

Quarto derives the pandoc code-block class from ``kernelspec.language``. The
.NET Interactive kernel writes ``C#``, which Quarto emits as the invalid
attribute class ``{.c# .cell-code}`` (``#`` is the pandoc ID marker). When the
code fence carries that class AND the cell sits at column 0, Quarto's ipynb ->
qmd writer merges the first source line into the opening fence line; pandoc
then re-parses the cell body as markdown, so C# ``$"..."`` interpolated strings
are consumed by MathJax as LaTeX math and the code leaks out as <p> paragraphs
on the rendered page (issue #11335, measured firsthand on Search-15
-NetworkX-Csharp: 0 sourceCode blocks, 14 math-inline spans, 11 leaked
``::: {.cell-output}`` markers; reproduced identically on Quarto 1.7.32 CI and
1.10.18 local).

Python notebooks are unaffected (`` ``` python`` class, clean fence). Setting
``kernelspec.language`` to ``csharp`` makes Quarto emit `` ``` csharp`` and the
whole defect class disappears (measured: 22 sourceCode blocks, 0 leaks).
``kernelspec.language`` is informational only: kernel selection in Jupyter /
papermill uses ``kernelspec.name`` (``.net-csharp``), which is left untouched,
so the patch never affects execution.

The patch is a **byte-level string replacement** (``"language": "C#"`` ->
``"language": "csharp"``) anchored on the last ``"kernelspec"`` key (cell-level
metadata like ``dotnet_repl`` may carry its own ``"language": "C#"``) — NOT a
JSON load/dump round-trip, which would corrupt notebooks whose output cells
embed raw CR/LF inside JSON strings (the .NET Interactive wrapper script).
apply / restore are therefore byte-perfect on LF-committed notebooks.

Usage:
    python scripts/quarto_csharp_kernel_fix.py apply    # patch C#-kernel notebooks
    python scripts/quarto_csharp_kernel_fix.py restore  # revert exactly what apply did
    python scripts/quarto_csharp_kernel_fix.py check    # exit 1 if any notebook still 'C#'
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import regen_quarto_render as rqr

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST = REPO_ROOT / ".quarto-csharp-manifest.json"

BUGGY = '"language": "C#"'
FIXED = '"language": "csharp"'


def target_notebooks() -> list[str]:
    """Repo-relative POSIX paths of the notebooks Quarto renders (same source
    of truth as the render list, exclusions included)."""
    return rqr.git_tracked_notebooks()


def rewrite_at(rel_path: str, offset: int, old: str, new: str) -> bool:
    """Replace the occurrence of `old` at byte offset `offset`. Exact-position
    patching (not count-based): some notebooks embed the JSON fragment in their
    output cells, so `old` may legitimately appear more than once."""
    path = REPO_ROOT / rel_path
    text = path.read_text(encoding="utf-8")
    if text[offset:offset + len(old)] != old:
        return False
    # write_bytes: Path.write_text would translate \n to \r\n on Windows
    # (default newline=None), producing a phantom EOL diff on LF-committed
    # notebooks (HEAD blobs are LF). Bytes keep the diff minimal.
    path.write_bytes((text[:offset] + new + text[offset + len(old):]).encode("utf-8"))
    return True


def find_offset(text: str, needle: str, rel_path: str) -> int | None:
    # nbformat orders the JSON: cells (with their own cell-level metadata, e.g.
    # "dotnet_repl": {"language": "C#"}) first, then the top-level metadata whose
    # "kernelspec" object carries the language that Quarto reads. The kernelspec
    # block is therefore the LAST section: anchor on the last '"kernelspec"' key.
    kspec = text.rfind('"kernelspec"')
    if kspec < 0:
        raise SystemExit(f"{rel_path}: no 'kernelspec' key found")
    idx = text.find(needle, kspec)
    if idx < 0:
        return None
    if text.find(needle, idx + 1) >= 0:
        raise SystemExit(f"{rel_path}: {needle!r} appears more than once after "
                         "'kernelspec' — refusing to patch ambiguously")
    return idx


def cmd_apply() -> int:
    # Two phases so an ambiguity anywhere leaves the tree untouched (a crash
    # mid-apply would orphan patched files without a manifest to restore them).
    candidates: list[tuple[str, int]] = []
    for rel in target_notebooks():
        text = (REPO_ROOT / rel).read_text(encoding="utf-8")
        idx = find_offset(text, BUGGY, rel)
        if idx is not None:
            candidates.append((rel, idx))
    for rel, idx in candidates:
        rewrite_at(rel, idx, BUGGY, FIXED)
    if candidates:
        import json
        MANIFEST.write_text(
            json.dumps([{"path": rel, "offset": idx} for rel, idx in candidates],
                       indent=1), encoding="utf-8")
    print(f"quarto_csharp_kernel_fix: {len(candidates)} notebooks patched "
          f"({BUGGY} -> {FIXED}).")
    return 0


def cmd_restore() -> int:
    if not MANIFEST.exists():
        print("quarto_csharp_kernel_fix: no manifest — nothing to restore.")
        return 0
    import json
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    restored = 0
    for entry in manifest:
        if rewrite_at(entry["path"], entry["offset"], FIXED, BUGGY):
            restored += 1
    MANIFEST.unlink()
    print(f"quarto_csharp_kernel_fix: {restored} notebooks restored to {BUGGY}.")
    return 0


def cmd_check() -> int:
    bad = []
    for rel in target_notebooks():
        if BUGGY in (REPO_ROOT / rel).read_text(encoding="utf-8"):
            bad.append(rel)
    if bad:
        print(f"quarto_csharp_kernel_fix: {len(bad)} notebooks still carry "
              f"{BUGGY}: {bad[0]} ... (run 'apply' before render)",
              file=sys.stderr)
        return 1
    print("quarto_csharp_kernel_fix: no C#-kernel notebooks in the render list.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("command", choices=("apply", "restore", "check"))
    args = ap.parse_args()
    if args.command == "apply":
        return cmd_apply()
    if args.command == "restore":
        return cmd_restore()
    return cmd_check()


if __name__ == "__main__":
    raise SystemExit(main())
