#!/usr/bin/env python3
"""Quarto C# kernelspec fix — byte-level apply/restore/check (issue #11335, EPIC #10921).

Problem: notebooks with `kernelspec.language: "C#"` make Quarto emit an invalid
attribute class in the intermediate qmd (```{.c# .cell-code}...). `#` is pandoc's
ID marker, so the fence is broken and pandoc re-parses the C# source as markdown:
interpolated strings `$"..."` get swallowed as LaTeX math, code leaks into <p>.

Fix: `kernelspec.language` is informational (execution uses `kernelspec.name`,
`.net-csharp`), so the render pipeline patches it to "csharp" — Quarto then emits
a clean ``` csharp fence (same shape as ``` python).

Design (per issue acceptance):
- apply:    byte-level replacement of "C#" -> "csharp" in the language field of
            the kernelspec metadata of .NET notebooks only (kernelspec.name ==
            '.net-csharp'). Records the byte offset of every patched token in a
            manifest.
- restore:  reverse replacement, verified against the manifest (same occurrence
            count per file). Files that no longer match are reported and skipped
            loudly (exit 1) rather than silently clobbered.
- check:    report how many notebooks are patched/unpatched; --strict exits 1 if
            any `.net-csharp` notebook still carries "C#" (CI guard after apply).

The round-trip is byte-clean: only the language token bytes differ, everything
else on disk is untouched (no JSON re-serialization).

Manifest: JSON {file: [offsets]}, default `<repo-root>/.quarto_csharp_fix_manifest.json`
(gitignored). Offsets point at the opening quote of the "csharp" token post-apply
(same position the "C#" token occupied pre-apply).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"
DEFAULT_MANIFEST = REPO_ROOT / ".quarto_csharp_fix_manifest.json"

# kernelspec is a flat object: {"display_name": ..., "language": ..., "name": ".net-csharp"}
KERNELSPEC_RE = re.compile(rb'"kernelspec"\s*:\s*\{[^{}]*\}')
DOTNET_NAME_RE = re.compile(rb'"name"\s*:\s*"\.net-csharp"')
LANG_CSHARP_TOKEN_RE = re.compile(rb'("language"\s*:\s*)("C#")')
LANG_FIX_TOKEN_RE = re.compile(rb'("language"\s*:\s*)("csharp")')


def iter_notebooks(root: Path):
    for path in sorted(root.rglob("*.ipynb")):
        yield path


def patched_spans(data: bytes, token_re):
    """Yield (start, end) byte spans of language tokens inside .NET kernelspecs."""
    for ks in KERNELSPEC_RE.finditer(data):
        if not DOTNET_NAME_RE.search(ks.group(0)):
            continue
        for m in token_re.finditer(ks.group(0)):
            yield ks.start() + m.start(2), ks.start() + m.end(2)


def cmd_apply(root: Path, manifest_path: Path) -> int:
    if manifest_path.exists():
        print(f"[apply] manifest {manifest_path} already exists — restore first "
              f"(refusing to overwrite offsets of an in-flight patch)")
        return 1
    manifest = {}
    patched = 0
    for path in iter_notebooks(root):
        data = path.read_bytes()
        spans = list(patched_spans(data, LANG_CSHARP_TOKEN_RE))
        if not spans:
            continue
        out = bytearray(data)
        # replace back-to-front so earlier offsets stay valid while we edit
        for start, end in reversed(spans):
            out[start:end] = b'"csharp"'
        path.write_bytes(bytes(out))
        rel = str(path.relative_to(root)).replace("\\", "/")
        manifest[rel] = [start for start, _ in spans]
        patched += 1
        print(f"[apply] {rel}: {len(spans)} kernelspec token(s)")
    manifest_path.write_text(json.dumps(manifest, indent=1), encoding="utf-8")
    print(f"[apply] {patched} notebook(s) patched, manifest -> {manifest_path.name}")
    return 0


def cmd_restore(manifest_path: Path, root: Path) -> int:
    if not manifest_path.exists():
        print(f"[restore] no manifest at {manifest_path} — nothing to restore")
        return 0
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    failures = 0
    for rel, offsets in manifest.items():
        path = root / rel
        if not path.exists():
            print(f"[restore] MISSING {rel} — file gone since apply, skipping")
            failures += 1
            continue
        data = path.read_bytes()
        spans = list(patched_spans(data, LANG_FIX_TOKEN_RE))
        if len(spans) != len(offsets):
            print(f"[restore] DRIFT {rel}: manifest says {len(offsets)} patch(es), "
                  f"file now has {len(spans)} csharp token(s) — NOT touching it")
            failures += 1
            continue
        out = bytearray(data)
        for start, end in reversed(spans):
            out[start:end] = b'"C#"'
        path.write_bytes(bytes(out))
        print(f"[restore] {rel}: {len(spans)} token(s) reverted")
    if failures:
        print(f"[restore] {failures} file(s) could not be restored — manual review needed")
        return 1
    manifest_path.unlink()
    print("[restore] all files reverted byte-clean, manifest removed")
    return 0


def cmd_check(root: Path, strict: bool) -> int:
    unpatched = patched = 0
    for path in iter_notebooks(root):
        data = path.read_bytes()
        if list(patched_spans(data, LANG_CSHARP_TOKEN_RE)):
            rel = str(path.relative_to(root)).replace("\\", "/")
            print(f"[check] UNPATCHED {rel}")
            unpatched += 1
        elif list(patched_spans(data, LANG_FIX_TOKEN_RE)):
            patched += 1
    print(f"[check] {patched} patched (csharp), {unpatched} still C#")
    if strict and unpatched:
        return 1
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    ap_apply = sub.add_parser("apply", help="patch language C# -> csharp (records offsets)")
    ap_apply.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    ap_apply.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap_restore = sub.add_parser("restore", help="revert using the manifest")
    ap_restore.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap_restore.add_argument("--root", type=Path, default=DEFAULT_ROOT,
                            help="root the manifest paths are relative to")
    ap_check = sub.add_parser("check", help="report patched/unpatched state")
    ap_check.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    ap_check.add_argument("--strict", action="store_true",
                          help="exit 1 if any .net-csharp notebook still carries C#")
    args = ap.parse_args()
    if args.cmd == "apply":
        return cmd_apply(args.root.resolve(), args.manifest)
    if args.cmd == "restore":
        return cmd_restore(args.manifest, args.root.resolve())
    return cmd_check(args.root.resolve(), args.strict)


if __name__ == "__main__":
    sys.exit(main())
