#!/usr/bin/env python3
"""Post-bake fixup for Slidev builds on Windows.

Tell c.1037 ★ NEW : `slidev build` injects the cwd Windows path
(e.g. `C:/Program Files/Git/...`) into the generated HTML/JS/CSS/_redirects
files, and sometimes URL-encodes the space (`Program%20Files`).
This script rewrites every occurrence of the *current* cwd (and the
two known baked-in markers) to relative `'./...'` so the build is
reproducible across machines and CI runners.

Usage:
    cd slides/<deck>
    slidev build --base / --out dist
    python ../../scripts/post_bake_slides.py

Verify:
    grep -r "Program Files\\|Program%20Files" dist/   # must return 0 lines

Note (c.1062 item 2 #15452): the previous version carried four latent
defects that made it a "green that measures nothing" (cf. #15381/#15545):

  1. The rewrite regex was hard-coded to `C:/Program Files/Git/`, so any
     cwd not matching that exact prefix was silently ignored (and the
     `fixed += 1` counter incremented anyway because it was keyed on the
     hit count of `b"Program Files"` in `content`).
  2. The substitution therefore never matched the URL-encoded form
     `Program%20Files` produced by some bundlers.
  3. The residue check called `f.read()` once per pattern, so the second
     pattern always saw an exhausted cursor at EOF -- the verification
     was structurally blind to whatever the rewrite did not catch.
  4. `.map` files were scanned for residue but never rewritten (missing
     from `TARGET_EXTS`).

This module derives the rewrite prefix from `os.getcwd()`, rewrites both
the literal and the URL-encoded forms, counts `fixed` only when the file
content actually changed, and reads each file exactly once per scan.
"""
import os
import re
import sys

ROOT = "dist"
PATTERNS = (b"Program Files", b"Program%20Files")
TARGET_EXTS = (".html", ".js", ".css", ".json", ".txt", ".map")
REDIRECT_FILES = ("_redirects",)


def _is_target(fn: str) -> bool:
    return fn.endswith(TARGET_EXTS) or fn in REDIRECT_FILES


def _cwd_prefix_bytes() -> bytes:
    """Build the cwd-derived prefix used to rewrite baked-in absolute paths.

    `slidev build` injects paths of the form `<cwd>/<sub>` into the output,
    so we substitute any occurrence of `<cwd>/` with `./`. The cwd is taken
    fresh each call -- the script always runs in the deck directory.
    """
    cwd = os.getcwd().replace("\\", "/").rstrip("/").encode("ascii", "replace")
    return cwd + b"/"


def _rewrite(content: bytes, cwd_prefix: bytes) -> bytes:
    """Rewrite `content` in-place: replace cwd-derived paths and the two
    baked-in `Program Files` markers (literal and URL-encoded) with `./`.

    Returns the new bytes (== `content` if no rewrite was needed).
    """
    new = content.replace(cwd_prefix, b"./")
    # Baked-in markers (Tell c.1018-L1) -- not always derived from cwd,
    # sometimes URL-encoded by the bundler.
    new = new.replace(b"Program Files", b".")
    new = new.replace(b"Program%20Files", b".")
    return new


def _scan_dist(root: str):
    """Yield absolute paths of target files under `root`."""
    for r, _, files in os.walk(root):
        for fn in files:
            if _is_target(fn):
                yield os.path.join(r, fn)


def _rewrite_tree(root: str) -> tuple[int, int]:
    """Walk `root`, rewrite every target file. Returns (fixed, total)."""
    cwd_prefix = _cwd_prefix_bytes()
    fixed = 0
    total = 0
    for p in _scan_dist(root):
        try:
            with open(p, "rb") as f:
                content = f.read()
        except OSError:
            continue
        total += 1
        new = _rewrite(content, cwd_prefix)
        if new == content:
            continue
        hits = sum(content.count(pat) for pat in PATTERNS) + content.count(cwd_prefix)
        try:
            with open(p, "wb") as f:
                f.write(new)
        except OSError:
            continue
        print(f"  fixed {p}: hits={hits}")
        fixed += 1
    return fixed, total


def _check_residue(root: str) -> int:
    """Count files under `root` that still carry any of the PATTERNS.

    One read per file, all patterns tested on the same content -- this is
    the structural fix for the previous bug where `f.read()` was called
    once per pattern, exhausting the cursor on the second pattern.
    """
    residue = 0
    for p in _scan_dist(root):
        try:
            with open(p, "rb") as f:
                content = f.read()
        except OSError:
            continue
        if any(pat in content for pat in PATTERNS):
            residue += 1
    return residue


def main() -> int:
    if not os.path.isdir(ROOT):
        print(f"error: '{ROOT}' not found; run 'slidev build --base / --out dist' first", file=sys.stderr)
        return 1
    fixed, total = _rewrite_tree(ROOT)
    print(f"TOTAL: {fixed}/{total} files modified")
    residue = _check_residue(ROOT)
    if residue:
        print(f"FAIL: {residue} files still contain Program Files/Program%20Files", file=sys.stderr)
        return 1
    print("OK: 0 residue Program Files/Program%20Files in dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
