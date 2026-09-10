#!/usr/bin/env python3
"""Post-bake fixup for Slidev builds on Windows.

Tell c.1037 ★ NEW : `slidev build` injects the cwd Windows path
(`C:/Program Files/Git/...`) into the generated HTML/JS/CSS/_redirects
files. This script rewrites those absolute Windows paths to relative
`'.'` so that the build is reproducible across machines and CI runners.

Usage:
    cd slides/<deck>
    slidev build --base / --out dist
    python ../../scripts/post_bake_slides.py

Verify:
    grep -r "Program Files\\|Program%20Files" dist/   # must return 0 lines
"""
import os
import re
import sys

ROOT = "dist"
PATTERNS = (b"Program Files", b"Program%20Files")
PATH_RE = re.compile(rb"C:/Program Files/Git/")
TARGET_EXTS = (".html", ".js", ".css", ".json", ".txt")


def main() -> int:
    if not os.path.isdir(ROOT):
        print(f"error: '{ROOT}' not found; run 'slidev build --base / --out dist' first", file=sys.stderr)
        return 1
    fixed = 0
    total = 0
    for root, _, files in os.walk(ROOT):
        for fn in files:
            if not fn.endswith(TARGET_EXTS) and fn != "_redirects":
                continue
            p = os.path.join(root, fn)
            try:
                with open(p, "rb") as f:
                    content = f.read()
            except OSError:
                continue
            total += 1
            hits = sum(content.count(p_) for p_ in PATTERNS)
            if hits == 0:
                continue
            new = PATH_RE.sub(b"./", content)
            with open(p, "wb") as f:
                f.write(new)
            print(f"  fixed {p}: hits={hits}")
            fixed += 1
    print(f"TOTAL: {fixed}/{total} files modified")
    # Verify no residue
    residue = 0
    for root, _, files in os.walk(ROOT):
        for fn in files:
            p = os.path.join(root, fn)
            try:
                with open(p, "rb") as f:
                    if any(pat in f.read() for pat in PATTERNS):
                        residue += 1
            except OSError:
                continue
    if residue:
        print(f"FAIL: {residue} files still contain Program Files/Program%20Files", file=sys.stderr)
        return 1
    print("OK: 0 residue Program Files/Program%20Files in dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
