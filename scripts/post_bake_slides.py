#!/usr/bin/env python3
"""Post-bake fixup for Slidev builds on Windows.

Tell c.1037 ★ NEW : `slidev build` injects the cwd Windows path
(e.g. `C:/Program Files/Git/...`) into the generated HTML/JS/CSS/_redirects
files, and sometimes URL-encodes the space (`Program%20Files`).
This script rewrites every **absolute Windows path** baked into the
output to relative `'./...'`, so the build is reproducible across machines
and CI runners regardless of where the deck was built.

Usage:
    cd slides/<deck>
    slidev build --base / --out dist
    python ../../scripts/post_bake_slides.py

Verify (informally):
    python -c "import re,sys; sys.exit(0 if not re.search(rb'[A-Za-z]:[/\\\\]|[^A-Za-z]%20', open(sys.argv[1],'rb').read()) else 1)" dist/index.html

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

Tell c.1051 ★ NEW : the prior fix closed (1)-(4) but introduced a fifth
defect (the "green-that-measures-nothing" raised in #15452 point 1) -- the
`_rewrite` step replaced only the substring `Program Files` with `.`,
leaving the absolute machine path intact (e.g. `C:/Program Files/nodejs/...`
became `C:/./nodejs/...`, still absolute). `_check_residue` then matched
only the two literal markers, so it returned 0 even though the absolute
path was still baked into the output. The detection pattern was decoupled
from the rewrite target.

This module:
  - rewrites **every absolute Windows path** (`C:/...`, `C:\...`,
    URL-encoded `%20` separators) baked into the output, using a generic
    drive-letter regex -- independent of any specific cwd or marker;
  - reads each file **exactly once** per scan (no cursor-exhaustion bug);
  - checks for residue on the **same shape of pattern** as the rewrite
    (drive-letter absolute paths and `%20`-encoded separators), not on
    substring markers that the rewrite happened to remove;
  - counts `fixed` only when file content actually changed.
"""
import os
import re
import sys

ROOT = "dist"
# Patterns detected by `_check_residue`. They mirror the rewrite targets:
# any *absolute* Windows path (drive letter) or URL-encoded space separator
# (`%20`) that survives the rewrite is a residue.
RESIDUE_PATTERNS = (
    re.compile(rb"[A-Za-z]:[/\\]"),  # any drive-letter absolute path
    re.compile(rb"%20"),               # URL-encoded separator still present
)
TARGET_EXTS = (".html", ".js", ".css", ".json", ".txt", ".map")
REDIRECT_FILES = ("_redirects",)


def _is_target(fn: str) -> bool:
    return fn.endswith(TARGET_EXTS) or fn in REDIRECT_FILES


def _rewrite(content: bytes) -> bytes:
    """Rewrite every absolute Windows path baked into `content` to a
    relative `./...` form. Returns the rewritten bytes (== `content` if no
    rewrite was needed).

    The rewrite is cwd-independent: any occurrence of `<letter>:/...` or
    `<letter>:\...` is collapsed to `./...`. URL-encoded ` ` (`%20`) inside
    an absolute path is normalized to `/` before the rewrite, so a path
    like `C:/Program%20Files/nodejs/...` becomes `./nodejs/...` -- not
    `C:/./nodejs/...`.
    """
    new = content
    # Normalize URL-encoded `%20` in any drive-letter path context to `/`,
    # so the regex below matches both encodings uniformly.
    new = re.sub(rb"([A-Za-z]):[/\\]%20", rb"\1:/", new)
    new = re.sub(rb"%20([A-Za-z0-9_./-])", rb"/\1", new)
    # Collapse every remaining absolute Windows path to `./`.
    # The negated class excludes ONLY `"`, `'`, and `\` (the quote and
    # backslash bytes that delimit a path inside JS/CSS strings). Whitespace
    # and the letter `s` are KEPT in the matched path: the previous pattern
    # `rb"[^\"'\\s]*"` -- inside `rb"…"`, `\\s` is THREE chars (literal `\`
    # then literal `s`) interpreted by the regex engine as the class
    # `[^"'\\s]` which excludes `{", ', \, s}`. The `*` therefore stopped at
    # the first `s` byte in the path -- the Tell c.1051-L1 ★ NEW fondateur
    # symptom was exactly that:
    #     b"C:/Program Files/nodejs/lib/app.js"
    #         -> b"./s/nodejs/lib/app.js"   (truncated at the 's' of Files)
    #         -> b"./"                     (whole path collapsed, after fix)
    # The fix keeps the class narrow: only the bytes that actually end a
    # path inside a string literal (`"`, `'`, `\`). Whitespace stays in the
    # match so `C:/Program Files/...` collapses to `./` instead of
    # `./ Files/...`.
    new = re.sub(rb"""[A-Za-z]:[/\\][^"'\\]*""", b"./", new)
    return new


def _scan_dist(root: str):
    """Yield absolute paths of target files under `root`."""
    for r, _, files in os.walk(root):
        for fn in files:
            if _is_target(fn):
                yield os.path.join(r, fn)


def _count_hits(content: bytes) -> int:
    """Count absolute-path hits in `content` for the per-file log line."""
    return len(re.findall(rb"[A-Za-z]:[/\\]", content)) + content.count(b"%20")


def _rewrite_tree(root: str) -> tuple[int, int]:
    """Walk `root`, rewrite every target file. Returns (fixed, total)."""
    fixed = 0
    total = 0
    for p in _scan_dist(root):
        try:
            with open(p, "rb") as f:
                content = f.read()
        except OSError:
            continue
        total += 1
        new = _rewrite(content)
        if new == content:
            continue
        hits = _count_hits(content)
        try:
            with open(p, "wb") as f:
                f.write(new)
        except OSError:
            continue
        print(f"  fixed {p}: hits={hits}")
        fixed += 1
    return fixed, total


def _check_residue(root: str) -> int:
    """Count files under `root` that still carry any absolute Windows path
    or URL-encoded separator. One read per file, all patterns tested on
    the same content -- this is the structural fix for the previous bug
    where `f.read()` was called once per pattern, exhausting the cursor
    on the second pattern.
    """
    residue = 0
    for p in _scan_dist(root):
        try:
            with open(p, "rb") as f:
                content = f.read()
        except OSError:
            continue
        if any(pat.search(content) for pat in RESIDUE_PATTERNS):
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
        print(f"FAIL: {residue} files still contain an absolute Windows path or %20 separator", file=sys.stderr)
        return 1
    print("OK: 0 absolute-path residue in dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
