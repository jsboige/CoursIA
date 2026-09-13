#!/usr/bin/env python3
"""Post-bake fixup for Slidev builds on Windows.

Tell c.1037 ★ NEW : `slidev build` injects the cwd Windows path
(e.g. `C:/Program Files/Git/...`) into the generated HTML/JS/CSS/_redirects
files, and sometimes URL-encodes the space (`Program%20Files`).
This script makes the baked output machine-independent, so the build is
reproducible across machines and CI runners regardless of where the deck
was built.

Usage:
    cd slides/<deck>
    slidev build --base / --out dist
    python ../../scripts/post_bake_slides.py

Verify (informally):
    python -c "import re,sys; sys.exit(0 if not re.search(rb'[A-Za-z]:[/\\\\]', open(sys.argv[1],'rb').read()) else 1)" dist/index.html

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

Tell #15703 ★ NEW : the c.1051 whole-path collapse had two measured
defects of its own. Its greedy class `[^"'\\]*` ran past whitespace and
markup -- `C:/Users/MYIA/data et autres</p>\n<script src=` was silently
deleted. And collapsing ANY absolute path to `./` hid the real question:
a path outside the build root has no meaningful relative form. The
contract, decided on #15703:

  - the ONLY rewrite is the **build-root prefix** (the absolute path of
    the build output directory, `<cwd>/dist`) replaced by `.`, with the
    rest of the path kept byte-intact:
        `D:/deck/dist/assets/app.js` -> `./assets/app.js`
  - an absolute path OUTSIDE the build root makes the post-bake FAIL,
    naming the offending file and path -- it is never silently rewritten
    (collapsing `C:/Program Files/nodejs/lib/app.js` to `./`, or to any
    truncated relative form, resolves nothing: both render a broken
    dist, one of them silently);
  - the path matcher stops at the first quote, whitespace, `<`, `>` or
    `)` -- a path cited in slide prose cannot swallow the markup around
    it (a prose path is out-of-root by construction; the error names it
    in its bounded form, up to the first space);
  - `%20` normalization is bounded to the absolute-path context: prose
    `Program%20Files` survives the bake untouched.

Tell #15747 ★ NEW : `%20` is the URL encoding of a SPACE, not a path
separator. The canonical form decodes it to a space on both sides of the
build-root comparison, and the emitted in-root tail keeps its original
encoding (`mon%20image.png` in -> `mon%20image.png` out, resolving to the
spaced filename on disk; the pre-#15747 `%20 -> /` decode rewrote it to
`mon/image.png`, a silent 404). A build root containing a literal space
(the `Jean Dupont` class) now bakes successfully instead of failing
closed. Prose `%20` still survives untouched (#15703 acceptance 4).

This module:
  - rewrites the build-root prefix of every absolute Windows path
    (`C:/...`, `C:\\...`, `%20`-encoded) baked into the output;
  - rejects (FAIL, exit 1) any absolute path outside the build root,
    naming it, BEFORE writing any file (the tree is either fully
    rewritten or left untouched);
  - reads each file exactly once per scan (no cursor-exhaustion bug);
  - checks for residue on the same shape of pattern as the rewrite
    (drive-letter absolute paths), not on substring markers;
  - counts `fixed` only when file content actually changed.
"""
import os
import re
import sys

ROOT = "dist"
# Patterns detected by `_check_residue`. They mirror the rewrite target:
# any *absolute* Windows path (drive letter) that survives the rewrite is
# a residue. `%20` alone is NOT a residue anymore (#15703): prose
# `Program%20Files` legitimately survives the bake.
RESIDUE_PATTERNS = (
    re.compile(rb"[A-Za-z]:[/\\]"),  # any drive-letter absolute path
)
TARGET_EXTS = (".html", ".js", ".css", ".json", ".txt", ".map")
REDIRECT_FILES = ("_redirects",)


class OutOfRootPathError(Exception):
    """An absolute Windows path outside the build root was found in the
    baked output. The message names the offending path (and, when raised
    by `_rewrite_tree`, the file that carries it)."""


# An absolute Windows path token: drive letter + separator + body. The
# body stops at the FIRST delimiter byte among `"` (string boundary),
# `'`, whitespace, `<`, `>`, `)` -- it must never run across markup: the
# c.1051 class `[^"'\\]*` consumed `</p>\n<script src=` and silently
# deleted it (#15703 residu 1). A prose path is bounded at its first
# space; the error names it in that bounded form.
ABSPATH_RE = re.compile(rb"[A-Za-z]:[/\\][^\"'\s<>)]*")


def _is_target(fn: str) -> bool:
    return fn.endswith(TARGET_EXTS) or fn in REDIRECT_FILES


def _canonical(path: str) -> str:
    """Canonical comparison form: URL-encoded `%20` decoded to a SPACE
    (it is the encoding of one, never a path separator, #15747) and
    native backslashes to `/`, case PRESERVED."""
    return path.replace("%20", " ").replace("\\", "/")


def _original_prefix_end(token_str: str, canon_len: int) -> int:
    """Index in `token_str` where its canonical form reaches `canon_len`
    characters. `%20` compresses 3 chars to 1 when canonicalized, so the
    root boundary cannot be sliced off the canonical string: walk the
    original instead, so the emitted tail keeps its original encoding
    (#15747 -- a `%20` coming in goes out as `%20`)."""
    clen = 0
    i = 0
    n = len(token_str)
    while i < n and clen < canon_len:
        i += 3 if token_str.startswith("%20", i) else 1
        clen += 1
    return i


def _norm(path: str) -> str:
    """Normalize a path for build-root comparison: the canonical form
    case-folded (Windows paths are case-insensitive). Applied to BOTH
    the build root and each candidate token, so the prefix comparison is
    encoding- and case-agnostic. `%20` in a token decodes to a space, so
    a build root containing a literal space (the `Jean Dupont` class)
    matches its `%20`-encoded baked tokens and the bake SUCCEEDS
    (#15747 -- previously such roots failed closed)."""
    return _canonical(path).lower()


def _rewrite(content: bytes, build_root: str) -> bytes:
    """Rewrite the build-root prefix of every absolute Windows path in
    `content` to `.`, keeping the rest of the path byte-intact.

    `build_root` is the absolute path of the build output directory (the
    form `os.path.abspath(ROOT)` produces on the bake machine). The
    comparison is case-insensitive with `%20` decoded to a space and
    backslash separators normalized to `/` on both sides, so
    `<root>/assets/app.js` becomes `./assets/app.js` byte-exactly, a
    token equal to the root itself becomes `.`, and the emitted tail
    keeps its ORIGINAL encoding (`%20` in, `%20` out -- the reference
    stays valid for the on-disk spaced filename, #15747).

    Raises `OutOfRootPathError` naming the path when `content` carries an
    absolute path that is NOT under `build_root` -- the caller fails the
    post-bake instead of silently rewriting it (#15703).
    """
    root_n = _norm(build_root)

    def _sub(m: "re.Match[bytes]") -> bytes:
        token = m.group(0)
        token_str = token.decode("utf-8", "replace")
        token_n = _norm(token_str)
        if token_n == root_n or token_n.startswith(root_n + "/"):
            # In-root: slice the ORIGINAL token at the root boundary --
            # `_original_prefix_end` tracks the 3:1 `%20` compression so
            # the offset is exact -- then canonicalize only the
            # separators of the tail. Case and `%20` encoding of the
            # rest are preserved verbatim (#15747).
            cut = _original_prefix_end(token_str, len(root_n))
            rest = token_str[cut:].replace("\\", "/")
            return b"." + rest.encode("utf-8", "replace")
        raise OutOfRootPathError(
            "absolute path outside the build root: " + token_str
        )

    return ABSPATH_RE.sub(_sub, content)


def _scan_dist(root: str):
    """Yield absolute paths of target files under `root`."""
    for r, _, files in os.walk(root):
        for fn in files:
            if _is_target(fn):
                yield os.path.join(r, fn)


def _count_hits(content: bytes) -> int:
    """Count absolute-path hits in `content` for the per-file log line."""
    return len(re.findall(rb"[A-Za-z]:[/\\]", content))


def _rewrite_tree(root: str, build_root: str) -> tuple[int, int]:
    """Walk `root`, rewrite every target file. Returns (fixed, total).

    Raises `OutOfRootPathError` naming every offending file and path when
    any absolute path outside the build root is found -- raised BEFORE
    any file is written, so the tree is either fully rewritten or left
    untouched.
    """
    fixed = 0
    total = 0
    pending = []
    offenders = []
    for p in _scan_dist(root):
        try:
            with open(p, "rb") as f:
                content = f.read()
        except OSError:
            continue
        total += 1
        try:
            new = _rewrite(content, build_root)
        except OutOfRootPathError as e:
            offenders.append(f"{p}: {e}")
            continue
        if new == content:
            continue
        pending.append((p, new, _count_hits(content)))
    if offenders:
        raise OutOfRootPathError("; ".join(offenders))
    for p, new, hits in pending:
        try:
            with open(p, "wb") as f:
                f.write(new)
        except OSError:
            continue
        print(f"  fixed {p}: hits={hits}")
        fixed += 1
    return fixed, total


def _check_residue(root: str) -> int:
    """Count files under `root` that still carry an absolute Windows path.
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
        if any(pat.search(content) for pat in RESIDUE_PATTERNS):
            residue += 1
    return residue


def main() -> int:
    if not os.path.isdir(ROOT):
        print(f"error: '{ROOT}' not found; run 'slidev build --base / --out dist' first", file=sys.stderr)
        return 1
    build_root = os.path.abspath(ROOT).replace(os.sep, "/")
    try:
        fixed, total = _rewrite_tree(ROOT, build_root)
    except OutOfRootPathError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    print(f"TOTAL: {fixed}/{total} files modified")
    residue = _check_residue(ROOT)
    if residue:
        print(f"FAIL: {residue} files still contain an absolute Windows path", file=sys.stderr)
        return 1
    print("OK: 0 absolute-path residue in dist/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
