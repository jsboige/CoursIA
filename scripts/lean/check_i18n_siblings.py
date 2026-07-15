#!/usr/bin/env python3
"""Check Lean i18n sibling-pair body byte-identity (EPIC #4980).

Convention #4980 (ratified 2026-07-04, cf ``.claude/rules/code-style.md`` §Lean
i18n): a French-canonical ``Foo.lean`` may have an English mirror ``Foo_en.lean``.
Only the **docstrings** (``/-- ... -/``, ``/- ... -/``) and **comments**
(``-- ...``) differ between the two files; the code **body** — signatures,
``def`` / ``structure`` / ``inductive``, theorem statements, proofs, tactics,
``#eval`` — stays **byte-identical**, modulo the lines that legitimately differ:
``import`` (the ``_en`` file imports its FR sibling and/or Mathlib differently),
``open`` (the ``_en`` file opens the FR namespace), ``namespace`` / ``end`` (the
``_en`` file suffixes the namespace with ``_en``). The two validated i18n
variants (lesson C565-L1) are both accepted: *reuse-FR-names* (the EN file does
``open <FRnamespace>`` and reuses the FR identifiers verbatim — conway_lean) and
*prefixed-suffix* (the EN file refers to ``_en``-suffixed entities such as
``TUGame_en`` — game_theory_lean); the trailing ``_en`` on identifiers is
collapsed symmetrically so genuine body content still compares byte-for-byte.

This is the reusable form of the ad-hoc ``normalize_body()`` that the #4980
rollout has been re-writing by hand for every pair (cf the conway_lean sibling
pairs, forensic notes "byte-identity N/N"). It does **NOT** compile Lean — use
``lake build`` for that, per ``.claude/rules/lean-merge-discipline.md``; it only
proves that the FR and EN bodies have not drifted apart.

Usage
-----
    python scripts/lean/check_i18n_siblings.py PATH [PATH ...]
    python scripts/lean/check_i18n_siblings.py --all

``PATH`` may be a directory (scanned recursively for ``*_en.lean``) or a single
``*_en.lean`` file. ``--all`` scans the whole repository, skipping vendored /
out-of-scope trees (``.lake/``, ``_peters/``, ``reference_docs/``, ...).

Exit code ``0`` if every discovered pair matches (or none is found), ``1`` on any
body drift or on an orphan ``_en`` file (a ``*_en.lean`` whose FR sibling is
missing).
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

# Trees out of scope for the #4980 convention (vendored Mathlib, external lakes,
# third-party fixtures) — cf code-style.md §Lean i18n "Hors scope".
EXCLUDE_PARTS = frozenset(
    {".lake", "_peters", "reference_docs", "agent_tests", ".git", ".claude",
     "node_modules", "foundry-lib"}
)

# Lines that legitimately differ between an FR canonical and its EN mirror.
_STRUCTURAL_LINE = re.compile(r"^\s*(import|open|namespace|end)\b")

# The `_en` anti-collision suffix the convention adds to namespaced identifiers
# in the EN mirror. Two validated i18n variants exist (lesson C565-L1):
#   * reuse-FR-names  — the EN file does `open <FRnamespace>` and references the
#     FR identifiers verbatim (conway_lean); no `_en` suffix in the body.
#   * prefixed-suffix — the EN file defines `_en`-suffixed entities and refers to
#     them with the suffix (game_theory_lean: `TUGame` ↔ `TUGame_en`).
# Collapsing a trailing `_en` on identifiers (applied to BOTH files, so it is
# symmetric) makes the two variants compare equal on genuine body content while
# still surfacing any real divergence.
_EN_SUFFIX = re.compile(r"\b(\w+)_en\b")


def strip_comments(src: str) -> str:
    """Remove Lean block comments (``/- -/`` and ``/-- -/`` docstrings,
    nesting-aware) and ``-- ...`` line comments, while leaving string literals
    untouched. Newlines are preserved so line structure survives."""
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0        # block-comment nesting depth
    in_str = False
    while i < n:
        c = src[i]
        pair = src[i:i + 2]
        if depth > 0:                       # inside a (possibly nested) block comment
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append("\n")        # keep line breaks from multi-line comments
                i += 1
            continue
        if in_str:                          # inside a "..." string literal
            out.append(c)
            if c == "\\" and i + 1 < n:     # escaped char — copy verbatim
                out.append(src[i + 1])
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        # normal code
        if c == '"':
            in_str = True
            out.append(c)
            i += 1
        elif pair == "/-":
            depth += 1
            i += 2
        elif pair == "--":
            j = src.find("\n", i)           # line comment → drop to end of line
            if j == -1:
                break
            i = j                           # leave the newline for the next iteration
        else:
            out.append(c)
            i += 1
    return "".join(out)


def normalize_body(src: str) -> str:
    """Reduce a ``.lean`` source to its comparable code body: strip comments /
    docstrings, drop ``import`` / ``open`` / ``namespace`` / ``end`` lines and
    blank lines, and trim trailing whitespace (indentation is preserved, as Lean
    tactic blocks are indentation-sensitive)."""
    stripped = strip_comments(src)
    kept: list[str] = []
    for line in stripped.splitlines():
        if _STRUCTURAL_LINE.match(line):
            continue
        trimmed = line.rstrip()
        if trimmed.strip() == "":
            continue
        kept.append(trimmed)
    return _EN_SUFFIX.sub(r"\1", "\n".join(kept) + "\n")


def check_pair(fr_path: Path, en_path: Path) -> tuple[bool, str]:
    """Return ``(ok, diff)``: whether the FR and EN bodies match after
    normalization, and a short unified diff when they do not."""
    fr_body = normalize_body(fr_path.read_text(encoding="utf-8"))
    en_body = normalize_body(en_path.read_text(encoding="utf-8"))
    if fr_body == en_body:
        return True, ""
    diff = difflib.unified_diff(
        fr_body.splitlines(), en_body.splitlines(),
        fromfile=str(fr_path), tofile=str(en_path), lineterm="",
    )
    return False, "\n".join(list(diff)[:40])


def _excluded(path: Path) -> bool:
    return any(part in EXCLUDE_PARTS for part in path.parts)


def find_en_files(paths: list[Path]) -> list[Path]:
    """Collect ``*_en.lean`` files from the given files/directories, skipping
    out-of-scope trees and de-duplicating."""
    found: list[Path] = []
    seen: set[Path] = set()
    for raw in paths:
        p = Path(raw)
        candidates: list[Path]
        if p.is_file():
            candidates = [p] if p.name.endswith("_en.lean") else []
        elif p.is_dir():
            candidates = sorted(p.rglob("*_en.lean"))
        else:
            print(f"warning: path not found: {p}", file=sys.stderr)
            candidates = []
        for f in candidates:
            rf = f.resolve()
            if _excluded(f) or rf in seen:
                continue
            seen.add(rf)
            found.append(f)
    return found


def fr_sibling(en_path: Path) -> Path:
    """``Foo_en.lean`` → ``Foo.lean`` in the same directory."""
    return en_path.with_name(en_path.name[: -len("_en.lean")] + ".lean")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", help="files or directories to scan")
    parser.add_argument("--all", action="store_true",
                        help="scan the whole repository")
    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[2]
    if args.all:
        scan_paths = [repo_root]
    elif args.paths:
        scan_paths = [Path(p) for p in args.paths]
    else:
        parser.error("provide PATH(s) or --all")

    en_files = find_en_files(scan_paths)
    if not en_files:
        print("No *_en.lean sibling files found — nothing to check.")
        return 0

    passed = failed = orphan = 0
    for en in sorted(en_files):
        fr = fr_sibling(en)
        rel = en
        if not fr.exists():
            orphan += 1
            print(f"ORPHAN  {rel}  (no FR sibling {fr.name})")
            continue
        ok, diff = check_pair(fr, en)
        if ok:
            passed += 1
            print(f"OK      {rel}")
        else:
            failed += 1
            print(f"DRIFT   {rel}")
            print(diff)
    total = passed + failed + orphan
    print(f"\n{passed}/{total} pairs byte-identical"
          f" | {failed} drift | {orphan} orphan")
    return 0 if (failed == 0 and orphan == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
