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

Two structural divergences are recognized as legitimate (erratum on #4980,
2026-07-15, after false-positive DRIFT dispatches — cf PR #6716, then #6725):

* **Self-qualifiers** — an FR canonical whose defs live at top level may write
  ``_root_.X`` where its EN mirror, wrapped in ``namespace <Ns>_en``, must
  write ``<Ns>_en.X``: the same reference expressed from two scopes. Both
  spellings are normalized away (``_root_.`` always; ``<Ns>.`` only for
  namespaces *declared in the same file*, where the prefix is redundant with
  Lean's own name resolution).
* **Consumer/extender pattern** — an EN sibling that ``import``s the FR
  canonical module reuses the FR declarations instead of redeclaring them
  (StableMarriage/Lattice_en). Such a pair is checked by *subset*: every
  declaration block the EN file does state must match an FR block; blocks it
  reuses via the import are reported as ``OK-CONSUMER``, not as missing.
* **Order-insensitive match** — the same set of declaration blocks, on either
  side, but in a different order (typically one side was refactored or a new
  lemma was inserted at a non-corresponding site: ConeKernel_en, #6727). The
  checker reports ``OK-REORDERED`` (with the number of blocks at divergent
  positions) instead of DRIFT; an earlier attempt to reorder one side to
  match the other (PR #6717 v1, commit ``6788d1d1f``) broke the build — so the
  reorder-tolerant verdict is preferred over forced re-ordering.

Real drift that is NOT covered by any of the three legitimate variants is
still reported as ``DRIFT``, but the diagnostic lists the *blocks unique to
each side* rather than a text diff — a Counter diff is actionable for an
LLM reviewer (a literal ``difflib`` line dump is not).

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
import re
import sys
from collections import Counter
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

# Namespace declarations (matched on the comment-stripped source) feed the
# self-qualifier normalization: a `<Ns>.X` reference is only stripped when
# `<Ns>` is declared in the same file (after the `_en` collapse), so foreign
# qualified names still count as body content.
_NAMESPACE_DECL = re.compile(r"^\s*namespace\s+([\w.]+)", re.MULTILINE)

# Import lines (matched on the comment-stripped EN source) feed the
# consumer-pattern detection.
_IMPORT_LINE = re.compile(r"^\s*import\s+([\w.]+)", re.MULTILINE)

# A new top-level declaration (or a standalone attribute preceding one) starts
# a comparison block for the consumer-pattern subset check.
_DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+"
    r"|scoped\s+|local\s+)*"
    r"(?:def|theorem|lemma|structure|inductive|instance|abbrev|class|example"
    r"|axiom|opaque|macro|elab|syntax|notation|attribute|deriving|section"
    r"|variable|universe|#eval|#check|#print|set_option)\b"
)
_ATTR_ONLY = re.compile(r"^@\[[^\]]*\]\s*$")


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
    blank lines, trim trailing whitespace (indentation is preserved, as Lean
    tactic blocks are indentation-sensitive), collapse the ``_en`` suffix, and
    erase semantically-neutral self-qualifiers (``_root_.`` always, ``<Ns>.``
    for namespaces declared in this same file — the Arrow_en/#6716 false
    positive: FR top-level ``_root_.X`` vs EN in-namespace ``<Ns>_en.X``)."""
    stripped = strip_comments(src)
    quals = {"_root_."}
    for m in _NAMESPACE_DECL.finditer(stripped):
        quals.add(_EN_SUFFIX.sub(r"\1", m.group(1)) + ".")
    kept: list[str] = []
    for line in stripped.splitlines():
        if _STRUCTURAL_LINE.match(line):
            continue
        trimmed = line.rstrip()
        if trimmed.strip() == "":
            continue
        kept.append(trimmed)
    body = _EN_SUFFIX.sub(r"\1", "\n".join(kept) + "\n")
    qual_re = re.compile(r"\b(?:%s)" % "|".join(
        re.escape(q) for q in sorted(quals, key=len, reverse=True)))
    return qual_re.sub("", body)


def split_decls(body: str) -> list[str]:
    """Split a normalized body into top-level declaration blocks (used by the
    consumer-pattern subset check)."""
    blocks: list[str] = []
    cur: list[str] = []
    for line in body.splitlines():
        # A standalone attribute opens a block; the declaration that follows
        # it stays attached (so `@[simp]\ntheorem ...` is one block).
        starts_new = bool(_ATTR_ONLY.match(line)) or (
            bool(_DECL_START.match(line))
            and not all(_ATTR_ONLY.match(prev) for prev in cur))
        if cur and starts_new:
            blocks.append("\n".join(cur))
            cur = []
        cur.append(line)
    if cur:
        blocks.append("\n".join(cur))
    return blocks


def imports_fr_sibling(en_src_stripped: str, fr_module: str) -> bool:
    """Consumer/extender pattern (Lattice_en case): the EN file imports the FR
    canonical module and legitimately reuses its declarations instead of
    redeclaring them."""
    return any(
        m.group(1).rsplit(".", 1)[-1] == fr_module
        for m in _IMPORT_LINE.finditer(en_src_stripped)
    )


def check_pair(fr_path: Path, en_path: Path) -> tuple[str, str]:
    """Compare an FR/EN sibling pair. Returns ``(status, detail)`` where
    ``status`` is one of:

    * ``"OK"`` — bodies identical after normalization.
    * ``"OK-CONSUMER"`` — the EN file imports the FR module and every
      declaration block it does state matches an FR block; the rest is reused
      via the import, not missing.
    * ``"OK-REORDERED"`` — the same set of declaration blocks on each side
      (verified as equal multisets via ``Counter``), but in a different
      top-level order. Counts the number of blocks that landed at a
      *different position* (longest-common-prefix walk — a stable proxy for
      how disruptive the reorder is).
    * ``"DRIFT"`` — real divergence: blocks appear on one side that have no
      counterpart on the other. ``detail`` carries a Counter diff (the blocks
      unique to FR / unique to EN, up to a small preview) instead of a
      textual ``difflib`` dump — the Counter diff is what an LLM reviewer can
      act on, while a raw line diff is not.
    """
    fr_src = fr_path.read_text(encoding="utf-8")
    en_src = en_path.read_text(encoding="utf-8")
    fr_body = normalize_body(fr_src)
    en_body = normalize_body(en_src)
    if fr_body == en_body:
        return "OK", ""
    if imports_fr_sibling(strip_comments(en_src), fr_path.stem):
        fr_blocks = Counter(split_decls(fr_body))
        unmatched: list[str] = []
        for blk in split_decls(en_body):
            if fr_blocks[blk] > 0:
                fr_blocks[blk] -= 1
            else:
                unmatched.append(blk)
        if not unmatched:
            reused = sum(fr_blocks.values())
            return "OK-CONSUMER", (
                f"{reused} FR declaration block(s) reused via import; "
                "all EN-stated blocks match FR")
        return _block_diff_diagnostic("consumer pattern, but",
                                     unmatched, [], fr_path, en_path)
    fr_blocks = split_decls(fr_body)
    en_blocks = split_decls(en_body)
    if Counter(fr_blocks) == Counter(en_blocks):
        moved = _count_reordered(fr_blocks, en_blocks)
        return "OK-REORDERED", (
            f"{len(fr_blocks)}/{len(en_blocks)} declaration block(s) match "
            f"order-insensitively ({moved} at a different position)")
    fr_c, en_c = Counter(fr_blocks), Counter(en_blocks)
    fr_only = list((fr_c - en_c).elements())
    en_only = list((en_c - fr_c).elements())
    return _block_diff_diagnostic("", fr_only, en_only, fr_path, en_path)


def _block_diff_diagnostic(prefix: str, fr_only: list[str], en_only: list[str],
                           fr_path: Path, en_path: Path) -> tuple[str, str]:
    """Build a ``DRIFT`` diagnostic that lists the blocks unique to each side
    (up to a 3-block preview on each side) instead of a textual ``difflib``
    dump. The Counter diff is actionable: an LLM reviewer can read
    *\"FR has X, EN has Y, no match\"*; it cannot reliably act on a 40-line
    ``difflib`` patch."""
    parts: list[str] = []
    if prefix:
        parts.append(prefix)
    parts.append(f"{len(fr_only)} FR-only block(s), {len(en_only)} EN-only block(s)")
    if fr_only:
        parts.append("--- FR-only (first 3) ---")
        for blk in fr_only[:3]:
            for line in blk.splitlines()[:6]:
                parts.append(f"FR | {line}")
    if en_only:
        parts.append("--- EN-only (first 3) ---")
        for blk in en_only[:3]:
            for line in blk.splitlines()[:6]:
                parts.append(f"EN | {line}")
    return "DRIFT", "\n".join(parts)


def _count_reordered(fr_blocks: list[str], en_blocks: list[str]) -> int:
    """Count how many top-level declaration blocks landed at a different
    position on the EN side than on the FR side. We walk the ordered pair
    with a longest-common-prefix / -suffix style greedy match: at each index
    we either advance both sides (matched blocks at the same position) or
    just advance the FR side (a block that moved). This is a stable proxy;
    an LLM reviewer using ``OK-REORDERED`` typically wants an order-of-
    magnitude estimate, not an exact permutation distance."""
    f, e = list(fr_blocks), list(en_blocks)
    i = j = moved = 0
    while i < len(f) and j < len(e):
        if f[i] == e[j]:
            i += 1; j += 1
            continue
        # FR block at i is not at the current EN position: count it as moved
        # and advance i. (Repeated blocks favour one side — we just take the
        # first match greedily, which is robust enough for diagnostics.)
        if f[i] in e[j:]:
            moved += 1
            i += 1
        else:
            j += 1
    moved += max(0, len(f) - i)
    return moved


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

    passed = consumer = reordered = failed = orphan = 0
    for en in sorted(en_files):
        fr = fr_sibling(en)
        if not fr.exists():
            orphan += 1
            print(f"ORPHAN  {en}  (no FR sibling {fr.name})")
            continue
        status, detail = check_pair(fr, en)
        if status == "OK":
            passed += 1
            print(f"OK      {en}")
        elif status == "OK-CONSUMER":
            consumer += 1
            print(f"OK-CONSUMER  {en}  ({detail})")
        elif status == "OK-REORDERED":
            reordered += 1
            print(f"OK-REORDERED  {en}  ({detail})")
        else:
            failed += 1
            print(f"DRIFT   {en}")
            print(detail)
    total = passed + consumer + reordered + failed + orphan
    print(f"\n{passed}/{total} pairs byte-identical"
          f" | {consumer} consumer-pattern"
          f" | {reordered} reorder-tolerant"
          f" | {failed} drift | {orphan} orphan")
    return 0 if (failed == 0 and orphan == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
