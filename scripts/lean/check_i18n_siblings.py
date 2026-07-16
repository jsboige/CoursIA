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
2026-07-15, after two false-positive DRIFT dispatches — cf PR #6716):

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

Usage
-----
    python scripts/lean/check_i18n_siblings.py PATH [PATH ...]
    python scripts/lean/check_i18n_siblings.py --all

``PATH`` may be a directory (scanned recursively for ``*_en.lean``) or a single
``*_en.lean`` file. ``--all`` scans the whole repository, skipping vendored /
out-of-scope trees (``.lake/``, ``_peters/``, ``reference_docs/``, ...).

Exit code ``0`` if every discovered pair matches (or none is found), ``1`` on any
body drift, on an orphan ``_en`` file (a ``*_en.lean`` whose FR sibling is
missing), or on an *unbuilt* ``_en`` file (a ``*_en.lean`` whose module is
neither an explicit lake root nor covered by a parent glob, so ``lake build``
never compiles it and a green ``Lean CI`` is a false pass for it — the #6749
orphan-trap, which the body comparison alone cannot catch).
"""
from __future__ import annotations

import argparse
import difflib
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


def _drift_detail(fr_blocks: list[str], en_blocks: list[str],
                  fr_path: Path, en_path: Path) -> str:
    """Actionable ``DRIFT`` detail: list blocks *unique to each side* via
    multiset diff instead of a noisy ``difflib`` unified diff on bodies.
    Surfaces the structural divergence directly — which declarations exist
    only in FR / only in EN — which is what a reviewer actually needs to
    judge whether a drift is real (a missing declaration block, a missing
    proof) or harmless (whitespace, ordering, indentation). Falls back to a
    ``difflib`` dump only when the multisets match but bodies still diverge
    at line level (rare: indentation drift inside a block).
    """
    fr_counter = Counter(fr_blocks)
    en_counter = Counter(en_blocks)
    only_en: list[str] = []
    for blk, n in en_counter.items():
        if fr_counter[blk] >= n:
            fr_counter[blk] -= n
        else:
            only_en.append(blk)
    only_fr = list(fr_counter.elements())
    parts: list[str] = []
    if only_en:
        parts.append(f"{len(only_en)} block(s) only in EN:")
        parts.append("\n---\n".join(
            "\n".join(b.splitlines()[:6]) for b in only_en[:3]))
    if only_fr:
        parts.append(f"{len(only_fr)} block(s) only in FR:")
        parts.append("\n---\n".join(
            "\n".join(b.splitlines()[:6]) for b in only_fr[:3]))
    if not parts:
        # Multisets match — divergence is intra-block. Fall back to unified
        # diff for diagnostic (whitespace / indentation drift inside a block).
        diff = difflib.unified_diff(
            fr_blocks, en_blocks,
            fromfile=str(fr_path), tofile=str(en_path), lineterm="",
        )
        return "\n".join(list(diff)[:40])
    return "\n".join(parts)


def check_pair(fr_path: Path, en_path: Path) -> tuple[str, str]:
    """Compare an FR/EN sibling pair. Returns ``(status, detail)`` where
    ``status`` is ``"OK"`` (bodies identical after normalization),
    ``"OK-CONSUMER"`` (the EN file imports the FR module and every declaration
    block it does state matches an FR block — the rest is reused via the
    import, not missing), or
    ``"DRIFT"`` (detail lists the declaration blocks unique to each side —
    see ``_drift_detail``)."""
    fr_src = fr_path.read_text(encoding="utf-8")
    en_src = en_path.read_text(encoding="utf-8")
    fr_body = normalize_body(fr_src)
    en_body = normalize_body(en_src)
    if fr_body == en_body:
        return "OK", ""
    fr_blocks = split_decls(fr_body)
    en_blocks = split_decls(en_body)
    if imports_fr_sibling(strip_comments(en_src), fr_path.stem):
        # Consumer pattern: each EN-stated block must match an FR block (the
        # rest is legitimately reused via the import).
        fr_counter = Counter(fr_blocks)
        unmatched: list[str] = []
        for blk in en_blocks:
            if fr_counter[blk] > 0:
                fr_counter[blk] -= 1
            else:
                unmatched.append(blk)
        if not unmatched:
            reused = sum(fr_counter.values())
            return "OK-CONSUMER", (
                f"{reused} FR declaration block(s) reused via import; "
                "all EN-stated blocks match FR")
        preview = "\n---\n".join(
            "\n".join(b.splitlines()[:6]) for b in unmatched[:3])
        return "DRIFT", (
            f"consumer pattern, but {len(unmatched)} EN block(s) have no FR "
            f"counterpart:\n{preview}")
    return "DRIFT", _drift_detail(fr_blocks, en_blocks, fr_path, en_path)


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


# --- Orphan-trap guard: an `_en` mirror that `lake build` never compiles (#6749)
# A `*_en.lean` whose module is neither an explicit lake root nor covered by a
# parent glob is never built — so a green ``Lean CI (<lake>)`` is a FALSE PASS
# for that sibling (the job only cold-builds the declared roots/globs, and Lake
# matches roots by EXACT module name, not stem). This guard reproduces the
# by-hand roots-array check that gated the #6752 / #6749 / #6753 duplicates,
# which the ``OK``/``DRIFT`` body comparison alone cannot catch: bodies can be
# byte-identical while the mirror silently sits outside the build.
_LAKEFILE_NAMES = ("lakefile.toml", "lakefile.lean")

# `.lean` glob tokens inside `globs := #[...]` / `roots := #[...]`:
#   `Foo          → exact        Foo
#   `Foo_en       → exact        Foo_en
#   `Foo.*  `Foo.+ → glob-prefix Foo   (Foo and its submodules)
#   .submodules `Foo / .andSubmodules `Foo → glob-prefix Foo
_LEAN_BACKTICK = re.compile(
    r"(?P<sub>\.submodules\s+|\.andSubmodules\s+)?"
    r"`(?P<name>[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)"
    r"(?P<glob>\.\*|\.\+)?"
)
_LEAN_LIB = re.compile(r"lean_lib\s+«?([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)»?")
# `.toml` arrays: roots = [ "A", "B" ]  /  globs = [ "A.*" ]
_TOML_ARRAY = re.compile(r"\b(?:roots|globs)\s*=\s*\[(.*?)\]", re.DOTALL)


def lake_targets(lakefile: Path) -> tuple[set[str], set[str]]:
    """Parse a lakefile into ``(exact, glob_prefixes)`` — the modules Lake will
    compile. ``exact`` are single modules (``Foo``, ``Foo_en``); each entry of
    ``glob_prefixes`` is a parent whose subtree is globbed (``Foo`` from
    ``Foo.*`` / ``.submodules `Foo``). Returns empty sets when nothing parses,
    so the caller can conservatively skip rather than false-flag."""
    exact: set[str] = set()
    globs: set[str] = set()
    text = lakefile.read_text(encoding="utf-8", errors="replace")
    if lakefile.name == "lakefile.toml":
        # Drop `#` comments, then read quoted entries of roots/globs arrays.
        text = re.sub(r"#[^\n]*", "", text)
        for arr in _TOML_ARRAY.finditer(text):
            for m in re.finditer(r'"([^"]+)"', arr.group(1)):
                name = m.group(1)
                if name.endswith((".*", ".+")):
                    globs.add(name[:-2])
                else:
                    exact.add(name)
    else:
        # `.lean`: strip comments first (doc comments quote example globs, e.g.
        # conway_cgt_lean's ``globs := #[`Foo, `Foo_en]`` in prose).
        code = strip_comments(text)
        for m in _LEAN_LIB.finditer(code):
            exact.add(m.group(1))  # a lib with no globs roots at its own name
        for m in _LEAN_BACKTICK.finditer(code):
            if m.group("sub") or m.group("glob"):
                globs.add(m.group("name"))
            else:
                exact.add(m.group("name"))
    return exact, globs


def enclosing_lake(en_path: Path, repo_root: Path) -> Path | None:
    """Nearest ancestor directory (up to ``repo_root``) holding a lakefile."""
    for d in [en_path.parent, *en_path.parents]:
        for name in _LAKEFILE_NAMES:
            if (d / name).is_file():
                return d / name
        if d == repo_root:
            break
    return None


def check_en_built(en_path: Path, repo_root: Path) -> tuple[bool | None, str]:
    """Is ``en_path``'s module compiled by its lake? ``(True, "")`` when a root
    or glob covers it, ``(False, reason)`` when it is an orphan Lake never
    builds (the #6749 trap), ``(None, reason)`` when undeterminable (no lakefile
    / unparsable) — the caller skips those rather than false-flag."""
    en_path = en_path.resolve()
    lakefile = enclosing_lake(en_path, repo_root)
    if lakefile is None:
        return None, "no enclosing lakefile"
    exact, globs = lake_targets(lakefile)
    if not exact and not globs:
        return None, f"no roots/globs parsed from {lakefile.name}"
    module = ".".join(en_path.relative_to(lakefile.parent).with_suffix("").parts)
    if module in exact or any(
            module == g or module.startswith(g + ".") for g in globs):
        return True, ""
    return False, (
        f"module `{module}` absent from {lakefile.name} roots/globs "
        "-> never compiled by `lake build` (a green Lean CI is a false pass)")


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

    passed = consumer = failed = orphan = unbuilt = 0
    for en in sorted(en_files):
        fr = fr_sibling(en)
        if not fr.exists():
            orphan += 1
            print(f"ORPHAN  {en}  (no FR sibling {fr.name})")
            continue
        # Orphan-trap guard (#6749): flag an `_en` mirror Lake never compiles.
        # Orthogonal to the body check below — a pair can be byte-identical yet
        # sit outside the build, which is exactly the failure CI misses.
        built, why = check_en_built(en, repo_root)
        if built is False:
            unbuilt += 1
            print(f"UNBUILT {en}")
            print(f"        {why}")
        status, detail = check_pair(fr, en)
        if status == "OK":
            passed += 1
            print(f"OK      {en}")
        elif status == "OK-CONSUMER":
            consumer += 1
            print(f"OK-CONSUMER  {en}  ({detail})")
        else:
            failed += 1
            print(f"DRIFT   {en}")
            print(detail)
    total = passed + consumer + failed + orphan
    print(f"\n{passed}/{total} pairs byte-identical"
          f" | {consumer} consumer-pattern | {failed} drift | {orphan} orphan"
          f" | {unbuilt} unbuilt")
    return 0 if (failed == 0 and orphan == 0 and unbuilt == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
