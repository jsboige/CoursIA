#!/usr/bin/env python3
"""Count real ``sorry`` tokens and detect vacuous theorems in own Lean sources.

Why this organ exists
---------------------

``grep -c sorry`` overstates the open-proof debt by ~11x at repo scale: it
counts the word ``sorry`` inside docstrings (``/- ... sorry ... -/``), line
comments (``-- ... sorry``), and string literals. A PR body that cites a
before/after ``sorry`` count drawn from ``grep`` therefore cites a number that
has nothing to do with the actual proof debt, and a coordinator dispatching
"close sorry #N" work from such a count sends a worker to a dry vein (cf the
conway_lean case: ``grep -c sorry`` = 152, real code ``sorry`` = 2 distinct).

Conversely, an *empty* theorem -- one whose conclusion is ``True`` -- sails
through every gate we have: ``grep`` does not see it (no sorry, or a sorry on a
trivial goal), ``lake build`` is green, ``#print axioms`` is green, and the
``sorryAx`` / ``Classical.choice`` scans are green because ``True := trivial``
uses no forbidden axiom. The theorem is fully verified and entirely empty. This
is the worst blind spot we have: closing such a ``sorry`` in one line produces
an authentic-looking "sorry 41 -> 40" with zero mathematics.

This module is the organ (cf [[rule-needs-an-organ-not-more-vigilance]]): a rule
without an organ does not apply. It provides, per own lake:

  1. the real ``sorry`` count -- comment-stripped, attributed to the enclosing
     declaration, with ``_en`` i18n mirrors reported separately so the distinct
     count is not inflated by translation siblings;
  2. an advisory list of vacuous conclusions (``: True``, ``∃ ..., True``) so a
     human can triage the markers that are legit (``*_prerequisites``) from the
     theorems that say nothing.

It runs WITHOUT Lean or Mathlib -- pure text analysis -- so it can be cited in
a PR body or wired into CI as a measurement-only advisory (exit 0 by default;
``--strict`` exits 1 if any vacuous non-marker theorem is found, for the day
the triage is complete).

Out of scope (matching the i18n #4980 convention): ``.lake/packages/`` (Mathlib
vendored), ``_peters/``, ``agent_tests/prover/session_state/reference_docs/``
(third-party fixtures), vendored libs (``foundry-lib/lib/**``). Only own lakes
are measured.

Usage
-----

    # Full repo scan, per-lake table + advisory vacuous list (exit 0):
    python scripts/lean/count_code_sorry.py

    # Single lake:
    python scripts/lean/count_code_sorry.py --lake MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean

    # Machine-readable JSON (for CI / PR-body generation):
    python scripts/lean/count_code_sorry.py --json

    # Strict: exit 1 if a vacuous non-marker theorem remains (post-triage gate):
    python scripts/lean/count_code_sorry.py --strict

Module usage:
    from count_code_sorry import scan_lake, strip_lean_comments
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

# Directories that are NOT own lakes -- third-party / vendored / fixtures.
# Must match the i18n #4980 out-of-scope list (code-style.md).
EXCLUDE_DIR_PARTS = (
    ".lake",            # Mathlib + build artifacts
    "_peters",          # external lake
    "reference_docs",   # agent_tests/prover/session_state/reference_docs/
    "foundry-lib",      # vendored lib
)

# Declaration keywords whose header opens a new named scope.
DECL_KEYWORDS = (
    "theorem", "lemma", "def", "opaque", "axiom",
    "structure", "inductive", "class", "abbrev",
)

# A declaration header: optional leading modifiers/attributes/whitespace, then a
# keyword, then the name. ``instance`` is anonymous-allowed (name optional).
_DECL_MODIFIERS = r"(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|partial\s+|unsafe\s+|rec\s+)*"
_DECL_RE = re.compile(
    rf"^(?P<indent>\s*){_DECL_MODIFIERS}"
    rf"(?P<kw>{'|'.join(DECL_KEYWORDS)}|instance)\s+"
    rf"(?P<name>[A-Za-z_][A-Za-z0-9_']*)?"
)
_INSTANCE_ANON_RE = re.compile(rf"^(?P<indent>\s*){_DECL_MODIFIERS}instance\b")

# sorry as a real tactic token (word-boundary, not inside an identifier).
_SORRY_RE = re.compile(r"\bsorry\b")

# A declaration marker whose ``True`` conclusion is assumed-legit (knot_lean
# MathlibPrerequisites ports). Advisory only -- surfaced, not silenced, so the
# human sees the count but the strict gate does not fire on them.
_MARKER_NAME_RE = re.compile(r".*_prerequisites$")

# Vacuous: the type tail (statement text up to ``:=``) concludes with ``True``
# preceded by ``:`` (return type) or ``,`` (existential/forall conclusion).
# Anchored at the end of the type tail so ``a = True`` (equation) and
# ``True -> True`` (function) are NOT flagged.
_VACUOUS_RE = re.compile(r"(?::|,)\s*True\s*$")


# --------------------------------------------------------------------------- #
# Comment stripping (position-preserving)
# --------------------------------------------------------------------------- #

def strip_lean_comments(text: str) -> str:
    """Return ``text`` with Lean comments blanked (spaces), positions preserved.

    Handles nested block comments ``/- ... -/`` (Lean nests them, unlike C) and
    line comments ``--``. String literals ``"..."`` are skipped so a ``--`` or
    ``/-`` inside a string is not treated as a comment (best-effort: no char is
    perfectly lexed here, but the heuristic is sound for the sorry/True tokens).

    Newlines are preserved so line numbers stay valid for reporting.
    """
    out = []
    i = 0
    n = len(text)
    in_string = False
    block_depth = 0
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        # Inside a block comment: blank everything except newlines, track depth.
        if block_depth > 0:
            if c == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue

        # Not in a block comment.
        if in_string:
            if c == "\\" and nxt:  # escaped char (e.g. \", \\, \n)
                out.append(c)
                out.append(nxt)
                i += 2
                continue
            if c == '"':
                in_string = False
            out.append(c)
            i += 1
            continue

        if c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if c == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if c == "-" and nxt == "-":
            # Line comment: blank to end of line (preserve the newline).
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


# --------------------------------------------------------------------------- #
# Declaration model + scanning
# --------------------------------------------------------------------------- #

@dataclass
class Declaration:
    kind: str               # theorem / lemma / def / instance / ...
    name: str               # declaration name ("" for anonymous instance)
    line: int               # 1-based line of the header
    file: str               # source file path (relative)
    sorry_count: int = 0    # real sorry tokens in this declaration's body
    is_vacuous: bool = False  # conclusion is True (empty theorem)
    is_marker: bool = False   # name matches *_prerequisites (assumed-legit)


@dataclass
class LakeResult:
    lake: str                       # lake name (relative root)
    files: int = 0
    naive_sorry: int = 0            # grep -c sorry (comments included)
    code_sorry: int = 0             # real sorry (comment-stripped)
    code_sorry_en_mirrors: int = 0  # subset of code_sorry inside _en siblings
    declarations: list[Declaration] = field(default_factory=list)

    @property
    def distinct_code_sorry(self) -> int:
        """code_sorry minus the _en i18n mirror tokens (translation siblings)."""
        return self.code_sorry - self.code_sorry_en_mirrors

    @property
    def vacuous(self) -> list[Declaration]:
        return [d for d in self.declarations if d.is_vacuous]


def _is_excluded(path: Path) -> bool:
    return any(part in EXCLUDE_DIR_PARTS for part in path.parts)


def _is_en_mirror(path: Path) -> bool:
    return path.stem.endswith("_en")


def discover_lakes(root: Path) -> list[Path]:
    """Return own lake roots (dirs containing a ``lakefile.lean``), sorted.

    Falls back to ``*_lean`` directories without a lakefile (legacy lakes whose
    lakefile was removed when absorbed, e.g. absorbed into game_theory_lean).
    """
    lakes: list[Path] = []
    for lakefile in root.rglob("lakefile.lean"):
        lake_root = lakefile.parent
        if _is_excluded(lake_root):
            continue
        lakes.append(lake_root)
    # Legacy absorbed lakes: directories named *_lean without a lakefile but
    # containing own .lean files. Surfaced so dead-path references stay visible.
    for candidate in root.rglob("*_lean"):
        if not candidate.is_dir() or _is_excluded(candidate):
            continue
        if candidate in lakes:
            continue
        if any(candidate.samefile(l) for l in lakes):
            continue
        if not any(candidate.rglob("*.lean")):
            continue
        lakes.append(candidate)
    # Deduplicate by resolved path, keep deterministic order.
    seen: set[str] = set()
    unique: list[Path] = []
    for l in lakes:
        key = str(l.resolve())
        if key not in seen:
            seen.add(key)
            unique.append(l)
    unique.sort(key=lambda p: str(p))
    return unique


def scan_file(path: Path, root: Path) -> tuple[list[Declaration], int, int]:
    """Scan one .lean file.

    Returns ``(declarations, naive_sorry, code_sorry)``.
    """
    rel = str(path.relative_to(root))
    try:
        raw = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        raw = path.read_text(encoding="utf-8", errors="replace")

    naive = len(_SORRY_RE.findall(raw))
    code = strip_lean_comments(raw)
    code_sorry = len(_SORRY_RE.findall(code))

    lines = code.splitlines()
    declarations: list[Declaration] = []
    current: Declaration | None = None
    statement_buf: list[str] = []   # lines accumulated until ``:=`` for vacuous check
    seen_assign = False             # whether the current decl passed its ``:=``
    paren_depth = 0                 # brace/paren/bracket depth on the header line region

    def _flush_vacuous() -> None:
        nonlocal current, statement_buf, seen_assign
        # Evaluate on the accumulated statement regardless of whether ``:=``
        # was reached: we truncate at the first ``:=`` so the proof body cannot
        # pollute the type tail. (Gating on ``not seen_assign`` was the bug that
        # skipped every single-line ``theorem foo : True := by trivial``.)
        if current is not None and statement_buf:
            type_tail = "\n".join(statement_buf)
            # Truncate at the first ``:=`` if present on the tail.
            am = re.search(r":=", type_tail)
            if am:
                type_tail = type_tail[:am.start()]
            type_tail = type_tail.rstrip()
            if type_tail and _VACUOUS_RE.search(type_tail):
                current.is_vacuous = True
        statement_buf = []
        seen_assign = False

    for idx, line in enumerate(lines, start=1):
        # New declaration header? (at column 0 or close -- Lean allows indented
        # instances inside a namespace, so we allow leading whitespace.)
        hdr = _DECL_RE.match(line) or _INSTANCE_ANON_RE.match(line)
        if hdr:
            _flush_vacuous()
            kw = hdr.group("kw")
            name = hdr.groupdict().get("name") or ""
            current = Declaration(kind=kw, name=name, line=idx, file=rel,
                                  is_marker=bool(name and _MARKER_NAME_RE.match(name)))
            declarations.append(current)
            paren_depth = 0
            seen_assign = False
            statement_buf = [line]
        elif current is not None:
            if not seen_assign:
                statement_buf.append(line)

        # Track sorry in this line, attributed to the current declaration.
        line_sorry = len(_SORRY_RE.findall(line))
        if line_sorry and current is not None:
            current.sorry_count += line_sorry

        # Track when we cross the ``:=`` that ends the statement.
        if current is not None and not seen_assign:
            # cheap depth tracking on the raw line to avoid matching ``:=``
            # inside a binder type annotation (rare, but keeps FP down)
            if ":=" in line:
                seen_assign = True

    _flush_vacuous()
    return declarations, naive, code_sorry


def scan_lake(lake_root: Path, repo_root: Path) -> LakeResult:
    result = LakeResult(lake=str(lake_root.relative_to(repo_root)))
    # Scan own .lean files; exclude .lake and vendored subdirs at walk time.
    lean_files = [p for p in lake_root.rglob("*.lean") if not _is_excluded(p)]
    lean_files.sort()
    result.files = len(lean_files)
    for path in lean_files:
        # ``d.file`` is stored lake-relative so display can prepend the lake name
        # without doubling the path prefix.
        decls, naive, code = scan_file(path, lake_root)
        result.naive_sorry += naive
        result.code_sorry += code
        if _is_en_mirror(path):
            result.code_sorry_en_mirrors += code
        result.declarations.extend(decls)
    return result


# --------------------------------------------------------------------------- #
# Output formatting
# --------------------------------------------------------------------------- #

def _fmt_ratio(code: int, naive: int) -> str:
    if code == 0:
        return "inf" if naive > 0 else "-"
    return f"{naive / code:.0f}x"


def render_table(results: list[LakeResult]) -> str:
    total_naive = sum(r.naive_sorry for r in results)
    total_code = sum(r.code_sorry for r in results)
    total_distinct = sum(r.distinct_code_sorry for r in results)
    rows = []
    header = f"{'Lake':<48} {'code':>6} {'distinct':>9} {'grep':>6} {'ratio':>6}"
    rows.append(header)
    rows.append("-" * len(header))
    for r in sorted(results, key=lambda x: -x.code_sorry):
        lake_short = _norm(r.lake.replace("MyIA.AI.Notebooks/", ""))
        rows.append(
            f"{lake_short:<48} {r.code_sorry:>6} {r.distinct_code_sorry:>9} "
            f"{r.naive_sorry:>6} {_fmt_ratio(r.code_sorry, r.naive_sorry):>6}"
        )
    rows.append("-" * len(header))
    rows.append(
        f"{'TOTAL':<48} {total_code:>6} {total_distinct:>9} {total_naive:>6} "
        f"{_fmt_ratio(total_code, total_naive):>6}"
    )
    body = "\n".join(rows)
    note = (
        "\n\n"
        "code      = sorry tokens OUTSIDE comments (real proof debt)\n"
        "distinct  = code minus _en i18n mirror tokens (translation siblings)\n"
        "grep      = naive `grep -c sorry` (comments included) -- the misleading number\n"
        "ratio     = grep / code (how much grep overstates the debt)"
    )
    return body + note


def _norm(p: str) -> str:
    """Normalize path separators to forward slashes for repo-consistent display."""
    return p.replace("\\", "/")


def render_vacuous(results: list[LakeResult]) -> str:
    lines = ["", "ADVISORY -- vacuous conclusions (`: True` / `∃ ..., True`)", "=" * 60]
    any_vac = False
    for r in sorted(results, key=lambda x: x.lake):
        for d in r.vacuous:
            any_vac = True
            lake_short = _norm(r.lake.replace("MyIA.AI.Notebooks/", ""))
            tag = " [marker -- assumed legit]" if d.is_marker else ""
            lines.append(f"  {lake_short}/{_norm(d.file)}:{d.line}  {d.kind} {d.name}{tag}")
            if d.sorry_count:
                lines.append(f"      sorry on trivial goal: {d.sorry_count}")
    if not any_vac:
        lines.append("  (none)")
    lines.append("")
    lines.append("These pass lake build + axiom checks but state nothing. Closing a")
    lines.append("`sorry` here yields an authentic-looking count delta with zero math.")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    repo = Path(__file__).resolve().parents[2]
    p.add_argument("--repo", default=str(repo), help="repo root (default: autodetect)")
    p.add_argument("--lake", action="append", default=[],
                   help="scan a single lake root (repeatable); default = all own lakes")
    p.add_argument("--json", action="store_true",
                   help="emit machine-readable JSON instead of the table")
    p.add_argument("--strict", action="store_true",
                   help="exit 1 if any vacuous NON-marker theorem is found")
    p.add_argument("--no-vacuous", action="store_true",
                   help="skip the vacuous-conclusion advisory (sorry count only)")
    args = p.parse_args(argv)

    repo_root = Path(args.repo).resolve()
    if args.lake:
        lake_roots = [repo_root / lk if not Path(lk).is_absolute() else Path(lk)
                      for lk in args.lake]
        # normalize: keep only existing own lakes
        lake_roots = [lk.resolve() for lk in lake_roots if lk.exists()]
    else:
        nb_root = repo_root / "MyIA.AI.Notebooks"
        lake_roots = discover_lakes(nb_root)

    results = [scan_lake(lk, repo_root) for lk in lake_roots]
    results = [r for r in results if r.files > 0]
    results.sort(key=lambda x: x.lake)

    if args.json:
        payload = {
            "lakes": [
                {
                    "lake": _norm(r.lake),
                    "files": r.files,
                    "naive_sorry": r.naive_sorry,
                    "code_sorry": r.code_sorry,
                    "distinct_code_sorry": r.distinct_code_sorry,
                    "vacuous": [
                        {"file": _norm(d.file), "line": d.line, "kind": d.kind,
                         "name": d.name, "is_marker": d.is_marker,
                         "sorry_count": d.sorry_count}
                        for d in r.vacuous
                    ],
                }
                for r in results
            ],
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(render_table(results))
        if not args.no_vacuous:
            print(render_vacuous(results))

    if args.strict:
        offenders = [d for r in results for d in r.vacuous if not d.is_marker]
        if offenders:
            print(f"\nSTRICT FAIL: {len(offenders)} vacuous non-marker theorem(s).",
                  file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
