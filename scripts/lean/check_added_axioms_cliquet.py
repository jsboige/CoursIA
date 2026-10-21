#!/usr/bin/env python3
"""Cliquet: lines added to ``*.lean`` files that introduce ``native_decide``,
``sorry`` or ``admit``.

Why this organ exists
---------------------

``LeanVerifier.check_axioms(module, fail_on_sorry=True)`` reads the axiom
graph of the **named constants** of a Lean module. A Lean ``example`` does
not create a constant -- so an ``example : P := by native_decide`` is
invisible to ``check_axioms`` by construction. The same applies to ``sorry``
and ``admit`` written inside an ``example``.

Instance: the compression stack ``#18706`` adds 9 ``native_decide`` anchors,
all inside ``example`` blocks. The CI proof-integrity leg stays green, and
a third-party reviewer attested "0 native_decide in the diff" on the
strength of that green job (review 5568326526 on PR #20584).

Main already carries 221 lines containing ``native_decide`` in 50 own
``.lean`` files, so a retroactive audit would be invasive. The organ
targets the **added** lines of a pull request diff only.

What it does
------------

Given a base SHA and a head SHA:

1. ``git diff`` the in-scope ``*.lean`` files.
2. For each file in the diff, parse the **head** version to build a list of
   declarations with their line ranges. Re-uses the header regex from
   ``count_code_sorry`` (``theorem | lemma | def | example | ...``).
3. For each added line containing a real ``native_decide``, ``sorry`` or
   ``admit`` token (word-boundary, outside comments and string literals),
   find the enclosing declaration by line number.
4. Emit a structured report listing the file, line, token, declaration
   kind, declaration name and whether the line sits in an ``example``.

A control positive (``#20584`` at ``3e9c8504c2``) must render 3 entries,
all in ``example``. A control negative (a Lean PR with no such tokens)
must render an empty list.

Out of scope (matches ``count_code_sorry``): ``.lake/packages/``,
``.mathlib-cache``, ``_peters``, ``agent_tests/.../reference_docs/``,
``foundry-lib/lib/**``. Only own ``*.lean`` files are measured.

Usage
-----

    # Diff against origin/main on the current branch:
    python scripts/lean/check_added_axioms_cliquet.py

    # Explicit SHAs:
    python scripts/lean/check_added_axioms_cliquet.py --base <sha> --head <sha>

    # Restrict to specific paths (default: own lakes):
    python scripts/lean/check_added_axioms_cliquet.py --paths 'MyIA.AI.Notebooks/Compression/Compression_lean/*.lean'

    # JSON for CI consumption:
    python scripts/lean/check_added_axioms_cliquet.py --json

Exit codes:
    0  -- no anchor added, or anchors only inside ``example`` (no action)
    1  -- at least one anchor added inside a named declaration (rouge)
    2  -- invocation error (bad SHA, no lean files in scope)

Module usage:
    from check_added_axioms_cliquet import diff_added_anchors, scan_added_lines
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Iterable

# Re-use the existing comment stripper; for the declaration model, we add
# ``example`` to the keyword list. ``count_code_sorry`` omits it on purpose:
# ``example`` declarations are anonymous, so they have no sorry/vacuous
# attribution to surface. The cliquet is the opposite problem -- it needs
# to KNOW the enclosing declaration is anonymous so it can flag the anchor
# as ``in_example`` rather than ``in_named``.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from count_code_sorry import (  # noqa: E402
    _DECL_MODIFIERS,
    _INSTANCE_ANON_RE,
    strip_lean_comments,
)

# Local, extended keyword list: standard named decls + ``example`` (nameless).
_CLIQUET_DECL_KEYWORDS = (
    "theorem", "lemma", "def", "opaque", "axiom",
    "structure", "inductive", "class", "abbrev",
    "example",
)
_CLIQUET_DECL_RE = re.compile(
    rf"^(?P<indent>\s*){_DECL_MODIFIERS}"
    rf"(?P<kw>{'|'.join(_CLIQUET_DECL_KEYWORDS)}|instance)\s+"
    rf"(?P<name>[A-Za-z_][A-Za-z0-9_']*)?"
)

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

# Tokens the cliquet looks for in added lines. Word-boundary anchored so
# ``sorrying`` or ``admitted`` do not match. A real ``sorry`` tactic is
# rendered as ``by sorry`` (with a space) and ``admit`` similarly; ``decide``
# is not the same as ``native_decide`` and is out of scope.
ANCHOR_TOKENS = ("native_decide", "sorry", "admit")
_ANCHOR_RES = {tok: re.compile(rf"\b{re.escape(tok)}\b") for tok in ANCHOR_TOKENS}

# Directories that are NOT own lakes. Same convention as count_code_sorry.
EXCLUDE_DIR_PARTS = (
    ".lake",
    ".mathlib-cache",
    "_peters",
    "reference_docs",
    "foundry-lib",
)


# --------------------------------------------------------------------------- #
# Data model
# --------------------------------------------------------------------------- #


@dataclass
class Declaration:
    kind: str               # theorem / example / def / instance / ...
    name: str               # declaration name ("" for anonymous / example)
    header_line: int        # 1-based line of the header


@dataclass
class AnchorHit:
    file: str
    line: int
    token: str
    decl_kind: str
    decl_name: str
    in_example: bool        # True when decl_kind == "example" (or anon instance)


@dataclass
class CliquetReport:
    base: str
    head: str
    hits: list[AnchorHit] = field(default_factory=list)
    files_scanned: int = 0
    lines_added: int = 0

    @property
    def hits_in_named_decls(self) -> list[AnchorHit]:
        """Anchors that sit inside a NAMED declaration (the only case the
        cliquet considers a regression). Hits inside ``example`` are
        surfaced but do not cause a non-zero exit.
        """
        return [h for h in self.hits if not h.in_example]


# --------------------------------------------------------------------------- #
# Diff parsing
# --------------------------------------------------------------------------- #


def _is_excluded(path: Path) -> bool:
    return any(part in EXCLUDE_DIR_PARTS for part in path.parts)


def _git_rev_list(base: str, head: str, repo_root: Path | None = None) -> list[Path]:
    """Return the in-scope ``*.lean`` file paths that differ between base
    and head. Includes added, modified and deleted files; the consumer
    filters by content.
    """
    cmd = ["git", "diff", "--name-only", "--diff-filter=AM", f"{base}..{head}"]
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", check=True, cwd=repo_root)
    paths = [Path(p) for p in out.stdout.splitlines() if p.endswith(".lean")]
    return [p for p in paths if not _is_excluded(p)]


def _git_show_file(sha: str, path: Path, repo_root: Path | None = None) -> str | None:
    """Return the file content at ``sha`` (or None if absent)."""
    res = subprocess.run(
        ["git", "show", f"{sha}:{path.as_posix()}"],
        capture_output=True, text=True, encoding="utf-8", cwd=repo_root,
    )
    if res.returncode != 0:
        return None
    return res.stdout


def _git_diff_added_lines(base: str, head: str, path: Path, repo_root: Path | None = None) -> list[int]:
    """Return 1-based line numbers of ADDED lines (no context, no deletions)
    in ``path`` between base and head.
    """
    cmd = ["git", "diff", "--unified=0", "--no-color", f"{base}..{head}", "--", path.as_posix()]
    res = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", cwd=repo_root)
    if res.returncode != 0:
        return []
    added: list[int] = []
    head_line = 0
    for raw in res.stdout.splitlines():
        if raw.startswith("@@"):
            # @@ -<base_start>[,<count>] +<head_start>[,<count>] @@
            m = re.match(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", raw)
            if m:
                head_line = int(m.group(1))
            continue
        if not raw or len(raw) < 1:
            continue
        # git diff metadata: file headers ("diff --git", "+++", "---",
        # "new file mode", "index", ...) and "\ No newline at end of file".
        if raw[:1] in ("\\",) or raw.startswith("diff ") or raw.startswith("+++") or raw.startswith("---") or raw.startswith("new ") or raw.startswith("deleted ") or raw.startswith("old ") or raw.startswith("index "):
            continue
        prefix = raw[0]
        if prefix == "+":
            added.append(head_line)
            head_line += 1
        elif prefix == "-":
            # deletions do not advance head line counter
            continue
        elif prefix == " ":
            # context: advance head line counter
            head_line += 1
        # else: unknown line, ignore
    return added


# --------------------------------------------------------------------------- #
# Declaration parsing of HEAD content
# --------------------------------------------------------------------------- #

# ``example`` and anonymous ``instance`` are declarations that produce no
# named constant in the Lean environment. The cliquet flags anchors inside
# them with ``in_example=True`` and they do NOT cause a non-zero exit.
NAMELESS_KINDS = {"example", "instance"}


def parse_declarations(content: str) -> list[Declaration]:
    """Parse HEAD content of a ``.lean`` file, returning the header of every
    declaration in source order. A declaration's body is taken to span from
    its header line to the next declaration header (regardless of column).
    """
    code = strip_lean_comments(content)
    decls: list[Declaration] = []
    for idx, line in enumerate(code.splitlines(), start=1):
        hdr = _CLIQUET_DECL_RE.match(line) or _INSTANCE_ANON_RE.match(line)
        if not hdr:
            continue
        kw = hdr.groupdict().get("kw") or "instance"
        name = hdr.groupdict().get("name") or ""
        decls.append(Declaration(kind=kw, name=name, header_line=idx))
    return decls


def enclosing_declaration(decls: list[Declaration], line: int) -> Declaration | None:
    """Return the declaration that owns ``line`` (last header strictly <= line).
    Returns ``None`` for top-level (above any declaration) or for module-level
    axioms/opaques that have no body.
    """
    owner: Declaration | None = None
    for d in decls:
        if d.header_line <= line:
            owner = d
        else:
            break
    return owner


# --------------------------------------------------------------------------- #
# Token detection in code (post-comment-strip)
# --------------------------------------------------------------------------- #


def detect_anchors(line_code: str) -> list[str]:
    """Return the subset of ANCHOR_TOKENS found in a code line (already
    comment-stripped and quote-safe via ``strip_lean_comments``).
    """
    return [tok for tok in ANCHOR_TOKENS if _ANCHOR_RES[tok].search(line_code)]


# --------------------------------------------------------------------------- #
# Pipeline
# --------------------------------------------------------------------------- #


def scan_added_lines(
    base: str,
    head: str,
    paths: Iterable[Path] | None = None,
    repo_root: Path | None = None,
) -> CliquetReport:
    """Diff ``base..head`` for ``*.lean`` files and return a structured report.
    ``paths`` is the in-scope set; ``None`` means "all own-lake lean files
    that differ between base and head". ``repo_root`` is the directory in
    which to run ``git`` (defaults to the process cwd).
    """
    report = CliquetReport(base=base, head=head)
    if paths is None:
        paths = _git_rev_list(base, head, repo_root=repo_root)
    paths = [p for p in paths if not _is_excluded(p)]
    for path in paths:
        head_content = _git_show_file(head, path, repo_root=repo_root)
        if head_content is None:
            # file deleted in head -- no anchors possible
            continue
        added_lines = _git_diff_added_lines(base, head, path, repo_root=repo_root)
        if not added_lines:
            continue
        report.files_scanned += 1
        report.lines_added += len(added_lines)
        decls = parse_declarations(head_content)
        code_lines = strip_lean_comments(head_content).splitlines()
        for lineno in added_lines:
            if lineno - 1 >= len(code_lines):
                continue
            code_line = code_lines[lineno - 1]
            tokens = detect_anchors(code_line)
            if not tokens:
                continue
            owner = enclosing_declaration(decls, lineno)
            for tok in tokens:
                if owner is None:
                    kind, name, in_example = "<top-level>", "", True
                else:
                    kind = owner.kind
                    name = owner.name
                    in_example = kind in NAMELESS_KINDS
                report.hits.append(AnchorHit(
                    file=path.as_posix(),
                    line=lineno,
                    token=tok,
                    decl_kind=kind,
                    decl_name=name,
                    in_example=in_example,
                ))
    return report


# --------------------------------------------------------------------------- #
# Output
# --------------------------------------------------------------------------- #


def declared_line(hit: AnchorHit) -> str:
    """La ligne declarative et nominative d'une ancre nommee.

    Format : ``[LEAN-ANCHOR-DECLARED] <fichier>:<decl> -- <motif>``. Elle se
    grep tel quel et se parse sur ``" -- "`` puis sur le premier ``":"`` : le
    compte seul ne dit pas QUELLE declaration rendrait le merge impossible.
    """
    decl = f"{hit.decl_kind} {hit.decl_name}".strip()
    return f"[LEAN-ANCHOR-DECLARED] {hit.file}:{decl} -- {hit.token}"


def render_text(report: CliquetReport) -> str:
    if not report.hits:
        return (
            f"OK: 0 anchor added across {report.files_scanned} file(s), "
            f"{report.lines_added} line(s) added."
        )
    lines = [
        f"REPORT: {len(report.hits)} anchor(s) added across "
        f"{report.files_scanned} file(s), {report.lines_added} line(s) added.",
        "",
        f"{'file':<60} {'line':>4}  {'token':<14}  {'decl':<24}  {'in_example':>10}",
        "-" * 120,
    ]
    for h in report.hits:
        decl = f"{h.decl_kind} {h.decl_name}".strip()
        lines.append(
            f"{h.file:<60} {h.line:>4}  {h.token:<14}  {decl:<24}  {str(h.in_example):>10}"
        )
    named = report.hits_in_named_decls
    if named:
        lines.append("")
        lines.append(
            f"ROUGE: {len(named)} anchor(s) in NAMED declarations "
            f"(would be invisible to check_axioms if you re-execute it)."
        )
        # Une ligne declarative et nominative par ancre nommee : le compte
        # seul ne dit pas QUELLE declaration rendrait le merge impossible.
        # Format : `[LEAN-ANCHOR-DECLARED] <fichier>:<decl> -- <motif>` --
        # se grep tel quel, se parse sur " -- " puis sur le premier ":".
        for h in named:
            lines.append(declared_line(h))
    else:
        lines.append("")
        lines.append(
            "GREEN: all anchors inside `example` (visible to humans, "
            "invisible to check_axioms -- by design)."
        )
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--base", default="origin/main",
                   help="base SHA (default: origin/main)")
    p.add_argument("--head", default="HEAD",
                   help="head SHA (default: HEAD)")
    p.add_argument("--paths", nargs="*", default=None,
                   help="restrict to specific .lean file paths")
    p.add_argument("--json", action="store_true",
                   help="emit machine-readable JSON")
    args = p.parse_args(argv)

    # Validate SHAs early (fail-closed: typo in SHA -> exit 2, not 0).
    for label, sha in (("--base", args.base), ("--head", args.head)):
        res = subprocess.run(
            ["git", "rev-parse", "--verify", f"{sha}^{{commit}}"],
            capture_output=True, text=True, encoding="utf-8",
        )
        if res.returncode != 0:
            print(f"ERROR: {label}={sha!r} does not resolve to a commit.",
                  file=sys.stderr)
            return 2

    paths = [Path(x) for x in args.paths] if args.paths else None
    report = scan_added_lines(args.base, args.head, paths=paths)

    if args.json:
        print(json.dumps({
            "base": report.base,
            "head": report.head,
            "files_scanned": report.files_scanned,
            "lines_added": report.lines_added,
            "hits": [asdict(h) for h in report.hits],
            "hits_in_named": [asdict(h) for h in report.hits_in_named_decls],
            "declared": [declared_line(h) for h in report.hits_in_named_decls],
        }, indent=2, ensure_ascii=False))
    else:
        print(render_text(report))

    # Non-zero exit only when an anchor sits in a NAMED declaration -- the
    # cliquet is informational for example/instance anchors (they are
    # invisible to check_axioms, not a bug in the proof).
    return 1 if report.hits_in_named_decls else 0


if __name__ == "__main__":
    sys.exit(main())
