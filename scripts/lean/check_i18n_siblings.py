#!/usr/bin/env python3
"""Check Lean i18n sibling-pair body byte-identity (EPIC #4980).

Convention #4980 (ratified 2026-07-04, cf ``.claude/rules/lean-i18n.md`` §Lean
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
    python scripts/lean/check_i18n_siblings.py --all --fr-import-advisory

``PATH`` may be a directory (scanned recursively for ``*_en.lean``) or a single
``*_en.lean`` file. ``--all`` scans the whole repository, skipping vendored /
out-of-scope trees (``.lake/``, ``_peters/``, ``reference_docs/``, ...).

Exit code ``0`` if every discovered pair matches (or none is found), ``1`` on any
body drift, on an orphan ``_en`` file (a ``*_en.lean`` whose FR sibling is
missing), or on an *unbuilt* ``_en`` file (a ``*_en.lean`` whose module is
neither an explicit lake root nor covered by a parent glob, so ``lake build``
never compiles it and a green ``Lean CI`` is a false pass for it — the #6749
orphan-trap, which the body comparison alone cannot catch).

A fourth class of finding is reported as **advisory** (does NOT flip the exit
code): a ``HALF-DONE`` pair whose FR-canonical file and its EN mirror still
share one or more verbatim block-comment / docstring bodies ≥100 chars after
trimming (#7763, surfaced during the i18n rollout for ``conway_lean`` /
``knot_lean`` / ``game_theory_lean.Folk`` / ``lean_game_defs_ext.Bayesian`` /
``grothendieck_lean.Conservative``). Two failure modes it catches:

1. The FR-canonical file was never FR-localized — it still carries the EN
   verbatim copy (the common case for the half-baked migrations seen so far).
2. The EN mirror was never written *from* the canonical — it is a verbatim
   copy of the original EN skeleton the FR file was supposed to diverge from.

Advisory by design because legitimate identical bodies exist (a verbatim
bibliographic citation, a shared boilerplate); a human must triage the list
before any flip. The repository's Apache-2.0 licence header is the one
boilerplate that is identical **by construction** in every sibling pair: it is
excluded from the comparison by name (see :func:`is_repo_boilerplate`), so the
advisory keeps its signal — every remaining hit is prose that really was never
translated. The summary line carries the ``| N half-done (advisory)``
counter regardless of exit code.

An opt-in ``--fr-import-advisory`` adds a fifth advisory: in a declaring
``*_en`` module, it reports imports of same-lake FR modules whose ``_en`` twin
exists. It excludes prose-only and consumer-only modules and external imports
such as Mathlib. It never changes the exit code; reviewers use the report to
triage a possible mixed-namespace dependency chain.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from collections import Counter
from pathlib import Path

from lake_selectors import LakefileError, lake_selectors, selected

# Trees out of scope for the #4980 convention (vendored Mathlib, external lakes,
# third-party fixtures) — cf lean-i18n.md §Lean i18n "Hors scope".
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

# A declaration is needed before an FR import is suspicious: prose-only
# mirrors and consumer-only modules may legitimately import the FR source.
_OWN_DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|instance|structure|class|abbrev|inductive)\b",
    re.MULTILINE,
)

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


def extract_block_comment_bodies(src: str) -> list[str]:
    """Return the list of block-comment / docstring BODIES (delimiters
    ``/-`` / ``/--`` / ``-/`` stripped) in source order, nesting-aware — the
    complement of :func:`strip_comments` (which discards them). Lines,
    indentation, and trailing-newline structure are preserved inside each
    body so byte-equality of large prose paragraphs can be detected
    verbatim between siblings.

    Used by the ``HALF-DONE`` advisory (#7763): when an FR/EN sibling pair
    shares one or more verbatim block-comment bodies (longer than
    ``_MIN_HALF_DONE_BODY`` chars after stripping whitespace), the canonical
    FR file has not actually been FR-localized — the EN copy is sitting
    verbatim inside it, which is the migration failure mode this checker
    was extended to surface.
    """
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0
    body_start: int | None = None
    while i < n:
        pair = src[i:i + 2]
        if depth > 0:                          # inside a (possibly nested) block comment
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                if depth == 0 and body_start is not None:
                    out.append(src[body_start:i])
                    body_start = None
                i += 2
            else:
                i += 1
            continue
        # Normal code / string-literal territory
        if pair == "/-":
            depth = 1
            # `/--` is a docstring (single-token); `/-` is a regular block comment.
            # Either way, the body starts AFTER the second hyphen — so the opening
            # marker is consistently stripped (the canonical sibling mirror's doc
            # style may differ from its canonical's).
            j = i + 2
            if j < n and src[j] == "-":
                j += 1
            body_start = j
            i = j
        else:
            i += 1
    return out


# The repository's Apache-2.0 licence header, in the exact form the Lean
# sources carry it. It is identical in every sibling pair **by construction**,
# so it can never carry a signal about the translation: excluding it is what
# keeps the HALF-DONE advisory usable (measured 2026-11-02: 9 of the 10
# half-done pairs of the repository were flagged by this header alone, the
# 10th being the one pair whose EN mirror really does carry FR prose).
_LICENCE_BODY_RE = re.compile(
    r"^Copyright \(c\) \d{4} CoursIA\. All rights reserved\. "
    r"Released under Apache 2\.0 license as described in the file LICENSE\.$"
)


def is_repo_boilerplate(body: str) -> bool:
    """True when ``body`` is repository boilerplate rather than prose.

    Only one such body exists today — the Apache-2.0 licence header — and it
    is recognised **by name** (a named exemption, never a wildcard: same
    discipline as the ``allow-axioms`` whitelist of ``pr-review-discipline``
    §B). A body that merely *resembles* the header is not boilerplate: the
    match is anchored on both ends, so any additional sentence disqualifies it.

    In particular, the fourteen ``_en.lean`` block bodies that concatenate the
    header with a module title inside the same ``/- … -/`` block are **not**
    exempted (measured 2026-11-02, #24161): the exemption covers the pure
    header alone, and a header-plus-title body remains a compared block — it
    stays flagged by ``is_half_done`` if it is shared verbatim with the FR
    sibling.
    """
    text = " ".join(body.split())
    return bool(_LICENCE_BODY_RE.match(text))


def is_half_done(fr_path: Path, en_path: Path,
                 min_body_chars: int = 100) -> tuple[bool, int]:
    """Detect the ``HALF-DONE`` migration failure mode of the i18n rollout
    (#7763): the FR-canonical sibling pair contains at least one block-comment
    body (longer than ``min_body_chars`` after trimming) that is **byte-identical
    verbatim** to a block-comment body in the EN sibling. Two equally plausible
    explanations:

    1. The FR file was never FR-localized — it still carries the EN copy (the
       common case in the conway_lean / folk_theorem / knot_lean cohort).
    2. The EN file was never written from the canonical — it is a verbatim
       copy of the EN skeleton the FR file was meant to diverge from.

    Both indicate a missing human translation step; the checker surfaces them
    as **advisory** (does NOT fail CI) because some legitimate use cases
    produce identical bodies (a verbatim citation, a shared bibliographic
    reference) and must remain a human triage.

    Bodies recognised as repository boilerplate (:func:`is_repo_boilerplate`)
    are excluded from the comparison: they are identical in every pair by
    construction and carry no signal about the translation.

    Returns ``(flagged, n_identical)`` where ``n_identical`` counts distinct
    bodies in ``en_path`` that have a byte-identical match in ``fr_path``.
    """
    fr_bodies = [b.strip() for b in extract_block_comment_bodies(
        fr_path.read_text(encoding="utf-8", errors="replace"))]
    en_bodies = [b.strip() for b in extract_block_comment_bodies(
        en_path.read_text(encoding="utf-8", errors="replace"))]
    if not fr_bodies or not en_bodies:
        return False, 0
    fr_set = {b for b in fr_bodies
              if len(b) >= min_body_chars and not is_repo_boilerplate(b)}
    n_identical = sum(1 for b in en_bodies
                      if len(b) >= min_body_chars
                      and not is_repo_boilerplate(b)
                      and b in fr_set)
    return n_identical > 0, n_identical


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



def _advisory_code(src: str) -> str:
    """Masque commentaires et chaines Lean, en conservant les sauts de ligne.

    Flux reserve au diagnostic d'imports : les chaines doivent rester
    intactes dans la comparaison semantique de ``normalize_body``.
    """
    out = list(src)
    n = len(src)
    raw_start = re.compile(r'r(#*)"')
    char_literal = re.compile(
        r"'(?:\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^\\'\n])'"
    )

    def mask(start: int, end: int) -> None:
        for pos in range(start, end):
            if src[pos] != "\n":
                out[pos] = " "

    i = 0
    while i < n:
        if src[i] == "«":
            # Les identifiants echappes peuvent contenir des guillemets et
            # des marqueurs de commentaire ; ils ne sont pas du code Lean.
            end = src.find("»", i + 1)
            if end == -1:
                mask(i + 1, n)
                i = n
            else:
                mask(i + 1, end)
                i = end + 1
        elif src.startswith("--", i):
            end = src.find("\n", i)
            end = n if end == -1 else end
            mask(i, end)
            i = end
        elif src.startswith("/-", i):
            start = i
            i += 2
            depth = 1
            while i < n and depth:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask(start, i)
        else:
            raw = None
            if src[i] == "r" and (i == 0 or not (src[i - 1].isalnum()
                                                   or src[i - 1] in "_'»")):
                raw = raw_start.match(src, i)
            char = None
            if src[i] == "'" and (i == 0 or not (src[i - 1].isalnum()
                                                    or src[i - 1] in "_'»")):
                char = char_literal.match(src, i)
            if char:
                mask(i, char.end())
                i = char.end()
            elif raw:
                start = i
                closing = '"' + raw.group(1)
                end = src.find(closing, raw.end())
                i = n if end == -1 else end + len(closing)
                mask(start, i)
            elif src[i] == '"':
                start = i
                i += 1
                while i < n:
                    if src[i] == "\\" and i + 1 < n:
                        i += 2
                    elif src[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                mask(start, i)
            else:
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


def fr_import_siblings(en_path: Path) -> list[str]:
    """Find same-lake FR imports with an existing ``_en`` twin.

    This is an opt-in diagnostic, not a gate. It applies only to `_en` files
    that declare in a suffixed namespace and contain their own declarations;
    consumer-only and prose-only mirrors are deliberately excluded. Imports
    such as Mathlib are outside the lake's source tree and therefore excluded.
    """
    if not en_path.name.endswith("_en.lean"):
        return []
    code = _advisory_code(en_path.read_text(encoding="utf-8", errors="replace"))
    namespaces = [m.group(1) for m in _NAMESPACE_DECL.finditer(code)]
    # Un namespace qualifie peut placer le suffixe sur un composant parent,
    # comme `Knots_en.AnyMoves` dans le cas fondateur de #23906.
    if not any(part.endswith("_en")
               for ns in namespaces for part in ns.split(".")):
        return []
    if not _OWN_DECLARATION.search(code):
        return []

    lakefile = next(
        (parent / name for parent in (en_path.parent, *en_path.parents)
         for name in _LAKEFILE_NAMES if (parent / name).is_file()),
        None,
    )
    if lakefile is None:
        return []
    lake = lakefile.parent.resolve()
    findings: list[str] = []
    for match in re.finditer(r"^\s*import\s+(.+)$", code, re.MULTILINE):
        tokens = iter(match.group(1).split())
        for module in tokens:
            if module == "as":
                next(tokens, None)  # import alias, not another module
                continue
            if module.startswith(("«", '"')):
                continue
            if (not re.fullmatch(r"[\w]+(?:\.[\w]+)*", module)
                    or module.endswith("_en")):
                continue
            target = lake.joinpath(*module.split(".")).with_suffix(".lean")
            if not target.is_file() or _excluded(target):
                continue
            if target.with_name(target.stem + "_en.lean").is_file():
                findings.append(module)
    return findings


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
    builds (the #6749 trap), ``(None, reason)`` when there is no lakefile.
    An unparseable lakefile raises ``LakefileError`` instead of being skipped."""
    en_path = en_path.resolve()
    lakefile = enclosing_lake(en_path, repo_root)
    if lakefile is None:
        return None, "no enclosing lakefile"
    selectors = lake_selectors(lakefile.parent)
    module = ".".join(en_path.relative_to(lakefile.parent).with_suffix("").parts)
    if selected(module, selectors):
        return True, ""
    return False, (
        f"module `{module}` absent from {lakefile.name} roots/globs "
        "-> never compiled by `lake build` (a green Lean CI is a false pass)")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="*", help="files or directories to scan")
    parser.add_argument("--all", action="store_true",
                        help="scan the whole repository")
    parser.add_argument(
        "--fr-import-advisory", action="store_true",
        help=(
            "report same-lake unsuffixed imports with an existing `_en` twin "
            "in declaring `_en` modules; advisory only, never changes exit status"
        ),
    )
    parser.add_argument(
        "--allow-unbuilt", action="append", default=[],
        metavar="RELATIVE_PATH",
        help=(
            "Whitelist one unbuilt `_en` mirror (path relative to repo root, "
            "repeatable). The mirror is still scanned and reported as UNBUILT, "
            "but the exit code does NOT flip on it. Use NAMED exemptions only "
            "(never a wildcard) — same discipline as `allow-axioms` "
            "(pr-review-discipline §B): a gate that can never rouge is not a "
            "gate. Reserved for INTRINSIC exceptions where `lake build` cannot "
            "compile the mirror for an external reason (e.g. PetersTour_en "
            "tracks Peters v4.27, #7081). A new UNBUILT entry must be "
            "investigated and added by name; do NOT relax the checker."
        ),
    )
    args = parser.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[2]
    if args.all:
        scan_paths = [repo_root]
    elif args.paths:
        scan_paths = [Path(p) for p in args.paths]
    else:
        parser.error("provide PATH(s) or --all")

    # Normalize whitelist to POSIX strings relative to repo root; accept either
    # forward or backslashes (Windows runner + Linux runner share the same file).
    allow_unbuilt: set[str] = set()
    for raw in args.allow_unbuilt:
        # `str(Path)` on Windows yields backslashes; normalize to POSIX so the
        # whitelist round-trips identically between runner OS.
        norm = str(Path(raw)).replace("\\", "/")
        allow_unbuilt.add(norm)

    en_files = find_en_files(scan_paths)
    if not en_files:
        print("No *_en.lean sibling files found — nothing to check.")
        return 0

    passed = consumer = failed = orphan = unbuilt = half_done = fr_imports = 0
    unbuilt_whitelisted = 0
    for en in sorted(en_files):
        fr = fr_sibling(en)
        if not fr.exists():
            orphan += 1
            print(f"ORPHAN  {en}  (no FR sibling {fr.name})")
            continue
        # Orphan-trap guard (#6749): flag an `_en` mirror Lake never compiles.
        # Orthogonal to the body check below — a pair can be byte-identical yet
        # sit outside the build, which is exactly the failure CI misses.
        try:
            built, why = check_en_built(en, repo_root)
        except LakefileError as exc:
            print(f"ERROR   {exc}", file=sys.stderr)
            return 2
        if built is False:
            # Compute the same POSIX-normalized path the CLI flag uses, so the
            # whitelist matches regardless of OS runner.
            try:
                rel = en.resolve().relative_to(repo_root.resolve()).as_posix()
            except ValueError:
                rel = en.resolve().as_posix()
            whitelisted = rel in allow_unbuilt
            unbuilt += 1
            tag = "  [WHITELISTED]" if whitelisted else ""
            print(f"UNBUILT {en}{tag}")
            print(f"        {why}")
            if whitelisted:
                unbuilt_whitelisted += 1
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
        if args.fr_import_advisory:
            imports = fr_import_siblings(en)
            if imports:
                fr_imports += len(imports)
                print(f"FR-IMPORT  {en}  -> {', '.join(imports)} (advisory)")
        # HALF-DONE advisory (#7763): detect FR-canonical files that still
        # carry verbatim EN prose (the migration was started but never landed
        # on the FR side). Non-gating by design — some identical bodies are
        # legitimate (a citation, a shared bibliographic reference), so a human
        # triages. Repository boilerplate (the licence header) is excluded by
        # name and never reaches this count.
        hd, n_id = is_half_done(fr, en)
        if hd:
            half_done += 1
            print(f"HALF-DONE  {en}  ({n_id} identical block-comment body(s) "
                  f"≥100 chars shared between FR and EN "
                  f"— FR was probably never localized)")
    total = passed + consumer + failed + orphan
    print(f"\n{passed}/{total} pairs byte-identical"
          f" | {consumer} consumer-pattern | {failed} drift | {orphan} orphan"
          f" | {unbuilt} unbuilt ({unbuilt_whitelisted} whitelisted)"
          f" | {half_done} half-done (advisory)"
          + (f" | {fr_imports} FR-import edge(s) (advisory)"
             if args.fr_import_advisory else ""))
    # NB: half_done is ADVISORY — it does NOT flip the exit code. Some
    # legitimate scenarios produce identical bodies (a verbatim bibliographic
    # citation, etc.) and a human must triage; the licence header is excluded
    # by name upstream, so it never inflates the count. The
    # exit code remains a hard fail on real drift / orphan / non-whitelisted
    # unbuilt. Whitelisted unbuilt mirrors are reported as UNBUILT in the log
    # but excluded from the exit-code computation (cliquet: the exemption is
    # named at the call site, never wildcarded — same discipline as the
    # `allow-axioms` whitelist in pr-review-discipline §B).
    effective_unbuilt = unbuilt - unbuilt_whitelisted
    return 0 if (failed == 0 and orphan == 0 and effective_unbuilt == 0) else 1


if __name__ == "__main__":
    raise SystemExit(main())
