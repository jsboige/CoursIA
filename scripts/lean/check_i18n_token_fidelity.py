#!/usr/bin/env python3
"""Measure the token fidelity of a Lean FR/EN i18n sibling pair (#4980).

The sibling checker (``check_i18n_siblings.py``) proves that the **code bodies**
of a FR canonical and its ``_en`` mirror are byte-identical. It says nothing
about the **prose** the convention mandates to differ: the docstrings and
comments of the mirror are supposed to be a faithful *translation* of the
canonical ones, and nothing in the toolchain measures that.

This checker measures it, comment by comment:

* **code spans** (backticked literals) -- a backticked token is a reference to
  code. A span that names a **declaration of the very file** and is missing
  from the translation is a HARD finding; any other span (a file path, a
  syntax example, a generic word) is ADVISORY, because a translation may
  legitimately drop it.
* **numbers** -- a numeric literal in prose (an arc count, a bound, a date)
  must survive the translation. HARD finding. Dates are compared as a
  *multiset of their parts*, so ``2026-10-27`` and ``27/10/2026`` match.
* **technical identifiers** outside code spans (camelCase, ``snake_case``,
  ``ALLCAPS``) -- a translation may legitimately rephrase such a mention, so
  these are ADVISORY.

Three mechanisms keep the measure from drowning in false positives:

* the ``_en`` anti-collision suffix is collapsed **symmetrically** on both
  sides (the convention's two validated variants name the same entity ``Foo``
  or ``Foo_en``);
* a **counterpart cross-designation** is exempted: when one side names a file
  ``Knots/Conway.lean`` and the other names the same file ``Conway_en.lean``
  (or with a different path prefix), both mentions are dropped from the
  comparison -- they designate the same artefact, spelled in the convention's
  own way;
* the two comment sequences are paired **by code anchor** (the number of code
  tokens preceding the comment), not by index: a mirror that carries one
  extra comment must not shift the comparison of every later comment.

What the checker does **not** do: it does not replace a phrase-by-phrase
relecture. A translation can keep every token and still mistranslate the
sentence. This instrument **bounds** the technical loss; the semantic reading
stays a human act.

Usage::

    python scripts/lean/check_i18n_token_fidelity.py --all
    python scripts/lean/check_i18n_token_fidelity.py path/to/Foo_en.lean
    python scripts/lean/check_i18n_token_fidelity.py --all --json

Exit code: ``1`` when at least one HARD finding is reported, ``0`` otherwise
(ADVISORY findings never flip the code).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_i18n_siblings import (  # noqa: E402
    find_en_files,
    fr_sibling,
)

# The `_en` anti-collision suffix of the convention (collapsed on BOTH sides).
_EN_SUFFIX = re.compile(r"\b(\w+)_en\b")

# A backticked literal: the reference to code. A span MAY be wrapped over
# several lines by the translation, so the content may contain newlines; its
# internal whitespace is normalized before comparison (the wrapping is a
# typographic choice, the reference is the same).
_CODE_SPAN = re.compile(r"`([^`]{1,600})`")

# A numeric group: a digit run possibly made of several parts separated by a
# decimal/thousand/date separator (``2026-10-27``, ``27/10/2026``, ``1.5``).
_NUMBER_GROUP = re.compile(r"\d+(?:[.,/\-]\d+)*")

# A word-shaped token (identifier, keyword, ordinary English word).
_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# A declaration of a Lean file: the reference to code that a translation
# dropping it really loses.
_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|"
    r"scoped\s+|local\s+|nonrec\s+)*"
    r"(?:def|theorem|lemma|instance|abbrev|structure|inductive|example|axiom|"
    r"opaque|class)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
    re.MULTILINE,
)

# Extensions that make a backticked span a **file reference** -- only those
# take part in the counterpart cross-designation exemption.
_FILE_EXT = (
    "lean", "py", "md", "json", "yml", "yaml", "toml", "txt", "ipynb",
    "cs", "sh", "cfg", "ini", "csv", "xml", "html", "sql",
)

# Severity levels.
HARD = "HARD"
ADVISORY = "ADVISORY"

# Maximum number of findings printed per file (the totals always are).
MAX_PER_FILE = 20


# --------------------------------------------------------------------------
# Source scanning
# --------------------------------------------------------------------------

class _CodeCounter:
    """Counts the code tokens seen so far, whitespace-insensitively.

    The counter is the **anchor** of a comment: the i18n convention makes the
    code bodies of a FR canonical and its ``_en`` mirror identical, so the
    token index of a comment is a stable identifier of the code position the
    comment is attached to -- and it survives the reflow of a translated
    comment (which changes the line count but not the code).
    """

    def __init__(self) -> None:
        self.count = 0
        self.last_kind: str | None = None
        self.pending_space = False

    def feed(self, text: str) -> None:
        for ch in text:
            if ch.isspace():
                self.pending_space = True
                continue
            if ch.isalpha() or ch == "_":
                if not (self.last_kind == "ident" and not self.pending_space):
                    self.count += 1
                self.last_kind = "ident"
            elif ch.isdigit():
                if self.last_kind == "ident" and not self.pending_space:
                    pass  # a digit continues an identifier (foo1)
                elif self.last_kind == "num" and not self.pending_space:
                    pass
                else:
                    self.count += 1
                    self.last_kind = "num"
            else:
                self.count += 1
                self.last_kind = "sym"
            self.pending_space = False


def _skip_string(src: str, i: int, line: int) -> tuple[int, int]:
    """Skip a Lean double-quoted string literal starting at ``i``.

    Returns the index just after the closing quote and the updated line
    number. A ``--`` inside a string is NOT a comment.
    """
    n = len(src)
    i += 1  # opening quote
    while i < n:
        c = src[i]
        if c == "\\":
            if i + 1 < n and src[i + 1] == "\n":
                line += 1
            i += 2
            continue
        if c == "\n":
            line += 1
        elif c == '"':
            return i + 1, line
        i += 1
    return n, line


def _skip_char(src: str, i: int) -> tuple[int, int] | None:
    """Skip a Lean character literal (``'a'``, ``'\\n'``) at ``i``.

    Returns ``(index_after, line_delta)`` or ``None`` when the quote is an
    identifier prime (``foo'``) rather than a character literal.
    """
    n = len(src)
    j = i + 1
    if j < n and src[j] == "\\":
        j += 2
        while j < n and src[j] != "'":
            j += 1
        if j < n:
            return j + 1, 0
        return None
    if j < n and j + 1 < n and src[j + 1] == "'":
        return j + 2, 0
    return None


def scan_comments(src: str) -> list[tuple[int, str, str, int]]:
    """Return ``[(lineno, kind, body, anchor)]`` for every comment of ``src``.

    Kinds: ``line`` (``--``), ``block`` (``/- -/``), ``doc`` (``/-! -/``).
    Block comments are nesting-aware; string and character literals are
    skipped, so a ``--`` inside a string is never mistaken for a comment.
    """
    out: list[tuple[int, str, str, int]] = []
    counter = _CodeCounter()
    i = 0
    n = len(src)
    line = 1
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if c == '"':
            j, line = _skip_string(src, i, line)
            counter.feed(src[i:j])
            i = j
            continue
        if c == "'":
            skipped = _skip_char(src, i)
            if skipped is not None:
                j = skipped[0]
                counter.feed(src[i:j])
                i = j
                continue
            i += 1
            continue
        if src.startswith("--", i) and not src.startswith("---", i):
            j = src.find("\n", i)
            if j == -1:
                j = n
            out.append((line, "line", src[i + 2: j], counter.count))
            i = j
            continue
        if src.startswith("/-", i):
            is_doc = src.startswith("/-!", i)
            depth = 0
            j = i
            while j < n:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    if src[j] == "\n":
                        line += 1
                    j += 1
            else:
                raise ValueError("unterminated block comment at line %d" % line)
            inner = i + (3 if is_doc else 2)
            out.append((line, "doc" if is_doc else "block", src[inner: j - 2],
                        counter.count))
            i = j
            continue
        counter.feed(c)
        i += 1
    return out


def declaration_names(src: str) -> set[str]:
    """The names of the declarations of a Lean file (last dotted component)."""
    names: set[str] = set()
    for m in _DECL.finditer(src):
        names.add(m.group(1).rsplit(".", 1)[-1])
    return names


# --------------------------------------------------------------------------
# Token extraction
# --------------------------------------------------------------------------

def collapse_en(text: str) -> str:
    """Collapse the convention's ``_en`` anti-collision suffix."""
    return _EN_SUFFIX.sub(r"\1", text)


def is_technical(name: str) -> bool:
    """True when ``name`` reads as a code identifier rather than prose.

    ``snake_case``, ``camelCase`` and ``ALLCAPS`` runs of three characters or
    more qualify; an ordinary capitalized word (``Lean``, ``Conway``) does
    not, and neither does a two-letter language tag (``FR``, ``EN``).
    """
    if "_" in name.strip("_"):
        return True
    if re.search(r"[a-z][A-Z]", name):
        return True
    if len(name) >= 3 and re.search(r"[A-Z]{2,}", name):
        return True
    return False


def _file_stem(span: str) -> str | None:
    """Return the stem of a backticked span that names a file, else None."""
    s = span.strip()
    if "/" in s or "\\" in s:
        s = s.replace("\\", "/").rsplit("/", 1)[-1]
    if "." not in s:
        return None
    base, _, ext = s.rpartition(".")
    if ext.lower() not in _FILE_EXT or not base:
        return None
    return collapse_en(base)


def code_spans(body: str) -> list[str]:
    """The backticked literals of ``body`` (order preserved).

    The internal whitespace of a span is normalized: a translation may wrap
    a long reference over several lines, which changes the wrapping but not
    the reference.
    """
    out: list[str] = []
    for m in _CODE_SPAN.finditer(body):
        span = " ".join(m.group(1).split())
        if span:
            out.append(span)
    return out


def number_parts(body: str) -> list[str]:
    """The digit parts of ``body``, code spans excluded.

    A group is split on its separators, so ``2026-10-27`` contributes the
    parts ``2026``, ``10`` and ``27``: a date reads the same whether it is
    written in one format or another.
    """
    stripped = _CODE_SPAN.sub(" ", body)
    parts: list[str] = []
    for m in _NUMBER_GROUP.finditer(stripped):
        for p in re.split(r"[.,/\-]", m.group(0)):
            if p:
                parts.append(p)
    return parts


def has_year(body: str) -> bool:
    """True when ``body`` carries a four-digit year somewhere."""
    stripped = _CODE_SPAN.sub(" ", body)
    return any(re.search(r"\b\d{4}\b", m.group(0))
               for m in _NUMBER_GROUP.finditer(stripped))


# The English words that carry a small number in a translation.
_NUMBER_WORDS = {
    0: "zero", 1: "one", 2: "two", 3: "three", 4: "four", 5: "five",
    6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten", 11: "eleven",
    12: "twelve", 13: "thirteen", 14: "fourteen", 15: "fifteen",
    16: "sixteen", 17: "seventeen", 18: "eighteen", 19: "nineteen",
    20: "twenty",
}


def number_is_carried_elsewhere(part: str, other_body: str) -> bool:
    """True when the other side carries the number in another form.

    Two mitigations keep the number class from drowning in false positives:
    a translation may spell a small number in words ("one" for ``1``), and it
    may express a date differently ("April 7, 2026" for ``2026-04-07``).
    """
    if part.isdigit():
        value = int(part)
        word = _NUMBER_WORDS.get(value)
        if word and re.search(r"\b%s\b" % word, other_body, re.IGNORECASE):
            return True
        if len(part) <= 2 and has_year(other_body):
            return True
    return False


def technical_identifiers(body: str) -> set[str]:
    """The technical identifiers mentioned in ``body`` outside code spans."""
    stripped = _CODE_SPAN.sub(" ", body)
    out: set[str] = set()
    for m in _WORD.finditer(stripped):
        word = m.group(0)
        if is_technical(word):
            out.add(collapse_en(word))
    return out


def designation_exemptions(fr_body: str, en_body: str) -> tuple[set[str], set[str]]:
    """Return the code spans to drop from each side (counterpart designation).

    A span naming a file is exempt when the other side names a file with the
    same stem: the two mentions designate the same artefact, spelled in the
    convention's own way (``Knots/Conway.lean`` vs ``Conway_en.lean``).
    """
    fr_spans = code_spans(fr_body)
    en_spans = code_spans(en_body)
    fr_stems = {s for s in (_file_stem(x) for x in fr_spans) if s}
    en_stems = {s for s in (_file_stem(x) for x in en_spans) if s}
    shared = fr_stems & en_stems
    if not shared:
        return set(), set()
    drop_fr = {x for x in fr_spans if _file_stem(x) in shared}
    drop_en = {x for x in en_spans if _file_stem(x) in shared}
    return drop_fr, drop_en


def span_is_decl_ref(span: str, decls: set[str]) -> bool:
    """True when ``span`` names a declaration of the file being translated."""
    for word in _WORD.finditer(span):
        if word.group(0).rsplit(".", 1)[-1] in decls:
            return True
    return False


# --------------------------------------------------------------------------
# Pair comparison
# --------------------------------------------------------------------------

def compare_bodies(fr_body: str, en_body: str,
                   decls: set[str] | None = None) -> list[dict]:
    """Compare one FR/EN comment-body pair; return the list of findings."""
    decls = decls or set()
    findings: list[dict] = []
    drop_fr, drop_en = designation_exemptions(fr_body, en_body)

    fr_spans = {collapse_en(s) for s in code_spans(fr_body)} - {
        collapse_en(s) for s in drop_fr}
    en_spans = {collapse_en(s) for s in code_spans(en_body)} - {
        collapse_en(s) for s in drop_en}

    for span in sorted(fr_spans - en_spans):
        findings.append({"severity": span_severity(span, decls), "kind": "code-span",
                         "token": span, "side": "FR"})
    for span in sorted(en_spans - fr_spans):
        findings.append({"severity": span_severity(span, decls), "kind": "code-span",
                         "token": span, "side": "EN"})

    fr_nums = Counter(number_parts(fr_body))
    en_nums = Counter(number_parts(en_body))
    for num, count in sorted((fr_nums - en_nums).items()):
        if number_is_carried_elsewhere(num, en_body):
            continue
        findings.append({"severity": HARD, "kind": "number",
                         "token": num, "side": "FR"})
    for num, count in sorted((en_nums - fr_nums).items()):
        if number_is_carried_elsewhere(num, fr_body):
            continue
        findings.append({"severity": HARD, "kind": "number",
                         "token": num, "side": "EN"})

    fr_ids = technical_identifiers(fr_body)
    en_ids = technical_identifiers(en_body)
    for ident in sorted(fr_ids - en_ids):
        findings.append({"severity": ADVISORY, "kind": "identifier",
                         "token": ident, "side": "FR"})
    for ident in sorted(en_ids - fr_ids):
        findings.append({"severity": ADVISORY, "kind": "identifier",
                         "token": ident, "side": "EN"})
    return findings


def span_severity(span: str, decls: set[str]) -> str:
    """A dropped span is HARD when it names a declaration of the file."""
    return HARD if span_is_decl_ref(span, decls) else ADVISORY


def _best_shift(fr_anchors: set[int], en_anchors: set[int]) -> int:
    """The constant offset that aligns the two anchor sequences best.

    The returned ``delta`` satisfies ``en_anchor = fr_anchor + delta``. A
    mirror that carries an extra import (or any other extra code) shifts
    every later anchor by a constant; a per-file search absorbs it, while an
    index pairing would misalign every comment after the shift.
    """
    best = 0
    best_score = -1
    for delta in range(-40, 41):
        score = sum(1 for a in fr_anchors if (a + delta) in en_anchors)
        if score > best_score or (score == best_score and abs(delta) < abs(best)):
            best_score = score
            best = delta
    return best


def compare_files(fr_path: Path, en_path: Path) -> dict:
    """Compare the FR canonical and its EN mirror; return a pair report."""
    fr_src = fr_path.read_text(encoding="utf-8", errors="replace")
    en_src = en_path.read_text(encoding="utf-8", errors="replace")
    fr_comments = scan_comments(fr_src)
    en_comments = scan_comments(en_src)
    decls = declaration_names(fr_src) | declaration_names(en_src)

    fr_by_anchor: dict[int, list] = {}
    for c in fr_comments:
        fr_by_anchor.setdefault(c[3], []).append(c)
    en_by_anchor: dict[int, list] = {}
    for c in en_comments:
        en_by_anchor.setdefault(c[3], []).append(c)

    shift = _best_shift(set(fr_by_anchor), set(en_by_anchor))

    # The FIRST comment of a file is its presentation header. The EN mirror
    # states its own metadata there ("English mirror of <path> (FR-first
    # canonical, tranche N EPIC #4980, <date>)"), which has no FR counterpart
    # by design: comparing it would report every metadata token of one side
    # as a loss of the other. The header is therefore excluded from the token
    # comparison -- when both sides carry one at the same anchor.
    shared_anchors = set(fr_by_anchor) & {a + shift for a in en_by_anchor}
    header_anchor = min(shared_anchors) if shared_anchors else None

    pairs: list[dict] = []
    unpaired: list[dict] = []
    for anchor in sorted(set(fr_by_anchor) | {a - shift for a in en_by_anchor}):
        fr_group = fr_by_anchor.get(anchor, [])
        en_group = en_by_anchor.get(anchor + shift, [])
        is_header = anchor == header_anchor
        for k in range(max(len(fr_group), len(en_group))):
            if k < len(fr_group):
                fr_line, fr_kind, fr_body, _ = fr_group[k]
            else:
                fr_line, fr_kind, fr_body = (0, "-", "")
            if k < len(en_group):
                en_line, en_kind, en_body, _ = en_group[k]
            else:
                en_line, en_kind, en_body = (0, "-", "")
            findings = (compare_bodies(fr_body, en_body, decls)
                        if (fr_body and en_body and not is_header) else [])
            pair = {
                "index": len(pairs) + 1,
                "anchor": anchor,
                "fr_line": fr_line,
                "en_line": en_line,
                "fr_kind": fr_kind,
                "en_kind": en_kind,
                "findings": findings,
            }
            pairs.append(pair)
            if not (fr_body and en_body) and not is_header:
                side = "EN" if fr_body else "FR"
                unpaired.append({"severity": ADVISORY, "kind": "unpaired-comment",
                                 "side": side, "line": fr_line or en_line,
                                 "anchor": anchor,
                                 "body": (fr_body or en_body).strip()[:120]})

    report = {
        "fr": str(fr_path),
        "en": str(en_path),
        "fr_comments": len(fr_comments),
        "en_comments": len(en_comments),
        "anchor_shift": shift,
        "pairs": pairs,
        "unpaired": unpaired,
        "findings": [dict(f, pair=p["index"], fr_line=p["fr_line"],
                          en_line=p["en_line"])
                     for p in pairs for f in p["findings"]],
    }
    if len(fr_comments) != len(en_comments):
        report["count_mismatch"] = {
            "severity": ADVISORY,
            "kind": "comment-count",
            "fr": len(fr_comments),
            "en": len(en_comments),
        }
    return report


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

def format_report(reports: list[dict], max_per_file: int = MAX_PER_FILE) -> str:
    lines: list[str] = []
    hard = 0
    advisory = 0
    compared = 0
    for rep in reports:
        all_findings = list(rep["findings"]) + list(rep.get("unpaired", []))
        if not all_findings and not rep.get("count_mismatch"):
            continue
        lines.append("TOKEN-FIDELITY  %s" % rep["en"])
        if rep.get("count_mismatch"):
            mm = rep["count_mismatch"]
            advisory += 1
            lines.append(
                "  %s comment-count: FR %d comments / EN %d comments"
                % (mm["severity"], mm["fr"], mm["en"]))
        shown = 0
        for pair in rep["pairs"]:
            if not pair["findings"]:
                continue
            compared += 1
            if shown >= max_per_file:
                break
            shown += 1
            lines.append("  pair %d  (FR L%d %s / EN L%d %s)"
                         % (pair["index"], pair["fr_line"], pair["fr_kind"],
                            pair["en_line"], pair["en_kind"]))
            for f in pair["findings"]:
                lines.append("    %-8s %s %s '%s'"
                             % (f["severity"], f["kind"], f["side"].lower(),
                                f["token"]))
        for u in rep.get("unpaired", []):
            if shown >= max_per_file:
                continue
            shown += 1
            lines.append("  %-8s %s %s (L%d, anchor %d) '%s'"
                         % (u["severity"], u["kind"], u["side"].lower(),
                            u["line"], u["anchor"], u["body"].replace("\n", " ")))
        n_hard = sum(1 for f in rep["findings"] if f["severity"] == HARD)
        n_adv = len(rep["findings"]) - n_hard + len(rep.get("unpaired", []))
        lines.append("  totals: %d hard, %d advisory" % (n_hard, n_adv))
    # The counts must cover the findings that the per-file cap hid.
    for rep in reports:
        hard += sum(1 for f in rep["findings"] if f["severity"] == HARD)
        advisory += sum(1 for f in rep["findings"] if f["severity"] != HARD)
        advisory += len(rep.get("unpaired", []))
    lines.append(
        "SUMMARY  %d file(s) | %d pair(s) with a finding | %d hard | %d advisory"
        % (len([r for r in reports if r["findings"] or r.get("unpaired")
                 or r.get("count_mismatch")]), compared, hard, advisory))
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Measure the token fidelity of Lean FR/EN i18n siblings.")
    parser.add_argument("paths", nargs="*", help="files or directories to scan")
    parser.add_argument("--all", action="store_true",
                        help="scan every *_en.lean of the repository")
    parser.add_argument("--json", action="store_true",
                        help="emit the report as JSON")
    parser.add_argument("--max-per-file", type=int, default=MAX_PER_FILE,
                        help="findings printed per file (totals always are)")
    args = parser.parse_args(argv)

    # Windows consoles default to a legacy code page: a Lean docstring may
    # carry any Unicode character, and the report must not die on it.
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")

    repo_root = Path(__file__).resolve().parents[2]
    if args.all:
        roots = [repo_root]
    elif args.paths:
        roots = [Path(p) for p in args.paths]
    else:
        parser.error("give PATH(s) or --all")

    reports: list[dict] = []
    for en_path in find_en_files(roots):
        fr_path = fr_sibling(en_path)
        if not fr_path.exists():
            continue
        try:
            reports.append(compare_files(fr_path, en_path))
        except ValueError as exc:
            print("skip %s: %s" % (en_path, exc), file=sys.stderr)

    if args.json:
        print(json.dumps(reports, ensure_ascii=False, indent=2))
    else:
        print(format_report(reports, args.max_per_file))

    hard = sum(1 for r in reports for f in r["findings"] if f["severity"] == HARD)
    return 1 if hard else 0


if __name__ == "__main__":
    raise SystemExit(main())
