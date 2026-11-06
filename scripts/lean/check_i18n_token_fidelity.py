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
  must survive the translation. HARD finding. A **date** is compared as a
  *multiset of its parts*, so ``2026-10-27`` and ``27/10/2026`` match; any
  other numeric group is ONE literal, its decimal separator normalized
  (``1,5`` and ``1.5`` are the same number) but not split -- splitting it
  made ``1.5`` and ``5.1`` compare equal.
* **technical identifiers** outside code spans (camelCase, ``snake_case``,
  ``ALLCAPS``) -- a translation may legitimately rephrase such a mention, so
  these are ADVISORY.

Six mechanisms keep the measure from drowning in false positives:

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
  extra comment must not shift the comparison of every later comment. The
  anchor offset between the two sequences is measured (a constant shift) and
  the leftovers are repaired within a small tolerance of code tokens, so an
  alignment artefact is not published as an orphan;
* a **metadata header** is excluded, and the test reads the **bodies** of the
  pair: the ``_en`` header declares itself the mirror of the canonical file
  ("English mirror of ``Foo.lean``"), which has no FR counterpart **by
  design** -- the FR file carries its own translated docstring at the same
  code position. Comparing the two would report every metadata token of one
  side as the loss of the other;
* a number is excused only when it belongs to a **full date** on one side and
  the other side carries a full date too. The mere presence of a year
  somewhere in the body excuses nothing: that exemption hid 29 findings of
  the repository, among them plain arc counts.
* an **OK-CONSUMER** sibling is excluded wholesale, on the verdict of the
  sibling organ (``check_i18n_siblings.check_pair``): when the ``_en`` file
  ``import``s its FR canonical and reuses the declarations, the FR
  per-declaration docstrings have no EN counterpart by design, and comparing
  them would publish a false HARD finding for each one.

Every file reports its **coverage**: how many comment pairs were compared, how
many were excluded as headers, how many were repaired by alignment, and how
many are left unpaired. A file where no pair could be aligned says so
explicitly -- a "0 finding" on such a file means "nothing was measured", not
"nothing was wrong".

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
    check_pair,
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

# A fenced code block (``` ... ```) inside a comment. The fence carries an
# ODD number of backticks, so the inline scanner above pairs its closing
# fence with the NEXT opening one and swallows the prose in between: on a
# faithful mirror pair this manufactured 130 HARD findings (measured, review
# of #24143 -- ``Knots/Invariant``). A fenced block is CODE, not prose: the
# Lean code it carries is bound by the byte-identity contract of
# ``check_i18n_siblings``, and its comments are translated on purpose (five
# mirror pairs translate the comment inside the fence). It is therefore
# removed from the prose comparison.
_FENCED_BLOCK = re.compile(r"```.*?```", re.S)


def prose_only(body: str) -> str:
    """``body`` without its fenced code blocks."""
    return _FENCED_BLOCK.sub(" ", body)

# A numeric group: a digit run possibly made of several parts separated by a
# decimal/thousand/date separator (``2026-10-27``, ``27/10/2026``, ``1.5``).
_NUMBER_GROUP = re.compile(r"\d+(?:[.,/\-]\d+)*")

# The same group, but a separator may be followed by a space: a date written
# in the English convention ("April 7, 2026") is ONE group. The number
# extraction keeps the space out -- there "7, 2026" is a decimal pair, not a
# date.
_DATE_GROUP = re.compile(r"\d+(?:\s*[.,/\-]\s*\d+)*")

# The mirror declaration of an EN header: it says it is the mirror/sibling/
# companion of a canonical file. Such a comment has no FR counterpart BY
# DESIGN -- the FR file carries its own (translated) docstring at the same
# code position -- so comparing them would report every metadata token of
# one side as the loss of the other. This is the marker that tells the two
# apart. "sibling of" / "companion to" are recognized only when they name a
# .lean file: a bare "sibling" (e.g. the "(EN sibling)" tag on the title
# line) is too weak to single out a metadata header.
_MIRROR_DECLARATION = re.compile(
    r"\b(?:mirror\s+of|miroir\s+de)\b"
    r"|\b(?:sibling|companion)\s+(?:of|to)\s+[`\"']?[A-Za-z0-9_./\\-]*\.lean",
    re.I)

# A `### i18n` convention note: a comment (or a section of one) that documents
# the sibling-pair convention itself -- e.g. an option-A bilingual-inline
# module that explains WHY it deviates from the `_en` sibling rule. It is
# metadata about the file, not translatable content: the EN mirror owes it
# nothing, so it is excluded from the comparison (a false "loss" / "orphan"
# otherwise, control Conway/Doomsday.lean, review of #24148).
#
# Position-restricted (NanoClaw review of #24765): the plain-spelling phrase
# must HEAD a line -- the labeled note form (`Convention i18n (EPIC #4980,
# ...) : ...`, `i18n convention (EPIC #4980, ...): this root ...`) that 45+
# `_en.lean` files open on. A translatable prose line that merely MENTIONS the
# convention mid-sentence (`... docstrings traduites -- convention i18n #4980
# pattern A.`) no longer exempts the whole comment: under the old any-position
# motif it would silence a comment it never intended to classify. The `###`
# marker form stays any-position: a marked section header is explicit metadata.
_I18N_CONVENTION = re.compile(
    r"###\s*i18n\b"                                   # marked section header
    r"|^[^\S\n]*(?:--|/-!)?[^\S\n]*"                  # label form, heading a line
    r"(?:convention\s+i18n|i18n\s+convention)\b"
    r"|(?:convention\s+i18n|i18n\s+convention)\b[^\n]{0,20}?#4980",  # citation
    re.I | re.MULTILINE,
)

# The `EN sibling of `X.lean`` form of the same declaration: the EN header
# names the file it mirrors and carries metadata the FR header has no
# counterpart for (ratification date, issue ids, method note). It is a
# mirror header in the same sense as `English mirror of `X.lean`` -- but
# unlike that form, it may ALSO translate the FR header, so excluding it
# unconditionally would hide a real loss (see `compare_files`).
_SIBLING_DECLARATION = re.compile(
    r"\b(?:EN|english)\s+sibling\s+of\b", re.I)


def declares_sibling_mirror(fr_body: str, en_body: str) -> bool:
    """True when the EN body declares itself the sibling of the FR file.

    The FR body is checked too: when BOTH sides declare the sibling, they
    are two metadata headers and comparing them is meaningful.
    """
    return (bool(_SIBLING_DECLARATION.search(en_body))
            and not _SIBLING_DECLARATION.search(fr_body))


def drops_fr_token(findings: list) -> bool:
    """True when the findings report a token the FR side carries and the EN
    side does not -- a real loss of translation."""
    return any(f.get("severity") == HARD and f.get("side") == "FR"
               for f in findings)


def is_i18n_convention_block(body: str) -> bool:
    """True when ``body`` is, or embeds, a `### i18n` convention note.

    The plain-spelling phrase counts only in heading position (it starts a
    line of the comment); a mid-prose mention of the convention does not
    exempt the comment from the comparison.
    """
    return bool(_I18N_CONVENTION.search(body))


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
            start_line = line
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
            out.append((start_line, "doc" if is_doc else "block",
                        src[inner: j - 2], counter.count))
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
    for m in _CODE_SPAN.finditer(prose_only(body)):
        span = " ".join(m.group(1).split())
        if span:
            out.append(span)
    return out


def number_parts(body: str) -> list[str]:
    """The numeric literals of ``body``, code spans excluded.

    A group that carries a four-digit year is a DATE: it is split on its
    separators, so ``2026-10-27`` and ``27/10/2026`` contribute the same
    parts ``2026``, ``10`` and ``27`` -- a date reads the same whether it
    is written in one format or another.

    Any other group is split on its SLASH and its DASH (a ratio ``0/1``, a
    range ``65-979``) but its decimal separator is NOT a separator: ``1,5``
    and ``1.5`` are one number written in the two conventions. Splitting
    the decimal made ``1.5`` and ``5.1`` compare equal, because the parts
    of both are ``{1, 5}`` (measured, review of #24148).
    """
    stripped = _CODE_SPAN.sub(" ", prose_only(body))
    parts: list[str] = []
    for m in _NUMBER_GROUP.finditer(stripped):
        raw = m.group(0)
        pieces = [p for p in re.split(r"[.,/\-]", raw) if p]
        if any(len(p) == 4 for p in pieces):
            parts.extend(pieces)
        else:
            for piece in re.split(r"[/\-]", raw):
                piece = piece.replace(",", ".")
                if piece:
                    parts.append(piece)
    return parts


def date_groups(body: str) -> list[list[str]]:
    """The numeric groups of ``body`` that spell a FULL date.

    A full date carries at least two components and one of them is a
    four-digit year: ``2026-10-27``, ``27/10/2026``, ``7, 2026``. A bare
    year (``2026``) is not a date -- it is the mere presence of a year
    that used to excuse every small number of the other side (measured:
    29 findings of the repository rested on that exemption, review of
    #24148).
    """
    out: list[list[str]] = []
    stripped = _CODE_SPAN.sub(" ", prose_only(body))
    for m in _DATE_GROUP.finditer(stripped):
        pieces = [p.strip() for p in re.split(r"[.,/\-]", m.group(0)) if p.strip()]
        if len(pieces) >= 2 and any(len(p) == 4 for p in pieces):
            out.append(pieces)
    return out


# The words that carry a small number in a translation, in both languages.
# The FR side may spell it in French ("nul", "zéro", "deux"); the EN side in
# English ("zero", "two"). Both spell the same small number, so a number the
# other side carries in words is not a loss. The list was English-only in the
# original, which made every faithful "FR word / EN digit" pair a false HARD
# (measured: 41 findings, tokens 0-6, review of #24148). 17-19 stay English
# only: their French forms are compound ("dix-sept") and were not in the
# measured class. "un"/"une" is deliberately NOT a word for 1: it is the
# common French article, and matching it would excuse every "1" of a file.
_NUMBER_WORDS = {
    0: ["zero", "zéro", "nul", "nulle"],
    1: ["one"],
    2: ["two", "deux"],
    3: ["three", "trois"],
    4: ["four", "quatre"],
    5: ["five", "cinq"],
    6: ["six"],
    7: ["seven", "sept"],
    8: ["eight", "huit"],
    9: ["nine", "neuf"],
    10: ["ten", "dix"],
    11: ["eleven", "onze"],
    12: ["twelve", "douze"],
    13: ["thirteen", "treize"],
    14: ["fourteen", "quatorze"],
    15: ["fifteen", "quinze"],
    16: ["sixteen", "seize"],
    17: ["seventeen"],
    18: ["eighteen"],
    19: ["nineteen"],
    20: ["twenty", "vingt"],
}


def number_is_carried_elsewhere(part: str, other_body: str,
                                own_body: str | None = None) -> bool:
    """True when the other side carries the number in another form.

    Two mitigations keep the number class from drowning in false positives:
    a translation may spell a small number in words ("one" for ``1``), and it
    may express a date differently ("April 7, 2026" for ``2026-04-07``).

    The date mitigation asks for a DATE NEIGHBOURHOOD, not for the presence
    of a year somewhere in the body: the number must belong to a full date
    of the other side, or to a full date of this side whose counterpart the
    other side spells in another convention. A bare year excuses nothing
    (measured: the arc counts of the repository rested on that exemption,
    review of #24148).
    """
    if not part.isdigit():
        return False
    value = int(part)
    words = _NUMBER_WORDS.get(value)
    if words and any(
        re.search(r"\b%s\b" % re.escape(w), other_body, re.IGNORECASE)
        for w in words
    ):
        return True
    other_dates = date_groups(other_body)
    for pieces in other_dates:
        if part in pieces:
            return True
    if own_body:
        for pieces in date_groups(own_body):
            if part in pieces and other_dates:
                return True
    return False


def technical_identifiers(body: str) -> set[str]:
    """The technical identifiers mentioned in ``body`` outside code spans."""
    stripped = _CODE_SPAN.sub(" ", prose_only(body))
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
                   decls: set[str] | None = None,
                   is_module: bool = False) -> list[dict]:
    """Compare one FR/EN comment-body pair; return the list of findings.

    ``is_module`` marks a pair that is the file's MODULE docstring (the
    top-of-file summary). A summary legitimately diverges between the FR and
    EN twins in wording and in WHICH cross-references it carries (declaration
    names, issue / arXiv ids, section numbers): the byte-identity contract
    binds the code, not the summary prose. So in a module docstring a
    divergent code-span or number is advisory, not a hard loss (control
    ``Generators_en.lean``, review of #24148).
    """
    decls = decls or set()
    findings: list[dict] = []
    drop_fr, drop_en = designation_exemptions(fr_body, en_body)

    fr_spans = {collapse_en(s) for s in code_spans(fr_body)} - {
        collapse_en(s) for s in drop_fr}
    en_spans = {collapse_en(s) for s in code_spans(en_body)} - {
        collapse_en(s) for s in drop_en}

    for span in sorted(fr_spans - en_spans):
        findings.append({"severity": span_severity(span, decls, is_module),
                         "kind": "code-span", "token": span, "side": "FR"})
    for span in sorted(en_spans - fr_spans):
        findings.append({"severity": span_severity(span, decls, is_module),
                         "kind": "code-span", "token": span, "side": "EN"})

    # In a module docstring a divergent number is a summary difference, not a
    # loss: it is advisory (see ``is_module`` above).
    num_severity = ADVISORY if is_module else HARD
    fr_nums = Counter(number_parts(fr_body))
    en_nums = Counter(number_parts(en_body))
    for num, count in sorted((fr_nums - en_nums).items()):
        if number_is_carried_elsewhere(num, en_body, fr_body):
            continue
        findings.append({"severity": num_severity, "kind": "number",
                         "token": num, "side": "FR"})
    for num, count in sorted((en_nums - fr_nums).items()):
        if number_is_carried_elsewhere(num, fr_body, en_body):
            continue
        findings.append({"severity": num_severity, "kind": "number",
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


def span_severity(span: str, decls: set[str], is_module: bool = False) -> str:
    """A dropped span is HARD when it names a declaration of the file.

    In a module docstring the summary may legitimately name a different
    subset of the module's declarations on each side, so a declaration
    reference is advisory there (control ``Generators_en.lean``, #24148).
    """
    if is_module:
        return ADVISORY
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


# The tolerance of the anchor pairing, in code tokens. The EN mirror adds
# its `_en` imports and its `_en` namespace, which shifts the code position
# of the comments that follow: a comment whose counterpart sits a few
# tokens away is an ALIGNMENT ARTEFACT, not an orphan comment.
ANCHOR_TOLERANCE = 3


def is_mirror_metadata_header(fr_body: str, en_body: str) -> bool:
    """True when the EN body is a mirror header and the FR body is not.

    The EN header of a mirror states its own metadata ("English mirror of
    `X.lean` (FR-first canonical, tranche N EPIC #4980, <date>)"): it has no
    FR counterpart BY DESIGN, because the FR file carries its own docstring
    at the same code position. Comparing the two would report every
    metadata token of one side as the loss of the other.

    The test therefore reads the BODIES of the pair, not the position of
    its anchor. Excluding the lowest shared anchor whatever it is dropped
    real translation checks: measured on the repository, 94 files lost a
    HARD finding that way (review of #24148).

    When BOTH sides declare the mirror, they are two metadata headers and
    comparing them is meaningful: the exclusion does not apply.
    """
    return (bool(_MIRROR_DECLARATION.search(en_body))
            and not _MIRROR_DECLARATION.search(fr_body))


def pair_comments(fr_comments: list, en_comments: list, shift: int,
                  tol: int = ANCHOR_TOLERANCE):
    """Pair the FR and EN comments by code anchor.

    Two passes: an exact pass (the counterpart sits at ``anchor + shift``)
    then a repair pass for the leftovers (the counterpart sits within
    ``tol`` code tokens). The repair pass never breaks an exact pair and
    keeps the order of the two sequences.

    Returns ``(pairs, orphans_fr, orphans_en, repaired)``: the pairs are
    ``(fr_group, en_group, fr_anchor)``, the orphans are the comments that
    have no counterpart at all.
    """
    fr_by: dict[int, list] = {}
    for c in fr_comments:
        fr_by.setdefault(c[3], []).append(c)
    en_by: dict[int, list] = {}
    for c in en_comments:
        en_by.setdefault(c[3], []).append(c)
    fr_anchors = sorted(fr_by)
    en_anchors = sorted(en_by)

    pairs: list[tuple] = []
    matched_fr: set[int] = set()
    matched_en: set[int] = set()

    # exact pass
    i = j = 0
    while i < len(fr_anchors) and j < len(en_anchors):
        fa, ea = fr_anchors[i], en_anchors[j]
        if fa + shift == ea:
            pairs.append((fr_by[fa], en_by[ea], fa))
            matched_fr.add(fa)
            matched_en.add(ea)
            i += 1
            j += 1
        elif fa + shift < ea:
            i += 1
        else:
            j += 1

    # repair pass: the leftovers whose counterpart is a few tokens away
    left_fr = [a for a in fr_anchors if a not in matched_fr]
    left_en = [b for b in en_anchors if b not in matched_en]
    repaired = 0
    i = j = 0
    while i < len(left_fr) and j < len(left_en):
        fa, ea = left_fr[i], left_en[j]
        delta = (ea - shift) - fa
        if delta < -tol:
            j += 1
        elif delta > tol:
            i += 1
        else:
            pairs.append((fr_by[fa], en_by[ea], fa))
            matched_fr.add(fa)
            matched_en.add(ea)
            repaired += 1
            i += 1
            j += 1

    orphans_fr = [c for a in left_fr if a not in matched_fr for c in fr_by[a]]
    orphans_en = [c for b in left_en if b not in matched_en for c in en_by[b]]
    pairs.sort(key=lambda p: p[2])
    return pairs, orphans_fr, orphans_en, repaired


def compare_files(fr_path: Path, en_path: Path) -> dict:
    """Compare the FR canonical and its EN mirror; return a pair report."""
    fr_src = fr_path.read_text(encoding="utf-8", errors="replace")
    en_src = en_path.read_text(encoding="utf-8", errors="replace")

    # OK-CONSUMER sibling: the EN file ``import``s the FR module and reuses its
    # declarations instead of redeclaring them, so the FR canonical's
    # per-declaration docstrings have **no EN counterpart by design**. Paired
    # positionally, the organ would report every one of them as a loss -- a
    # wall of HARD findings that is an artefact of the shape, not a translation
    # gap. The sibling organ (``check_i18n_siblings.check_pair``) already
    # classifies exactly this shape as ``"OK-CONSUMER"``; we reuse that verdict
    # (single source of truth) and skip the comparison for such a pair.
    if check_pair(fr_path, en_path)[0] == "OK-CONSUMER":
        return {
            "fr": str(fr_path),
            "en": str(en_path),
            "ok_consumer": True,
            "fr_comments": 0,
            "en_comments": 0,
            "anchor_shift": 0,
            "pairs_repaired": 0,
            "pairs_compared": 0,
            "pairs_excluded": 0,
            "pairs": [],
            "unpaired": [],
            "findings": [],
        }

    fr_comments = scan_comments(fr_src)
    en_comments = scan_comments(en_src)
    decls = declaration_names(fr_src) | declaration_names(en_src)

    # The module docstring is the file's first (lowest-anchor) block-doc
    # comment. A pair whose FR or EN side is that docstring is a summary,
    # compared as such (see ``compare_bodies`` / ``is_module``).
    fr_module_anchor = min((c[3] for c in fr_comments if c[1] == "doc"),
                           default=None)
    en_module_anchor = min((c[3] for c in en_comments if c[1] == "doc"),
                           default=None)

    shift = _best_shift({c[3] for c in fr_comments},
                        {c[3] for c in en_comments})
    raw_pairs, orphans_fr, orphans_en, repaired = pair_comments(
        fr_comments, en_comments, shift)

    pairs: list[dict] = []
    unpaired: list[dict] = []
    compared = 0
    excluded = 0
    for fr_group, en_group, anchor in raw_pairs:
        for k in range(max(len(fr_group), len(en_group))):
            if k < len(fr_group):
                fr_line, fr_kind, fr_body, fr_anchor = fr_group[k]
            else:
                fr_line, fr_kind, fr_body, fr_anchor = (0, "-", "", None)
            if k < len(en_group):
                en_line, en_kind, en_body, en_anchor = en_group[k]
            else:
                en_line, en_kind, en_body, en_anchor = (0, "-", "", None)
            # A pair whose side is the module docstring is a summary, not
            # translatable content: its cross-references are advisory.
            is_module = (fr_anchor == fr_module_anchor
                         or en_anchor == en_module_anchor)
            # A mirror header or a `### i18n` convention note has no
            # counterpart by design: exclude it from the comparison.
            is_header = (is_mirror_metadata_header(fr_body, en_body)
                         or is_i18n_convention_block(fr_body)
                         or is_i18n_convention_block(en_body))
            sibling = False
            pair_excluded = False
            if fr_body and en_body:
                sibling = declares_sibling_mirror(fr_body, en_body)
                # The findings are needed only when the pair is COMPARED, or
                # to decide whether a `sibling` header drops a FR token. A
                # plain mirror header (excluded by design) never needs them:
                # computing them for every excluded header doubled the work
                # over the whole `--all` corpus (188 excluded pairs out of
                # 9541, measured on the repository; review of #24591).
                if sibling or not is_header:
                    findings = compare_bodies(fr_body, en_body, decls,
                                              is_module=is_module)
                    # A `EN sibling of `X`` header is a mirror header too, but
                    # only when it drops NOTHING the FR side carries: a
                    # header that also translates the FR summary and loses a
                    # token holds a real loss, and stays compared.
                    # The sibling branch is evaluated FIRST, so a body
                    # carrying BOTH declarations and dropping a FR token is
                    # reported rather than excluded: the exclusion must
                    # never hide a real loss (review of #24591).
                    if sibling and drops_fr_token(findings):
                        compared += 1
                    elif is_header or sibling:
                        excluded += 1
                        findings = []
                        pair_excluded = True
                    else:
                        compared += 1
                else:
                    # Plain mirror header: excluded by design, no comparison
                    # performed.
                    findings = []
                    excluded += 1
                    pair_excluded = True
            else:
                findings = []
            pair = {
                "index": len(pairs) + 1,
                "anchor": anchor,
                "fr_line": fr_line,
                "en_line": en_line,
                "fr_kind": fr_kind,
                "en_kind": en_kind,
                "excluded": pair_excluded,
                "findings": findings,
            }
            pairs.append(pair)

    for line, kind, body, anchor in orphans_fr:
        # A `### i18n` convention note is metadata, not a lost comment: the
        # EN mirror owes it nothing (control Conway/Doomsday.lean, #24148).
        if is_i18n_convention_block(body):
            continue
        unpaired.append({"severity": ADVISORY, "kind": "unpaired-comment",
                         "side": "FR", "line": line, "anchor": anchor,
                         "body": body.strip()[:120]})
    for line, kind, body, anchor in orphans_en:
        # A mirror header has no FR counterpart by design: it is a header,
        # not an orphan comment. A `### i18n` note is metadata, same reason.
        if (_MIRROR_DECLARATION.search(body)
                or _SIBLING_DECLARATION.search(body)
                or is_i18n_convention_block(body)):
            continue
        unpaired.append({"severity": ADVISORY, "kind": "unpaired-comment",
                         "side": "EN", "line": line, "anchor": anchor,
                         "body": body.strip()[:120]})

    report = {
        "fr": str(fr_path),
        "en": str(en_path),
        "fr_comments": len(fr_comments),
        "en_comments": len(en_comments),
        "anchor_shift": shift,
        "pairs_repaired": repaired,
        "pairs_compared": compared,
        "pairs_excluded": excluded,
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
    pairs_with_finding = 0
    compared_total = 0
    for rep in reports:
        all_findings = list(rep["findings"]) + list(rep.get("unpaired", []))
        compared_total += rep.get("pairs_compared", 0)
        pairs_with_finding += sum(1 for p in rep["pairs"] if p["findings"])
        if (not all_findings and not rep.get("count_mismatch")
                and rep.get("pairs_compared", 0) > 0):
            continue
        lines.append("TOKEN-FIDELITY  %s" % rep["en"])
        lines.append(
            "  coverage: %d comment pair(s) compared, %d excluded (mirror header),"
            " %d repaired by alignment, %d unpaired"
            % (rep.get("pairs_compared", 0), rep.get("pairs_excluded", 0),
               rep.get("pairs_repaired", 0), len(rep.get("unpaired", []))))
        if rep.get("pairs_compared", 0) == 0:
            # "0 finding" here does not mean "faithful": nothing was measured.
            lines.append(
                "  NOTHING COMPARED: no comment pair could be aligned --"
                " a '0 finding' on this file means 'nothing was measured'")
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
            if shown >= max_per_file:
                continue
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
        "SUMMARY  %d file(s) | %d comment pair(s) compared | %d pair(s) with a"
        " finding | %d hard | %d advisory"
        % (len(reports), compared_total, pairs_with_finding, hard, advisory))
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
