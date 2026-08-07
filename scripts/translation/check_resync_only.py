#!/usr/bin/env python3
"""Detect "resync-only" PRs touching translations/**/*.csv without depositing
translations (#6949 second half, c.9717).

A "resync-only" PR satisfies BOTH:

1. ALL changed files match ``translations/**/*.csv`` (no notebook change, no
   script change, no doc change). A normal resync of T1 (extract) after an
   accent-cure campaign or a notebook rename lands exactly here.
2. NONE of the diff hunks add content in a ``text_<lang>`` or ``hash_<lang>``
   column for lang ∈ {en, es, ar, fa, zh, ru, pt} (the 7 target languages).
   Pure ``text_fr`` / ``hash_fr`` refresh (the source pivot) is allowed and is
   in fact the entire purpose of the resync.

Pattern measured on the 8 resync PRs that landed between 2026-07-21 and
2026-07-25 (#7577, #7695, #7772, #7773, #7806, #7916, #7949, #8431):
each one was a single CSV file with insertions ≈ deletions and zero
content in any non-fr column.

This script is a **CI advisory, non-blocking** by design. It codifies ai-01's
coordinator ruling of 2026-07-28 (issue #6949, see c.757 for context):
"plus de PR *resync-only* sur ``translations/**/*.csv`` jusqu'au GO moteur".
The ruling remains a coordinator decision — this advisory only surfaces it at
merge-gate review time so a human reviewer (or ai-01) can re-confirm the
intentionality of a resync against current policy.

Exit codes:
- 0: PR is NOT resync-only (or no diff to inspect).
- 0 with ``verdict: "resync_only"`` in the JSON: PR IS resync-only. CI prints
  a notice annotation; merge is **NOT** blocked (ai-01 policy).
- 2: usage error (CLI).

Stdlib-only (csv/json/subprocess/sys/pathlib/argparse/dataclasses).
Hermetic — does not call out to LLM, network, or filesystem outside the
provided ``--diff-range`` git invocation and the CSV headers (read inline).

Usage (CI):
    python scripts/translation/check_resync_only.py \
        --diff-range origin/main...HEAD

Usage (one-off, against a recorded range):
    python scripts/translation/check_resync_only.py \
        --diff-range origin/main...refs/pull/9842/head
"""

from __future__ import annotations

import argparse
import csv
import dataclasses
import io
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable

ALL_LANGS = ("en", "es", "ar", "fa", "zh", "ru", "pt")
PIVOT_LANG = "fr"

# ``translations/...csv`` paths only. Anything else (a notebook .ipynb, a
# script, a doc) breaks the "resync-only" verdict immediately.
TRANSLATIONS_RE = re.compile(r"^translations/.*\.csv$")


@dataclasses.dataclass
class FileDiff:
    """One file in a ``git diff --stat`` output."""

    path: str
    insertions: int
    deletions: int


@dataclasses.dataclass
class Report:
    """Advisory verdict for one PR."""

    diff_range: str
    changed_files: list[FileDiff]
    translations_only: bool
    lang_columns_added: list[str]  # empty = no translation content added
    verdict: str  # "resync_only" | "ok"
    policy_url: str = (
        "https://github.com/jsboige/CoursIA/issues/6949#issuecomment-2328497962"
    )

    def to_json(self) -> dict:
        return {
            "diff_range": self.diff_range,
            "changed_files": [dataclasses.asdict(f) for f in self.changed_files],
            "translations_only": self.translations_only,
            "lang_columns_added": self.lang_columns_added,
            "verdict": self.verdict,
            "policy_url": self.policy_url,
        }


# ---------------------------------------------------------------------------
# Git diff parsing
# ---------------------------------------------------------------------------

def _git_changed_files(diff_range: str) -> list[FileDiff]:
    """Run ``git diff --stat`` for the range and parse file-level changes.

    Lines look like::

        translations/planners/planners.csv | 394 +++---
        1 file changed, 394 insertions(+), 394 deletions(-)

    We only need ``path``, ``insertions``, ``deletions`` per file. We do not
    fail on renames (``=>``) because renames are not the target case.
    """
    proc = subprocess.run(
        ["git", "diff", "--stat", diff_range, "--"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git diff --stat {diff_range!r} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    files: list[FileDiff] = []
    for line in proc.stdout.splitlines():
        if not line or "|" not in line:
            continue
        # Skip summary line(s) ("N file(s) changed, ... +/-")
        if "file" in line.split("|", 1)[1] and "+/-" in line:
            continue
        left, right = line.split("|", 1)
        path = left.strip()
        right = right.strip()
        plus = right.count("+")
        minus = right.count("-")
        files.append(FileDiff(path=path, insertions=plus, deletions=minus))
    return files


def _git_added_lines(diff_range: str, paths: Iterable[str]) -> str:
    """Return the ``+``-side of the unified diff for the given paths.

    Useful to inspect which columns gained content. We use ``--diff-filter=AM``
    (Added + Modified) to ignore deletions (they cannot add a translation)
    and ``-U0`` to keep the diff terse.
    """
    cmd = [
        "git", "diff", "-U0", "--diff-filter=AM", diff_range, "--",
        *paths,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                          check=False)
    if proc.returncode != 0:
        raise RuntimeError(
            f"git diff -U0 --diff-filter=M {diff_range!r} failed "
            f"(exit {proc.returncode}): {proc.stderr.strip()}"
        )
    return proc.stdout


def _csv_columns() -> list[str]:
    """Canonical CSV header (single source of truth, see check_translation_sync)."""
    langs = list(ALL_LANGS)
    cols = [
        "notebook", "cell_id", "cell_type", "src_lang", "src_hash",
        "text_fr",
    ]
    cols += [f"text_{L}" for L in langs]
    cols += ["hash_fr"]
    cols += [f"hash_{L}" for L in langs]
    return cols


def _added_lang_columns(diff_text: str) -> list[str]:
    """Find which ``text_<lang>``/``hash_<lang>`` columns gained non-empty content.

    We accept the very first line of an added CSV row as evidence of "added
    translation content"; a same-row text_fr and text_en update counts as both
    fr (legitimate) and en (genuine translation), so this detector would
    correctly NOT flag it.

    The detector does NOT chase cell-level edits: it only checks whether the
    diff added any non-empty content in any non-fr column. That is sufficient
    to discriminate resync-only PRs (where columns 7-13 stay empty) from a
    genuine T3 deposit (which would add content in column 7+).
    """
    cols = _csv_columns()
    target_cols = {c for c in cols if c.startswith(("text_", "hash_"))
                   and not c.endswith(f"_{PIVOT_LANG}")}
    # We parse diff hunks. Each hunk starts with @@ -A,B +C,D @@, then ``+``
    # lines. CSV row lines start with a notebook path (contains ``.ipynb``)
    # followed by comma-separated quoted/unquoted fields.
    found: set[str] = set()
    hunk_re = re.compile(r"^\+\+\+\s", re.MULTILINE)
    if not hunk_re.search(diff_text):
        return []
    # Split per added hunk body (lines starting with ``+`` but NOT ``+++``).
    for line in diff_text.splitlines():
        if not line.startswith("+"):
            continue
        if line.startswith("+++"):  # hunk header
            continue
        body = line[1:]
        if not body:
            continue
        # CSV row — parse with stdlib csv on the body alone.
        try:
            row = next(csv.reader(io.StringIO(body)))
        except csv.Error:
            continue
        if len(row) != len(cols):
            continue  # malformed / header / not a row
        if row[0] == cols[0]:
            continue  # the canonical CSV header (its values ARE col names)
        for idx, col in enumerate(cols):
            if col in target_cols and row[idx].strip():
                found.add(col)
    return sorted(found)


# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------

def analyse(diff_range: str) -> Report:
    """Run the analysis and return a structured Report."""
    changed = _git_changed_files(diff_range)
    if not changed:
        return Report(
            diff_range=diff_range,
            changed_files=[],
            translations_only=False,
            lang_columns_added=[],
            verdict="ok",
        )
    translations_paths = [f.path for f in changed
                          if TRANSLATIONS_RE.match(f.path)]
    only_translations = bool(translations_paths) and len(translations_paths) == len(changed)
    if not only_translations:
        return Report(
            diff_range=diff_range,
            changed_files=changed,
            translations_only=False,
            lang_columns_added=[],
            verdict="ok",
        )
    diff_text = _git_added_lines(diff_range, translations_paths)
    added = _added_lang_columns(diff_text)
    verdict = "resync_only" if not added else "ok"
    return Report(
        diff_range=diff_range,
        changed_files=changed,
        translations_only=True,
        lang_columns_added=added,
        verdict=verdict,
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _format_notice(rep: Report) -> str:
    if rep.verdict == "ok":
        return ""
    paths = ", ".join(f.path for f in rep.changed_files)
    return (
        "::notice title=Translation resync-only::"
        f"This PR touches ONLY translations/**/*.csv ({paths}) "
        "and deposits no translation in any target language "
        "(en/es/ar/fa/zh/ru/pt). Per coordinator ruling on #6949 "
        "(2026-07-28), resync-only PRs are suspended until the T3 motor GO "
        "— a zero SRC_DRIFT on a 0%-translated table is non-informative "
        "(see #9431 for the fill-rate caveat). Confirm intentionality or "
        "wait for the motor. Non-blocking advisory."
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detect resync-only PRs touching translations/**/*.csv "
                    "(#6949 second half, advisory only)."
    )
    parser.add_argument(
        "--diff-range",
        default="origin/main...HEAD",
        help="Git diff range to inspect (default: origin/main...HEAD).",
    )
    parser.add_argument(
        "--json-only",
        action="store_true",
        help="Emit JSON only, no human-readable summary or ::notice.",
    )
    args = parser.parse_args(argv)
    try:
        rep = analyse(args.diff_range)
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(rep.to_json(), ensure_ascii=False))  # single-line, parseable
    if not args.json_only:
        print(json.dumps(rep.to_json(), ensure_ascii=False, indent=2),
              file=sys.stderr)
    if not args.json_only:
        print("", file=sys.stderr)
        if rep.verdict == "resync_only":
            print(_format_notice(rep), file=sys.stderr)
        else:
            print(
                f"Translation advisory OK: {len(rep.changed_files)} file(s), "
                f"translations_only={rep.translations_only}, "
                f"lang_columns_added={rep.lang_columns_added or 'none'}",
                file=sys.stderr,
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
