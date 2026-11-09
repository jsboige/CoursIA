#!/usr/bin/env python3
"""Verify every writing command in install-coursia-units.sh sits behind an icc_DRY_RUN guard.

#23342, acceptance criterion 4 : a control that goes red if an `install`/`systemctl`
writing command appears OUTSIDE an `icc_DRY_RUN` guard. The dry-run safety of a
UAC-touching installer rests entirely on every write site carrying
`[ "$icc_DRY_RUN" -eq 1 ] ||` before the command ; until now that was a one-off
line-by-line reading. This organ makes the invariant checkable. It is what
`scripts/ci/tests/test_coursia_units_dryrun.py` runs in CI, and re-runs against a
synthetic unguarded script as a positive control.

Read-only : it scans the script text, it never executes it.

A "writing command" is `install -m` (copies a file to the target) or a
state-changing `systemctl` subcommand (daemon-reload / restart / start / enable /
stop / mask). The read-only `systemctl is-enabled` / `is-active` calls and the
`command -v install|systemctl` presence checks are deliberately NOT writing.
Command text quoted inside a `log "..."` message is ignored (it is not executed).

Usage :
  check_coursia_units_write_guards.py [SCRIPT]

Exit 0 : every writing command is guarded.
Exit 1 : the script is missing, or at least one writing command is unguarded.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent / "docker/linux-runner/install-coursia-units.sh"

# Writing commands (matched on the line with quoted strings removed).
WRITE_PATTERNS = (
    re.compile(r"\binstall\s+-m\b"),
    re.compile(r"\bsystemctl\s+(?:daemon-reload|restart|start|enable|stop|mask)\b"),
)
# The guard a writing command must sit behind.
GUARD = re.compile(r'\[\s*"\$icc_DRY_RUN"\s+-eq\s+1\s*\]\s*\|\|')
QUOTES = re.compile(r'"[^"]*"')


def blank_code_spans(text: str) -> str:
    """Blank out `code` spans, including a span that crosses a newline (the
    usage() help wraps `systemctl restart` over two lines). A backtick toggles
    code-state; characters inside code-state become spaces. Newlines are
    preserved so the result splitlines() aligns with the source."""
    out: list[str] = []
    in_code = False
    for ch in text:
        if ch == "\n":
            out.append(ch)
        elif ch == "`":
            in_code = not in_code
            out.append(" ")
        elif in_code:
            out.append(" ")
        else:
            out.append(ch)
    if in_code:
        raise ValueError("unmatched backtick: source is not parseable")
    return "".join(out)


def writing_lines(text: str) -> list[tuple[int, str, bool]]:
    """`(lineno, stripped_line, guarded)` for every line that executes a write.

    A line counts only if, after blanking code spans and double-quoted strings,
    it still carries a write command -- i.e. the command is executed, not quoted
    in prose or in a `log "..."` message."""
    blanked = blank_code_spans(text).splitlines()
    out: list[tuple[int, str, bool]] = []
    for n, line in enumerate(text.splitlines(), 1):
        uq = QUOTES.sub("", blanked[n - 1])
        if any(p.search(uq) for p in WRITE_PATTERNS):
            out.append((n, line.strip(), bool(GUARD.search(line))))
    return out


def unguarded_writes(text: str) -> list[tuple[int, str]]:
    return [(n, s) for n, s, guarded in writing_lines(text) if not guarded]


def main(argv: list[str]) -> int:
    target = Path(argv[1]) if len(argv) > 1 else SCRIPT
    if not target.is_file():
        print(f"[write-guards] script absent : {target}", file=sys.stderr)
        return 1
    text = target.read_text(encoding="utf-8")
    try:
        bad = unguarded_writes(text)
    except ValueError as exc:
        print(f"[write-guards] source non parsable : {exc}", file=sys.stderr)
        return 1
    if bad:
        print(f"[write-guards] {len(bad)} commande(s) d'ecriture HORS garde icc_DRY_RUN :", file=sys.stderr)
        for n, line in bad:
            print(f"  l.{n}: {line}", file=sys.stderr)
        return 1
    total = len(writing_lines(text))
    print(f"[write-guards] OK : {total} site(s) d'ecriture, tous gardes par icc_DRY_RUN.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
