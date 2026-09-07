#!/usr/bin/env python3
"""Measure the phases of a ``quarto render`` run from a timestamped log.

Why this exists
---------------
Forensics on issue #14597 (2026-09-07) found that a Quarto site build has a
long SILENT phase between the last ``[N/M]`` document line and the
``Output created: _site/index.html`` line -- measured 2:56-5:50 on po-2024
docker runners and 11:27-15:09 on ai-01 docker runners, proportional to the
corpus (1252+ documents). That gap is invisible in the job log unless someone
manually diffs the raw-log timestamps of those two lines, which nobody does
until a run has already starved its ``PR gate`` (#13510) or hit the 60-min
ceiling (#14283).

``quarto-pages-deploy.yml`` therefore pipes ``quarto render`` through a bash
timestamping loop (``printf '%(%H:%M:%S)T'``) into ``render-timed.log``, and
this script turns that log into a phase table appended to the job summary:

- doc phase    : first timestamped line -> last ``[N/M]`` line
- post-render  : last ``[N/M]`` line    -> ``Output created`` line
                 (site assembly: search index over every page, manifests,
                 copied resources -- no per-document progress is printed)
- total        : first line -> ``Output created`` line

This is a measurement, not a gate: the script always exits 0 and reports
``not found`` for any marker absent from the log, so a Quarto log-format
change degrades the report rather than breaking the build.

Local usage
-----------
The same format is produced outside CI by::

    quarto render --to html 2>&1 \
      | awk '{ print strftime("%H:%M:%S"), $0; fflush() }' | tee render-timed.log
    python scripts/quarto_render_timing.py render-timed.log

(mawk lacks ``strftime``; gawk or the CI bash builtin loop are the portable
options).
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from datetime import datetime

TS_RE = re.compile(r"^(\d{2}:\d{2}:\d{2})\s?")
DOC_RE = re.compile(r"\[\s*(\d+)\s*/\s*(\d+)\s*\]")
OUTPUT_RE = re.compile(r"Output created:\s*(\S+)")


def _parse(ts: str) -> datetime:
    return datetime.strptime(ts, "%H:%M:%S")


def _fmt(delta: float) -> str:
    if delta < 0:  # %H:%M:%S wraps at midnight; renders crossing it are sub-hour
        delta += 86400
    seconds = int(round(delta))
    return f"{seconds // 60}:{seconds % 60:02d}"


def _physical_lines(raw: str) -> list[list[str]]:
    """Split raw log bytes into \\n-lines, each further split on \\r.

    Quarto's document-progress lines are \\r-separated segments riding inside
    one \\n-terminated line (ANSI color prefix, then ``\\r`` + one
    ``[  N/M]`` per document). Python text mode would translate those ``\\r``
    into newlines and divorce each progress segment from the line's timestamp
    prefix, so the file is decoded manually and segments stay grouped with
    their timestamp.
    """
    return [line.split("\r") for line in raw.split("\n")]


def analyse(raw: str) -> dict[str, object]:
    """Extract phase timestamps from a timestamped render log."""
    first_ts = None
    last_doc = None
    doc_count = None
    output_created = None
    site_path = None
    n_lines = 0
    for segments in _physical_lines(raw):
        ts = None
        for seg in segments:
            m = TS_RE.match(seg)
            if m:
                try:
                    ts = _parse(m.group(1))
                except ValueError:
                    continue
                break
        if ts is None:
            continue
        if first_ts is None:
            first_ts = ts
        n_lines += 1
        for seg in segments:
            m = DOC_RE.search(seg)
            if m:
                last_doc = (ts, seg.strip())
                doc_count = int(m.group(2))
            m = OUTPUT_RE.search(seg)
            if m and output_created is None:
                output_created = (ts, seg.strip())
                site_path = m.group(1)
    return {
        "first": first_ts,
        "last_doc": last_doc,
        "doc_count": doc_count,
        "output_created": output_created,
        "site_path": site_path,
        "n_lines": n_lines,
    }


def render_report(r: dict[str, object]) -> str:
    first = r["first"]
    last_doc = r["last_doc"]
    output_created = r["output_created"]
    doc_count = r["doc_count"]

    def phase(a, b):
        if a is None or b is None:
            return "not found"
        return _fmt((b - a).total_seconds())

    suffix = f" ({doc_count})" if doc_count else ""
    lines = [
        "### Quarto render phases (#14597)",
        "",
        "| phase | duration |",
        "|-------|----------|",
        f"| documents{suffix} | {phase(first, last_doc[0] if last_doc else None)} |",
        f"| post-render (silent) | {phase(last_doc[0] if last_doc else None, output_created[0] if output_created else None)} |",
        f"| total to `Output created` | {phase(first, output_created[0] if output_created else None)} |",
    ]
    if last_doc:
        lines.append("")
        lines.append(f"last document line: `{last_doc[1]}`")
    if output_created:
        lines.append(f"output: `{output_created[1]}`")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Report doc-phase vs post-render timings from a "
                    "timestamped `quarto render` log (measurement, never a gate).")
    ap.add_argument("log", help="path to the timestamped render log")
    args = ap.parse_args(argv)

    try:
        with open(args.log, "rb") as fh:
            raw = fh.read().decode("utf-8", errors="replace")
    except OSError as exc:
        print(f"quarto_render_timing: cannot read {args.log}: {exc}", file=sys.stderr)
        return 0

    report = render_report(analyse(raw))
    print(report)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as fh:
            fh.write(report + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
