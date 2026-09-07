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

Runner-park occupation covariate (dispatch ai-01 2026-09-07)
------------------------------------------------------------
The post-render amplification (2:56 vs 15:09) correlated with WHEN the run
happened, not WHERE: the same runners show both regimes across days. The
surviving covariate is park OCCUPATION (busy/online at job start, cf #14429
19/22 busy during the slow window vs 0/28 during the fast one). The workflow
samples it in a FIRST step (before the ~20 min render -- the count must
describe the park when the job started, not when it finished)::

    python scripts/quarto_render_timing.py --sample-occupation occupation.json

then the report step merges it into the table and prints a one-line
machine-readable record (greppable across >=6 runs for the two regressions:
runner name vs occupation)::

    #14597-covariates: runner=...,busy=...,online=...,total=...,doc_s=...,post_s=...,total_s=...

Both paths degrade, never gate: an HTTP 403 or a missing occupation file
reports ``not sampled``/``na`` and the build stays green.

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
import json
import os
import re
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone

TS_RE = re.compile(r"^(\d{2}:\d{2}:\d{2})\s?")
DOC_RE = re.compile(r"\[\s*(\d+)\s*/\s*(\d+)\s*\]")
OUTPUT_RE = re.compile(r"Output created:\s*(\S+)")
LINK_NEXT_RE = re.compile(r'<([^>]+)>;\s*rel="next"')
MAX_RUNNER_PAGES = 10


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


def parse_runners_pages(pages: list[dict]) -> dict[str, int]:
    """Count total/online/busy across ``/actions/runners`` API pages."""
    runners = [r for page in pages for r in page.get("runners", [])]
    return {
        "total": len(runners),
        "online": sum(1 for r in runners if r.get("status") == "online"),
        "busy": sum(1 for r in runners if r.get("busy") is True),
    }


def sample_occupation(out_path: str) -> int:
    """Fetch the repo's self-hosted runner park now; write counts to OUT.

    Measurement, never a gate: any failure (missing token, HTTP error, bad
    JSON) still writes a JSON file carrying the error and exits 0, so the
    report step degrades to ``not sampled`` instead of redding the build.
    """
    api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
    repo = os.environ.get("GITHUB_REPOSITORY")
    token = os.environ.get("GITHUB_TOKEN")
    sampled = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    result: dict[str, object] = {"sampled_at": sampled}
    if repo and token:
        url = f"{api}/repos/{repo}/actions/runners?per_page=100"
        pages: list[dict] = []
        try:
            for _ in range(MAX_RUNNER_PAGES):
                req = urllib.request.Request(
                    url, headers={"Authorization": f"Bearer {token}",
                                  "Accept": "application/vnd.github+json"})
                with urllib.request.urlopen(req, timeout=15) as resp:
                    pages.append(json.loads(resp.read().decode("utf-8")))
                nxt = LINK_NEXT_RE.search(resp.headers.get("Link", "") or "")
                if not nxt:
                    break
                url = nxt.group(1)
            result.update(parse_runners_pages(pages))
        except (urllib.error.URLError, OSError, ValueError) as exc:
            result["error"] = str(exc)
    else:
        result["error"] = "GITHUB_REPOSITORY/GITHUB_TOKEN not set"
    try:
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(result, fh)
    except OSError as exc:
        print(f"quarto_render_timing: cannot write {out_path}: {exc}", file=sys.stderr)
    return 0


def load_occupation(path: str | None) -> dict[str, object] | None:
    """Read an occupation.json written by --sample-occupation; None if unusable."""
    if not path:
        return None
    try:
        with open(path, "r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else None
    except (OSError, ValueError):
        return None


def _secs(a: datetime | None, b: datetime | None) -> int | None:
    if a is None or b is None:
        return None
    delta = (b - a).total_seconds()
    if delta < 0:  # same midnight-wrap rule as _fmt
        delta += 86400
    return int(round(delta))


def render_report(r: dict[str, object],
                  occupation: dict[str, object] | None = None,
                  runner: str | None = None) -> str:
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
    if occupation and "busy" in occupation:
        lines.append(f"| park busy/online at start "
                     f"| {occupation['busy']}/{occupation['online']} (sampled {occupation.get('sampled_at', '?')}) |")
    else:
        lines.append("| park busy/online at start | not sampled |")
    if runner:
        lines.append(f"| runner | {runner} |")
    if last_doc:
        lines.append("")
        lines.append(f"last document line: `{last_doc[1]}`")
    if output_created:
        lines.append(f"output: `{output_created[1]}`")
    return "\n".join(lines)


def covariates_line(r: dict[str, object],
                    occupation: dict[str, object] | None,
                    runner: str | None) -> str:
    """One greppable record so >=6 runs can be harvested from job logs and
    regressed on BOTH covariates (runner identity vs park occupation)."""
    def or_na(value):
        return value if value is not None else "na"
    doc = _secs(r["first"], r["last_doc"][0] if r["last_doc"] else None)
    post = _secs(r["last_doc"][0] if r["last_doc"] else None,
                 r["output_created"][0] if r["output_created"] else None)
    total = _secs(r["first"], r["output_created"][0] if r["output_created"] else None)
    runner = (runner or "na").replace(",", ";").replace(" ", "-")
    if occupation and "busy" in occupation:
        busy, online, tot = occupation["busy"], occupation["online"], occupation["total"]
    else:
        busy = online = tot = "na"
    return (f"#14597-covariates: runner={runner},busy={busy},online={online},"
            f"total={tot},doc_s={or_na(doc)},post_s={or_na(post)},total_s={or_na(total)}")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Report doc-phase vs post-render timings from a "
                    "timestamped `quarto render` log (measurement, never a gate).")
    ap.add_argument("log", nargs="?", help="path to the timestamped render log")
    ap.add_argument("--sample-occupation", metavar="OUT",
                    help="instead of reporting, query the repo runner park now "
                         "and write busy/online counts to OUT (early workflow step)")
    ap.add_argument("--occupation", metavar="PATH",
                    help="occupation.json written by --sample-occupation "
                         "(merged into the report as the park covariate)")
    ap.add_argument("--runner-name", default=os.environ.get("RUNNER_NAME"),
                    help="runner identity for the covariate record "
                         "(defaults to $RUNNER_NAME)")
    args = ap.parse_args(argv)

    if args.sample_occupation:
        return sample_occupation(args.sample_occupation)
    if not args.log:
        ap.error("log path required unless --sample-occupation is given")

    try:
        with open(args.log, "rb") as fh:
            raw = fh.read().decode("utf-8", errors="replace")
    except OSError as exc:
        print(f"quarto_render_timing: cannot read {args.log}: {exc}", file=sys.stderr)
        return 0

    occupation = load_occupation(args.occupation)
    r = analyse(raw)
    report = render_report(r, occupation=occupation, runner=args.runner_name)
    print(report)
    print(covariates_line(r, occupation, args.runner_name))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as fh:
            fh.write(report + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
