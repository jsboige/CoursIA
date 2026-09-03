#!/usr/bin/env python3
"""Check notebook link rendering in series READMEs.

Scans ``MyIA.AI.Notebooks/**/README.md`` and classifies each markdown link to a
``.ipynb`` file as one of:

* ``RENDU``  : a sibling ``.html`` exists locally (Quarto has rendered the notebook).
* ``BRUT``   : only the ``.ipynb`` exists locally (raw link, no local preview).
* ``MANQUE`` : neither the ``.ipynb`` nor any ``.html`` sibling exists (dangling).

The instrument is **diagnostic, not corrective**. The current root cause of the
high BRUT rate is ``_quarto.yml`` ``notebook-preview: false`` (which prevents
Quarto from rendering ``.ipynb`` files at all). Bulk replacement of links is a
composite change (G.4) and is **deliberately out of scope** for this tool —
strategy decisions (``notebook-preview: true`` vs. URLs to GitHub blob viewer)
belong to a follow-up epic PR, not an audit sweep.

Usage::

    python scripts/notebook_tools/check_notebook_link_render.py [path] [options]

    path                       root to scan (default: ``MyIA.AI.Notebooks``)
    --tracked-only             restrict to ``git ls-files`` intersection
    --json                     emit machine-readable JSON
    --verbose                  per-link verdicts on stdout
    --fail-on VERDICT          non-zero exit if any link matches VERDICT
                               (one of: RENDU, BRUT, MANQUE, ANY)
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import urllib.parse
from collections import Counter
from pathlib import Path

EXCLUDE_TOKENS = (".ipynb_checkpoints", "_archives", "/.git/")

LINK_PATTERN = re.compile(
    r"(?:\[[^\]]*\]\()([^\s)]+\.ipynb)(?:\)|\#)",
    re.IGNORECASE,
)


def tracked_files(root: Path) -> set[str] | None:
    """Posix paths (relative to CWD) of tracked files under ``root``.

    Returns ``None`` on ``git ls-files`` failure — caller falls back to scanning
    everything on disk.
    """
    try:
        out = subprocess.run(
            ["git", "ls-files", "--", str(root)],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True,
        ).stdout
    except (subprocess.CalledProcessError, OSError) as err:
        print(f"[!] git ls-files failed ({err}); scanning everything.",
              file=sys.stderr)
        return None
    return {Path(line).as_posix() for line in out.splitlines() if line}


def head_commit() -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return "?"


def classify_link(target: Path, repo_root: Path) -> str:
    """Classify a single resolved ``.ipynb`` link target.

    * ``RENDU``  if a sibling ``.html`` exists next to the ``.ipynb``.
    * ``MANQUE`` if the ``.ipynb`` itself does not exist (dangling).
    * ``BRUT``   otherwise — the ``.ipynb`` exists but no ``.html`` preview.
    """
    nb = target if target.suffix == ".ipynb" else target.with_suffix(".ipynb")
    if not nb.exists():
        return "MANQUE"
    html = nb.with_suffix(".html")
    if html.exists():
        return "RENDU"
    return "BRUT"


def extract_links(readme: Path, repo_root: Path, link_root: Path | None = None) -> list[dict]:
    """Extract ``.ipynb`` markdown links from a single README.

    Returns per-link records: ``link_text``, ``raw_target``, ``resolved`` (posix
    relative to CWD if inside repo, else absolute), ``verdict``.

    ``link_root`` controls how relative link paths are resolved: by default
    they are joined against the README's parent directory (markdown semantics).
    Passing an explicit ``link_root`` makes the checker resolve links against
    that directory instead — useful in CI when the README has been dumped to
    ``/tmp/`` and the real notebook files live in the repo.
    """
    try:
        text = readme.read_text(encoding="utf-8", errors="replace")
    except OSError as err:
        return [{"error": f"read failed: {err}", "verdict": "PARSE_ERROR"}]
    base = (link_root or readme.parent).resolve()
    records = []
    for match in LINK_PATTERN.finditer(text):
        raw = match.group(1)
        # Strip any URL fragment or query, then percent-decode (markdown links to
        # accented filenames often embed ``%C3%A9`` etc. — see SemanticKernel README).
        clean = urllib.parse.unquote(raw.split("#", 1)[0].split("?", 1)[0])
        # Resolve against ``base`` (markdown parent by default; override via link_root).
        candidate = (base / clean).resolve()
        try:
            relative = candidate.relative_to(repo_root.resolve()).as_posix()
        except ValueError:
            relative = candidate.as_posix()  # outside repo — surface absolute
        verdict = classify_link(candidate, repo_root)
        records.append({
            "link_text": raw,
            "resolved": relative,
            "verdict": verdict,
        })
    return records


def scan(target: Path, tracked_only: bool, repo_root: Path,
          link_root: Path | None = None) -> list[dict]:
    """Scan ``target`` recursively for README.md files and classify their links.

    ``link_root``, when provided, overrides the markdown-parent directory for
    resolving relative ``.ipynb`` link paths. See ``extract_links``.
    """
    if not target.exists():
        print(f"[!] target does not exist: {target}", file=sys.stderr)
        return []
    tracked = tracked_files(target) if tracked_only else None

    readmes = sorted(target.rglob("README.md")) if target.is_dir() else [target]
    out = []
    for readme in readmes:
        posix = readme.as_posix()
        if any(tok in posix for tok in EXCLUDE_TOKENS):
            continue
        if tracked is not None and posix not in tracked:
            continue
        links = extract_links(readme, repo_root, link_root)
        out.append({"readme": posix, "links": links})
    return out


def summarize(records: list[dict]) -> dict:
    """Global + per-README summary buckets. Verdicts: RENDU / BRUT / MANQUE."""
    per_readme = []
    global_counter: Counter[str] = Counter()
    readmes_with_links = 0
    readmes_100pct_brut = 0
    for entry in records:
        verdicts = [l.get("verdict") for l in entry["links"]]
        c = Counter(v for v in verdicts if v in {"RENDU", "BRUT", "MANQUE"})
        n_links = sum(c.values())
        if n_links:
            readmes_with_links += 1
            if c["RENDU"] == 0 and c["MANQUE"] == 0:
                readmes_100pct_brut += 1
        per_readme.append({
            "readme": entry["readme"],
            "n_links": n_links,
            "RENDU": c["RENDU"],
            "BRUT": c["BRUT"],
            "MANQUE": c["MANQUE"],
        })
        global_counter.update(c)
    return {
        "n_readmes_scanned": len(records),
        "n_readmes_with_links": readmes_with_links,
        "n_readmes_100pct_brut": readmes_100pct_brut,
        "totals": {
            "RENDU": global_counter["RENDU"],
            "BRUT": global_counter["BRUT"],
            "MANQUE": global_counter["MANQUE"],
        },
        "per_readme": per_readme,
    }


def emit_human(summary: dict, records: list[dict], verbose: bool, head: str) -> None:
    totals = summary["totals"]
    n_links = sum(totals.values())
    print(f"check_notebook_link_render @ {head}")
    print(f"  readmes scanned : {summary['n_readmes_scanned']}")
    print(f"  readmes w/ links: {summary['n_readmes_with_links']}")
    print(f"  100% BRUT       : {summary['n_readmes_100pct_brut']}")
    print(f"  totals          : {n_links} links")
    pct = lambda v: f"{(100.0 * v / n_links):5.1f}%" if n_links else "  0.0%"
    print(f"    RENDU  : {totals['RENDU']:5d}  {pct(totals['RENDU'])}")
    print(f"    BRUT   : {totals['BRUT']:5d}  {pct(totals['BRUT'])}")
    print(f"    MANQUE : {totals['MANQUE']:5d}  {pct(totals['MANQUE'])}")
    if not verbose:
        return
    for entry in records:
        if not entry["links"]:
            continue
        print(f"\n  {entry['readme']}")
        for link in entry["links"]:
            print(f"    [{link['verdict']:6s}] {link.get('resolved', link.get('link_text', '?'))}")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Classify notebook links in series READMEs as RENDU/BRUT/MANQUE.",
    )
    parser.add_argument(
        "path", nargs="?", default="MyIA.AI.Notebooks",
        help="root to scan (default: MyIA.AI.Notebooks)",
    )
    parser.add_argument(
        "--tracked-only", action="store_true",
        help="restrict to git ls-files intersection",
    )
    parser.add_argument(
        "--json", action="store_true",
        help="emit JSON instead of human-readable summary",
    )
    parser.add_argument(
        "--verbose", action="store_true",
        help="per-link verdicts on stdout (ignored with --json)",
    )
    parser.add_argument(
        "--fail-on", choices=("RENDU", "BRUT", "MANQUE", "ANY"), default=None,
        help="non-zero exit if any link matches this verdict",
    )
    parser.add_argument(
        "--link-root", default=None,
        help="resolve relative .ipynb links against this directory "
             "(default: the README's own parent). Useful in CI when the README "
             "has been dumped to /tmp/ and notebooks live in the real repo.",
    )
    args = parser.parse_args()

    repo_root = Path.cwd()
    target = Path(args.path)
    link_root = Path(args.link_root) if args.link_root else None
    records = scan(target, args.tracked_only, repo_root, link_root)
    summary = summarize(records)

    if args.json:
        print(json.dumps({
            "head": head_commit(),
            "target": target.as_posix(),
            "tracked_only": args.tracked_only,
            "link_root": link_root.as_posix() if link_root else None,
            "summary": summary,
            "records": records,
        }, indent=2, ensure_ascii=False))
    else:
        emit_human(summary, records, args.verbose, head_commit())

    if args.fail_on:
        totals = summary["totals"]
        threshold = sum(totals.values()) if args.fail_on == "ANY" else totals[args.fail_on]
        if threshold:
            print(f"[fail] {threshold} link(s) matched --fail-on {args.fail_on}",
                  file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
