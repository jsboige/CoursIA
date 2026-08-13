#!/usr/bin/env python3
"""check_harness_coauthor.py — detect stale `Co-Authored-By: Claude <Model> <ver>` in .claude/

Phase 2 of #10752 (harness stale templates). The convention (CLAUDE.md global
secGit line 27) prescribes `Co-Authored-By: Claude-Code <noreply@anthropic.com>`
without a model version. Two harness files (`skills/review-student-prs/SKILL.md`
+ `agents/notebook-iterative-builder.md`) were caught citing specific models
(`Claude Opus 4.6`, `Claude Sonnet 4.5`) that have not actually run since
the migration to Opus 5.x (cf c.1331+124-L1 lesson).

This guard makes the regression visible: any new `Co-Authored-By: Claude
(Opus|Sonnet|Haiku) [0-9]+.[0-9]+` in `.claude/**` fails the PR.

Tell (c.1331+124-L1): the canonical form is the literal substring
`Claude-Code` (no model name). A literal `Claude Sonnet 4.5` requires a
model name + version that an actual LLM ran under — anything else is a
stale label.

**Read-only** detector. The script does not modify any file. It produces a
JSON report consumable by `harness-coauthor-guard.yml` (the CI workflow).

Usage
-----

    # Standalone (developer-side):
    python scripts/notebook_tools/check_harness_coauthor.py [--paths PATH ...]

    # Programmatic:
    rc = check_harness_coauthor.scan(repo_root, paths=None)
    # rc == 0 if no stale references, 1 otherwise.

    # CI workflow:
    python scripts/notebook_tools/check_harness_coauthor.py --json
    # Outputs JSON to stdout, exit code follows findings.

Paths
-----

By default, scans `.claude/skills/`, `.claude/agents/`, `.claude/commands/`,
`.claude/rules/`. These are the directories where the convention is
enforced (cf CLAUDE.md global, .claude/**). The detector deliberately
excludes:

- `.claude/agent-memory/` : per-agent memory dumps, naturally free-form
- `.claude/local/` : per-machine local state, not under harness discipline
- `.claude/worktrees/` : transient worktree artifacts
- `.claude/plans/`, `.claude/progress/` : planning docs, not committable

Skip behavior follows the c.1331+107-L2 pattern (skip gracieux if scope
empty, never silently pass on a real failure).

JSON output
-----------

The `--json` flag emits a JSON report to stdout:

    {
      "scanned_paths": 4,
      "scanned_files": 17,
      "findings": [
        {
          "file": "skills/review-student-prs/SKILL.md",
          "line": 132,
          "match": "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>",
          "model": "Opus",
          "version": "4.6"
        }
      ],
      "total_findings": 1,
      "verdict": "STALE" | "CLEAN"
    }
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


# Pattern: catch Claude <Opus|Sonnet|Haiku> <major>.<minor> in Co-Authored-By.
# `Claude-Code` (the canonical form) does NOT match because it has no model
# token. Edge cases:
# - `Claude-3.5-Sonnet` (model name with version) is NOT matched here; this
#   pattern is targeted at the *trailer* identifier, not the model spec.
# - Whitespace between tokens is liberal (1+ spaces).
PATTERN = re.compile(
    r"Co-Authored-By:\s*Claude\s+(Opus|Sonnet|Haiku)\s+(\d+\.\d+)",
    re.IGNORECASE,
)

# Roots scanned by default. Each is scanned for *.md files (the convention
# applies to markdown harness surface; YAML/JSON are different surfaces).
DEFAULT_SCAN_ROOTS = (
    ".claude/skills",
    ".claude/agents",
    ".claude/commands",
    ".claude/rules",
)

# Roots explicitly excluded (cf top-of-file rationale).
EXCLUDED_SCAN_ROOTS = (
    ".claude/agent-memory",
    ".claude/local",
    ".claude/worktrees",
    ".claude/plans",
    ".claude/progress",
)


def scan(repo_root: Path, paths: list[str] | None = None) -> dict:
    """Scan the harness for stale Co-Authored-By trailers.

    Returns a JSON-compatible dict with findings + verdict. Does NOT throw on
    scan errors; instead, individual file errors are recorded as findings
    with a marker (so the CI run can report them).
    """
    if paths is None:
        roots = [repo_root / r for r in DEFAULT_SCAN_ROOTS]
    else:
        roots = [repo_root / p for p in paths]

    findings: list[dict] = []
    scanned_files = 0
    scanned_paths = 0

    for root in roots:
        if not root.exists():
            continue
        if any(str(root).startswith(str(repo_root / ex)) for ex in EXCLUDED_SCAN_ROOTS):
            continue
        scanned_paths += 1
        for md_file in sorted(root.rglob("*.md")):
            scanned_files += 1
            try:
                text = md_file.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                findings.append({
                    "file": str(md_file.relative_to(repo_root)),
                    "line": 0,
                    "match": f"<read-error: {exc!s}>",
                    "model": "unknown",
                    "version": "unknown",
                })
                continue
            for line_no, line in enumerate(text.splitlines(), start=1):
                m = PATTERN.search(line)
                if m:
                    findings.append({
                        "file": str(md_file.relative_to(repo_root)),
                        "line": line_no,
                        "match": line.strip(),
                        "model": m.group(1),
                        "version": m.group(2),
                    })

    verdict = "STALE" if findings else "CLEAN"
    return {
        "scanned_paths": scanned_paths,
        "scanned_files": scanned_files,
        "findings": findings,
        "total_findings": len(findings),
        "verdict": verdict,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument(
        "--repo-root",
        default=".",
        help="Repository root (default: current directory).",
    )
    parser.add_argument(
        "--paths",
        nargs="+",
        default=None,
        help="Specific paths to scan (relative to --repo-root). Overrides default scan roots.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON report to stdout.",
    )
    args = parser.parse_args()

    repo_root = Path(args.repo_root).resolve()
    report = scan(repo_root, args.paths)

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(f"Verdict: {report['verdict']}")
        print(f"Scanned paths: {report['scanned_paths']}")
        print(f"Scanned files: {report['scanned_files']}")
        print(f"Total findings: {report['total_findings']}")
        for f in report["findings"]:
            print(f"  {f['file']}:{f['line']} [{f['model']} {f['version']}] {f['match']}")

    # Exit 1 on stale references, 0 otherwise.
    # A broken detector (no scans ran) also exits 1 — c.1331+107-L2 pattern.
    return 1 if report["verdict"] == "STALE" else 0


if __name__ == "__main__":
    sys.exit(main())
