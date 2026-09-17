#!/usr/bin/env python3
r"""Confront an umbrella/EPIC body with the repository BEFORE judging it actionable.

Context (#11900): the picker is the first gesture of every cycle, and it weights
*delassement* (days since last activity) to surface what the fleet neglects. But
the older an EPIC is, the more likely its body is false -- so the harder the
picker does its job, the more apparent dead-ends it raises. #11900 measured this
on two consecutive draws (#2874, #7357); both EPICs were fully actionable and
both blocking paragraphs had outlived their own resolution.

The cost is paid by every lane that draws the umbrella: it reads a body dated
from its writing, concludes "blocked on someone else", and re-shelves it. This
organ makes the mechanical half of that confrontation cheap, so the verdict is
measured rather than felt.

Two of the three surfaces #11900 names are decided mechanically:

  1. referenced CONTENT numbers (#N) -> resolve each one's kind and state. An
     EPIC whose every referenced child issue is CLOSED has nothing left to pick
     inside it: the picker offered a container, not a grain.
  2. cited FILE PATHS -> checked against the working tree. A body that points at
     a path which no longer exists is the #2874 signature (the lake moved to
     SymbolicAI/Lean/ and the body kept the old location).

The third surface -- a pending DECISION request -- is NOT machine-decidable: the
answer is usually in the first comment. This organ emits it as an explicit
manual step rather than guessing at it.

Verdicts:
    SATURATED   every referenced child issue is CLOSED (exit 1)
    FRESH       at least one referenced child issue is OPEN (exit 0)
    UNRESOLVED  the body references no child issue (exit 0, advisory)

Missing cited paths are reported as `warnings` and never decide the exit code:
a path may legitimately have moved, and a guard must not fabricate a red on a
signal it cannot interpret. Exit 1 is reserved for the one reading that is not
ambiguous -- an umbrella with every door closed.

Usage:
    python scripts/ci/check_umbrella_freshness.py <issue> [<issue> ...]
    python scripts/ci/check_umbrella_freshness.py <issue> --json
    python scripts/ci/check_umbrella_freshness.py <issue> --repo-root .

Unknown inputs (network failure, gh unavailable) exit 0 with verdict "unknown"
plus a ::warning -- infrastructure never forges a red (#14849).
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

REPO = "jsboige/CoursIA"

# This repository's oldest live content numbers are 3-digit (#221, #498, #833),
# so a 3-digit floor keeps them while dropping noise like "§12" or "PR #12".
REF_RE = re.compile(r"#(\d{3,6})")

# Backticked tokens that plausibly name a repository path. A path must contain a
# separator and be either a directory (trailing /) or carry an extension. Globs
# are excluded: their existence is not a yes/no question.
PATH_RE = re.compile(r"`([A-Za-z0-9_][A-Za-z0-9_./-]*/[A-Za-z0-9_./-]+)`")
EXT_RE = re.compile(r"\.[A-Za-z0-9]{1,6}$")


def extract_refs(body: str, self_number: int) -> list[int]:
    """Content numbers referenced by the body, self-reference removed."""
    seen: list[int] = []
    for match in REF_RE.finditer(body or ""):
        number = int(match.group(1))
        if number != self_number and number not in seen:
            seen.append(number)
    return seen


def extract_paths(body: str) -> list[str]:
    """Repository paths cited in backticks, globs and artefacts excluded."""
    found: list[str] = []
    for match in PATH_RE.finditer(body or ""):
        candidate = match.group(1)
        if "*" in candidate or "{" in candidate:
            continue
        if not candidate.endswith("/") and not EXT_RE.search(candidate):
            continue
        if candidate not in found:
            found.append(candidate)
    return found


def classify_ref(number: int, raw: dict | None) -> dict:
    """Normalise one GitHub issue/PR payload into kind + state."""
    if raw is None:
        return {"number": number, "kind": "unknown", "state": "UNKNOWN",
                "merged": False}
    pull = raw.get("pull_request")
    is_pr = isinstance(pull, dict)
    merged = bool(is_pr and pull.get("merged_at"))
    return {
        "number": number,
        "kind": "pr" if is_pr else "issue",
        "state": str(raw.get("state") or "").upper(),
        "merged": merged,
    }


def classify(refs: list[dict], missing_paths: list[str]) -> dict:
    """Apply the verdict rules. Pure: the caller supplies measured states."""
    issues = [r for r in refs if r["kind"] == "issue"]
    open_issues = [r for r in issues if r["state"] == "OPEN"]

    warnings = [
        f"cited path not found in the working tree: {path}"
        for path in missing_paths
    ]

    if issues and not open_issues:
        return {
            "verdict": "SATURATED",
            "reason": (
                f"all {len(issues)} referenced child issue(s) are CLOSED -- "
                "the umbrella has nothing left to pick inside it"
            ),
            "child_issues": len(issues),
            "child_open": 0,
            "warnings": warnings,
        }
    if open_issues:
        return {
            "verdict": "FRESH",
            "reason": (
                f"{len(open_issues)} of {len(issues)} referenced child issue(s) "
                "are OPEN"
            ),
            "child_issues": len(issues),
            "child_open": len(open_issues),
            "warnings": warnings,
        }
    return {
        "verdict": "UNRESOLVED",
        "reason": (
            "the body references no child issue -- mechanical verdict "
            "unavailable; read the comments for a pending decision (#11900 "
            "surface 3)"
        ),
        "child_issues": 0,
        "child_open": 0,
        "warnings": warnings,
    }


def _gh_json(args: list[str]) -> dict | None:
    try:
        proc = subprocess.run(
            ["gh", *args], capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def missing_paths(cited: list[str], repo_root: Path) -> list[str]:
    absent: list[str] = []
    for path in cited:
        target = repo_root / path.rstrip("/")
        if not target.exists():
            absent.append(path)
    return absent


def assess(number: int, repo_root: Path, repo: str) -> dict:
    payload = _gh_json(["api", f"repos/{repo}/issues/{number}"])
    if payload is None:
        return {"number": number, "verdict": "unknown", "warning":
                "gh unavailable or request failed", "refs": [], "warnings": []}

    body = payload.get("body") or ""
    numbers = extract_refs(body, number)
    refs = [
        classify_ref(n, _gh_json(["api", f"repos/{repo}/issues/{n}"]))
        for n in numbers
    ]
    cited = extract_paths(body)
    result = classify(refs, missing_paths(cited, repo_root))
    result["number"] = number
    result["title"] = payload.get("title") or ""
    result["refs"] = refs
    result["cited_paths"] = cited
    return result


def render_text(result: dict) -> str:
    lines = [f"#{result['number']}  {result['title']}"]
    lines.append(f"  verdict: {result['verdict']} -- {result['reason']}")
    for ref in result.get("refs", []):
        suffix = " (merged)" if ref["merged"] else ""
        lines.append(f"    #{ref['number']}  {ref['kind']}  {ref['state']}{suffix}")
    for warning in result.get("warnings", []):
        lines.append(f"    ! {warning}")
    if result["verdict"] == "SATURATED":
        lines.append("    -> do not pick here; the picker offered a container, "
                     "not a grain")
    if result["verdict"] == "UNRESOLVED":
        lines.append("    -> read `gh issue view N --comments` for a pending "
                     "decision before concluding the umbrella is blocked")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Confront an umbrella body with the repository (#11900).")
    parser.add_argument("issues", nargs="+", type=int)
    parser.add_argument("--repo", default=REPO)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    root = Path(args.repo_root).resolve()
    results = [assess(n, root, args.repo) for n in args.issues]

    if args.json:
        print(json.dumps(results, indent=2, ensure_ascii=False))
    else:
        for result in results:
            print(render_text(result))
            print()

    for result in results:
        if result["verdict"] == "unknown":
            print(f"::warning::#{result['number']} freshness unresolved "
                  f"({result.get('warning', 'unknown')})", file=sys.stderr)

    return 1 if any(r["verdict"] == "SATURATED" for r in results) else 0


if __name__ == "__main__":
    raise SystemExit(main())
