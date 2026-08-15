#!/usr/bin/env python3
"""Per-PR advisory detector: a body invoking a .NET execution-block dispense
on a notebook that contains zero ``#r "nuget:"`` references.

Why this exists -- issue #10024 Livrable 2 (the organ).
``docs/reference/kernels-runtime.md`` documents that the headless ``#r "nuget:"``
restore is blocked cluster-wide ([dotnet-headless-nuget-restore-cluster-wide-blocker]).
That blocker is REAL but BOUNDED: it applies only to notebooks that actually
contain a ``#r "nuget:"`` cell. The dispense was repeatedly invoked as a blanket
excuse to skip re-execution or to transplant outputs from outside the repo -- on
notebooks that contained NO ``#r "nuget:"`` at all. PR #10021 is the canonical
case: ``RECOVERABLE-MACHINE`` verdict + outputs transplanted from an uncommitted
console project, for ``App-13b`` (0 ``#r "nuget:"``) -- the form of a falsified
execution proof.

This detector makes that anti-pattern VISIBLE. It is **advisory** (always exits
0): the actionable signal is the ``dotnet-block-without-nuget`` LABEL posed by
the workflow, never the exit code. A reviewer reading "exit 0" as "conforming"
reads the wrong signal -- the same trap documented in exercises-advisory.yml.

Falsifiability (acceptance: >=2 silence tests, [gate-must-verify-detector-fp-before-wiring]):
  - a .NET notebook WITH ``#r "nuget:"`` + body invoking the block -> SILENT
    (the block may be legitimate: nuget restore genuinely can hang headless).
  - a .NET notebook WITHOUT nuget and a body NOT invoking the block -> SILENT.
  - a non-.NET notebook -> out of scope, SILENT.
The reference case that must ROUGE: PR #10021 body on App-13b (0 nuget).

Usage (mirrors check_pr_exercises.py):

    python check_pr_dotnet_nuget_block.py --paths App-13b.ipynb --pr-body-file body.md --json
    git diff --name-only BASE HEAD -- '*.ipynb' | python check_pr_dotnet_nuget_block.py --stdin --pr-body-file body.md --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

LABEL_NAME = "dotnet-block-without-nuget"

# Keywords that signal a .NET execution-block dispense in a PR body. The flag
# fires only when the modified notebook has 0 ``#r "nuget:"``, so listing
# "nuget" here is self-consistent (a body mentioning nuget + a notebook with no
# nuget reference = the suspicious combination). Case-insensitive.
BLOCK_KEYWORDS: tuple[str, ...] = (
    "recoverable-machine",
    "headless",
    "non-executable",
    "non-exec",
    "pas executable",
    "pas execut",
    "transplant",
    "nuget",
)

# Matches ``#r "nuget:...`` in cell source (after JSON parse, quotes are real).
# Tolerates whitespace variants: ``#r "nuget:...``, ``#r  "nuget: ...``.
NUGET_REF_RE = re.compile(r'#r\s+"nuget\s*:', re.IGNORECASE)


def _is_dotnet_kernel(nb: dict) -> bool:
    """True if the notebook's kernelspec name starts with ``.net``."""
    name = (
        nb.get("metadata", {})
        .get("kernelspec", {})
        .get("name", "")
        .strip()
        .lower()
    )
    return name.startswith(".net")


def _count_nuget_refs(nb: dict) -> int:
    """Count ``#r "nuget:"`` occurrences across ALL cell sources."""
    total = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        source = cell.get("source", [])
        text = "".join(source) if isinstance(source, list) else str(source)
        total += len(NUGET_REF_RE.findall(text))
    return total


def _find_block_keywords(body: str) -> list[str]:
    """Return the (lowercased, de-duplicated, order-preserving) block keywords
    found in the PR body. Empty list if the body does not invoke a block."""
    if not body:
        return []
    low = body.lower()
    found: list[str] = []
    seen: set[str] = set()
    for kw in BLOCK_KEYWORDS:
        if kw in low and kw not in seen:
            seen.add(kw)
            found.append(kw)
    return found


def check_pr(paths: list[str], body: str) -> dict:
    """Inspect each notebook path + the PR body. Return the JSON payload.

    A notebook is FLAGGED iff ALL hold:
      1. it parses as a valid .ipynb with a ``.net*`` kernelspec,
      2. it contains 0 ``#r "nuget:"`` references,
      3. the PR body invokes >=1 block keyword.
    """
    body_keywords = _find_block_keywords(body)
    body_invokes_block = len(body_keywords) > 0

    notebooks_out: list[dict] = []
    dotnet_checked = 0
    dotnet_with_nuget = 0
    flagged = 0

    for raw_path in paths:
        raw_path = raw_path.strip()
        if not raw_path or not raw_path.endswith(".ipynb"):
            continue
        p = Path(raw_path)
        entry: dict = {"path": raw_path}
        if not p.is_file():
            entry.update({"status": "missing", "flagged": False})
            notebooks_out.append(entry)
            continue
        try:
            nb = json.loads(p.read_text(encoding="utf-8"))
        except (OSError, ValueError) as exc:
            entry.update({"status": f"unparseable: {exc}", "flagged": False})
            notebooks_out.append(entry)
            continue
        if not _is_dotnet_kernel(nb):
            entry.update(
                {
                    "status": "non-dotnet",
                    "kernel": nb.get("metadata", {})
                    .get("kernelspec", {})
                    .get("name", "?"),
                    "flagged": False,
                }
            )
            notebooks_out.append(entry)
            continue

        dotnet_checked += 1
        nuget_count = _count_nuget_refs(nb)
        entry.update(
            {
                "status": "ok",
                "kernel": nb.get("metadata", {})
                .get("kernelspec", {})
                .get("name", "?"),
                "nuget_count": nuget_count,
                "flagged": False,
            }
        )
        if nuget_count > 0:
            dotnet_with_nuget += 1
            # Legitimate block context: the nuget blocker genuinely can apply.
            entry["reason"] = "has #r nuget -- block may be legitimate (SILENT)"
        elif not body_invokes_block:
            entry["reason"] = "no nuget but body does not invoke a block (SILENT)"
        else:
            # The anti-pattern: 0 nuget + body invokes a blocker dispense.
            entry["flagged"] = True
            entry["body_block_keywords"] = body_keywords
            entry[
                "reason"
            ] = "0 #r nuget but body invokes a .NET exec block -- likely RECOVERABLE-LOCAL, re-exec for real"
            flagged += 1
        notebooks_out.append(entry)

    return {
        "summary": {
            "dotnet_block_without_nuget": flagged,
            "dotnet_notebooks_checked": dotnet_checked,
            "dotnet_notebooks_with_nuget": dotnet_with_nuget,
            "body_invokes_block": body_invokes_block,
            "body_keywords_found": body_keywords,
        },
        "notebooks": notebooks_out,
    }


def _collect_paths(path_args: list[str], from_stdin: bool) -> list[str]:
    paths = list(path_args or [])
    if from_stdin:
        for line in sys.stdin:
            line = line.strip()
            if line:
                paths.append(line)
    # De-duplicate while preserving order.
    seen: set[str] = set()
    out: list[str] = []
    for p in paths:
        if p not in seen:
            seen.add(p)
            out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Advisory detector for the .NET exec-block-without-nuget anti-pattern "
            "(#10024 Livrable 2). Always exits 0 (advisory): the signal is the "
            f"'{LABEL_NAME}' label, not this exit code."
        ),
    )
    parser.add_argument(
        "--paths", nargs="*", default=[],
        help="Notebook paths modified by the PR.",
    )
    parser.add_argument(
        "--stdin", action="store_true",
        help="Also read paths from stdin (one per line; e.g. git diff output).",
    )
    parser.add_argument(
        "--pr-body-file", dest="pr_body_file", default=None,
        help="Path to a file containing the PR body text.",
    )
    parser.add_argument(
        "--pr-body", dest="pr_body", default=None,
        help="PR body text directly (alternative to --pr-body-file).",
    )
    parser.add_argument(
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON (the workflow parses this for the label).",
    )
    args = parser.parse_args(argv)

    paths = _collect_paths(args.paths, args.stdin)
    body = args.pr_body or ""
    if args.pr_body_file:
        try:
            body += Path(args.pr_body_file).read_text(encoding="utf-8")
        except OSError:
            pass

    payload = check_pr(paths, body)

    if args.json_out:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        s = payload["summary"]
        print(f".NET notebooks checked: {s['dotnet_notebooks_checked']}")
        print(f"  with #r nuget: {s['dotnet_notebooks_with_nuget']}")
        print(f"  flagged (0 nuget + body block): {s['dotnet_block_without_nuget']}")
        if s["body_keywords_found"]:
            print(f"body block keywords: {s['body_keywords_found']}")
        for nb in payload["notebooks"]:
            tag = "FLAG" if nb.get("flagged") else "ok"
            print(f"  [{tag}] {nb['path']} -- {nb.get('reason', nb.get('status'))}")

    # Advisory: NEVER exit non-zero (#10024 acceptance).
    return 0


if __name__ == "__main__":
    sys.exit(main())
