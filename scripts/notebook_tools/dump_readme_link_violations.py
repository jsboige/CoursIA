#!/usr/bin/env python3
"""Capture README-vs-.ipynb violations as a JSON document (delta_argv feed).

Why this script exists
----------------------
`scripts/regen_quarto_render.py --check-readme-links` emits violations as
`::error::<CLASS> <readme> -> <href>` lines on stderr (one per line) plus a
human-readable summary on stdout. The fast-lane engine needs a stable JSON
artefact on stdout so the `delta_argv` comparator can diff head vs base.

This wrapper runs the check, parses both streams, and prints a JSON document
on stdout (the engine captures stdout via `payload_of()` and writes it to
`{name}.head.json` / `{name}.base.json` for the comparator):

    {"violations": [{"class": "STALE_LINK",
                     "readme": "...",
                     "href": "..."},
                    ...],
     "n_violations": <int>,
     "n_readmes": <int>}

Exit codes:
    0 = JSON printed (regardless of violation count -- the delta_argv
        comparator is the only one that decides the final verdict, and
        it ignores the upstream rc; this lets argv not rouge on the
        2432 historical violations while still capturing them for diff).
    2 = invocation error (cwd, missing upstream script, etc.).

Pair with `scripts/notebook_tools/diff_readme_link_violations.py` for the
delta comparator. Together they implement F2 of #18970 (delta-only, not
BRUT, so the 2428 historical backlog never blocks a PR that adds zero
new violations).
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

VIOLATION_RE = re.compile(r"^::error::(STALE_LINK|BROKEN|DEAD_RENDER)\s+(\S+)\s+->\s+(\S+)\s*$")


def _scan() -> dict:
    proc = subprocess.run(
        ["python", "scripts/regen_quarto_render.py", "--check-readme-links"],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    violations: list[dict] = []
    # Les violations partent sur stderr (file=sys.stderr dans regen_quarto_render.py l.503).
    for raw in (proc.stderr or "").splitlines():
        m = VIOLATION_RE.match(raw.strip())
        if m:
            violations.append({"class": m.group(1), "readme": m.group(2), "href": m.group(3)})
    # stdout porte le resume lisible ; on extrait n_readmes pour information.
    # Format: "README-link audit: 402 rendered-subtree READMEs, 2432 violation(s), ..."
    n_readmes = 0
    for raw in (proc.stdout or "").splitlines():
        if "README-link audit:" in raw:
            try:
                n_readmes = int(raw.split("rendered-subtree READMEs")[0].rsplit(" ", 1)[-1])
            except (ValueError, IndexError):
                # Fallback : split sur " rendered-subtree READMEs," et split sur espace.
                try:
                    n_readmes = int(raw.split(" rendered-subtree READMEs,")[0].rsplit(" ", 1)[-1])
                except (ValueError, IndexError):
                    n_readmes = 0
            break
    return {
        "violations": violations,
        "n_violations": len(violations),
        "n_readmes": n_readmes,
    }


def main() -> int:
    try:
        payload = _scan()
    except Exception as exc:
        print(f"::error::dump_readme_link_violations failed: {exc}", file=sys.stderr)
        return 2
    # Sortie sur stdout : le moteur fast-lane capture stdout via payload_of()
    # et l'ecrit dans {name}.head.json (puis base.json apres bascule phase 2).
    print(json.dumps(payload, ensure_ascii=False))
    # Toujours rc=0 en argv : seul delta_argv tranche (cf docstring module).
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

