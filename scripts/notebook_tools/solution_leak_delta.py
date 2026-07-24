#!/usr/bin/env python3
"""Solution-leak delta guard — compare two ``audit_solution_leaks.py --json``
scans and report HIGH-severity findings *newly introduced* by a PR.

Why a delta AND a WARN mode (not an absolute FAIL)
-------------------------------------------------
``audit_solution_leaks.py`` currently emits ~498 ``function_body_leak`` findings
across the repo, the large majority of which are legitimate worked examples
(functions with >3 logic lines that are *guided examples*, not student-exercise
stubs with their solution pasted in). The detector's precision on C#/.NET+Lean
is known low (~95% false-positive rate, fleet memory
``solution-leak-detector-csharp-lean-fp``; retracted for ``// TODO`` c.827).

An **absolute** gate would therefore (a) post a scary "497 leaks!" inventory on
every PR and (b) block the whole cluster once flipped to FAIL. Both are wrong.

The durable transposition, per issue #8053 acceptance "Mode WARN d'abord
(inventaire), puis bascule FAIL une fois le backlog nettoyé", is a **delta guard
in WARN mode**:

* compare HIGH findings on BASE vs HEAD, keyed by (path, type, func_name,
  cell_index, start_line) so unchanged inherited findings never count;
* report only the HIGH findings HEAD has that BASE does not (newly introduced
  / worsened by THIS PR) — a typical PR touches 1-7 notebooks, so the delta is
  compact and reviewer-actionable;
* **never fail** (exit 0) in this phase — the output is advisory, posted to the
  GitHub Actions job summary. The FAIL switch is gated on a detector-precision
  fix (reduce C#/.NET+Lean FP, restore ``// TODO`` discrimination) tracked
  separately and explicitly out of scope here.

Usage (driven by ``.github/workflows/solution-leak-guard.yml``)::

    python scripts/notebook_tools/audit_solution_leaks.py --json > head.json
    git checkout baseref -- MyIA.AI.Notebooks
    python scripts/notebook_tools/audit_solution_leaks.py --json > base.json
    git checkout HEAD -- MyIA.AI.Notebooks
    python scripts/notebook_tools/solution_leak_delta.py base.json head.json

Exit codes: 0 always (WARN phase). A future ``--fail-on-delta`` flag will flip
to exit 1 once precision is fixed and the backlog is drained.

See #8053 (CI gate), #8052 (audit sampling), exercise-example-labeling.md
(content-based rule), pip_leak_delta.py (mirror pattern, #6314).
"""
from __future__ import annotations

import argparse
import json
import sys

# Only HIGH-severity findings participate in the delta. MEDIUM/LOW/FLAG (C#
# candidates) are excluded: FLAG is explicitly manual-review-only and MEDIUM/LOW
# carry too much noise for an advisory gate. This mirrors pip_leak_delta.py
# restricting to HIGH_CLASSIFICATIONS.
DELTA_SEVERITY = "HIGH"


def _fingerprint(path, leak):
    """Stable identity for a finding so an unchanged inherited leak is not
    double-counted across BASE and HEAD. ``context`` (the raw source lines) is
    intentionally excluded: a reviewer-touched comment or whitespace tweak would
    otherwise create a phantom 'new' finding for the same logical leak."""
    return (
        path,
        leak.get("type"),
        leak.get("func_name"),
        leak.get("cell_index"),
        leak.get("start_line"),
    )


def _high_findings(data):
    """Yield (path, fingerprint, leak) for every HIGH finding in a parsed
    audit_solution_leaks JSON document. Findings are de-duplicated on
    fingerprint (the base detector can emit the same function twice — e.g.
    ``inheritance_value`` cell 47 listed 2x — which would otherwise inflate the
    delta)."""
    findings = data.get("findings", {}) if isinstance(data, dict) else {}
    seen = set()
    for path, leaks in findings.items():
        for leak in leaks:
            if leak.get("severity") != DELTA_SEVERITY:
                continue
            fp = _fingerprint(path, leak)
            if fp in seen:
                continue
            seen.add(fp)
            yield path, fp, leak


def _high_set(data):
    """map(fingerprint -> leak) for HIGH findings (deduplicated)."""
    return {fp: leak for _path, fp, leak in _high_findings(data)}


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Report HIGH solution-leak findings introduced by HEAD vs BASE (WARN mode, #8053)."
    )
    parser.add_argument("base", help="BASE JSON (audit_solution_leaks.py --json)")
    parser.add_argument("head", help="HEAD JSON (audit_solution_leaks.py --json)")
    args = parser.parse_args(argv)

    try:
        with open(args.base, encoding="utf-8") as fh:
            base = json.load(fh)
        with open(args.head, encoding="utf-8") as fh:
            head = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: cannot read JSON inputs: {exc}", file=sys.stderr)
        return 2

    base_map = _high_set(base)
    head_map = _high_set(head)
    base_n = len(base_map)
    head_n = len(head_map)

    # New = fingerprints present in HEAD but absent in BASE.
    new_fps = [fp for fp in head_map if fp not in base_map]
    delta = len(new_fps)

    print(f"solution-leak guard (WARN phase): BASE HIGH={base_n}  HEAD HIGH={head_n}  new={delta}")
    print(
        "WARN-only (exit 0): inherited HIGH findings tolerated; only newly-introduced "
        "HIGH findings are listed below. FAIL switch gated on detector-precision fix "
        "(C#/.NET+Lean FP, // TODO discrimination) — see #8053."
    )

    if delta > 0:
        print()
        print(f"### {delta} newly-introduced HIGH solution-leak candidate(s)")
        print()
        print(
            "_These are detector candidates, not auto-verdicts. A HIGH "
            "`function_body_leak` flags a function with >3 logic lines found under "
            "an Exercice marker — verify by CONTENT (cf exercise-example-labeling.md): "
            "a guided example (Exemple resolu) is legitimate and must NOT be stubbed._"
        )
        print()
        # Group new findings by notebook path for readability.
        by_path = {}
        for fp in new_fps:
            path = fp[0]
            by_path.setdefault(path, []).append(head_map[fp])
        for path in sorted(by_path):
            print(f"**{path}**")
            for leak in by_path[path]:
                desc = f"- [{leak.get('type')}]"
                if leak.get("func_name"):
                    desc += f" `{leak['func_name']}`"
                if leak.get("logic_lines") is not None:
                    desc += f" ({leak['logic_lines']} logic lines)"
                if leak.get("cell_index") is not None:
                    desc += f" cell {leak['cell_index']}"
                if leak.get("start_line") is not None:
                    desc += f" L{leak['start_line']}"
                print(desc)
            print()

    # WARN phase: never fail. Reviewer reads the job summary; FAIL is a future
    # flag (--fail-on-delta) gated on precision work.
    return 0


if __name__ == "__main__":
    sys.exit(main())
