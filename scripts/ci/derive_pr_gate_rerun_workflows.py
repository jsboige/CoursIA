#!/usr/bin/env python3
"""Derive the `workflow_run.workflows` list of pr-gate-rerun.yml (#11865).

The re-aggregation leg of the PR gate fires on a hand-written list of 5 guard
workflows chosen in #11405. Measured 2026-08-19 (#11865): 88 workflows carry a
`pull_request` trigger (113 jobs), the 5-name list covers 14 of them -- under
runner starvation the unlisted 70 have NO event-driven rescue path, and both
gate timeouts of that evening (#11776 on Catalog Drift / Quarto / CodeQL,
#11839 on Secret Scan) sat on workflows outside the list.

`workflow_run.workflows` accepts no wildcard, so the enumeration must stay
explicit in the YAML. The fix is not a longer hand-written list (it rots the
same way) but a DERIVED one, on the model of `pr_gate.py::
derive_always_on_jobs` (rule 8: derived, never hardcoded -- a baked-in list
rotten is worse than none because it under-covers in silence).

Membership rule -- a workflow belongs in the re-aggregation list when its
completion can flip the gate's verdict, i.e. when ALL of:

  1. it has a `pull_request` trigger (any shape -- path-filtered INCLUDED:
     when such a workflow runs, its check is waited on like any other, and a
     path filter merely means it runs on fewer PRs);
  2. it produces >= 1 NON-ADVISORY job (advisory checks never reach the
     gate's pending list, so their completion cannot flip a verdict -- see
     `classify` in pr_gate.py, rule 6);
  3. it is not the gate itself ("PR gate" must never appear in the list:
     its rerun would complete, re-trigger this workflow, and self-sustain --
     the loop bound documented in pr-gate-rerun.yml's header).

Positive control (#11865 acceptance): the derivation maps JOB names to their
owning workflow and must find exactly the workflow that owns the "PR gate"
job. A mapping that cannot find it is broken, and its output is a verdict
NUL -- the script refuses to green or red a check on a broken instrument
(exit 2, distinct from drift's exit 1).

Modes:
  --print-yaml  emit the derived list as the YAML `workflows: [...]` line
  --check       compare the committed list against the derived one; exit 1
                on drift (missing and/or extra names), exit 2 when the
                positive control fails, exit 0 when in sync.

Run: python scripts/ci/derive_pr_gate_rerun_workflows.py --check
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pr_gate  # noqa: E402  (scripts/ -- reuse its YAML trigger parsing)


DEFAULT_RERUN_YML = str(
    Path(__file__).resolve().parents[2] / ".github" / "workflows" / "pr-gate-rerun.yml"
)

# Exit codes: 0 in sync, 1 drift (actionable), 2 instrument broken (nul).
EXIT_SYNC, EXIT_DRIFT, EXIT_BROKEN = 0, 1, 2


def derive_rerun_workflows(
    workflows_dir: str = pr_gate.DEFAULT_WORKFLOWS_DIR,
    gate_job: str = pr_gate.DEFAULT_SELF_NAME,
) -> tuple[list[str], list[str]]:
    """Return (derived workflow names sorted, gate-owning workflow names).

    The second element is the positive control: the workflows owning a job
    named like the gate. The caller MUST verify it is non-empty before
    trusting the first element (a mapping that lost the gate itself has
    misparsed the directory and would silently under-cover again).
    """
    if pr_gate.yaml is None:
        return [], []  # caller reports the broken instrument, never a pass

    root = Path(workflows_dir)
    derived: set[str] = set()
    gate_workflows: set[str] = set()
    for yml in sorted(root.glob("*.yml")):
        try:
            data = pr_gate.yaml.safe_load(yml.read_text(encoding="utf-8"))
        except (OSError, pr_gate.yaml.YAMLError):
            continue
        if not isinstance(data, dict):
            continue

        jobs = pr_gate._workflow_job_names(data)
        wf_name = data.get("name") or yml.stem

        if any(pr_gate._norm(j) == pr_gate._norm(gate_job) for j in jobs):
            gate_workflows.add(wf_name)  # excluded: loop bound (rule 3)
            continue

        triggers = data.get("on", data.get(True))
        if pr_gate._pull_request_trigger(triggers) is None:
            continue
        if any(not pr_gate.is_advisory(j) for j in jobs):
            derived.add(wf_name)

    return sorted(derived), sorted(gate_workflows)


def committed_workflows(rerun_yml: str = DEFAULT_RERUN_YML) -> list[str] | None:
    """The `workflows:` list committed in pr-gate-rerun.yml, or None if the
    file/field cannot be read (broken instrument, not an empty list)."""
    if pr_gate.yaml is None:
        return None
    try:
        data = pr_gate.yaml.safe_load(Path(rerun_yml).read_text(encoding="utf-8"))
    except (OSError, pr_gate.yaml.YAMLError):
        return None
    if not isinstance(data, dict):
        return None
    wr = (data.get("on", data.get(True)) or {}).get("workflow_run")
    if isinstance(wr, dict) and isinstance(wr.get("workflows"), list):
        return [str(w) for w in wr["workflows"]]
    return None


def check(
    workflows_dir: str = pr_gate.DEFAULT_WORKFLOWS_DIR,
    rerun_yml: str = DEFAULT_RERUN_YML,
) -> int:
    derived, gate_workflows = derive_rerun_workflows(workflows_dir)
    if not gate_workflows:
        print(
            "[rerun-drift] POSITIVE CONTROL FAILED: no workflow found owning "
            f"the '{pr_gate.DEFAULT_SELF_NAME}' job -- mapping broken, "
            "verdict nul (fix the derivation before trusting any list).",
            file=sys.stderr,
        )
        return EXIT_BROKEN
    committed = committed_workflows(rerun_yml)
    if committed is None:
        print(
            "[rerun-drift] cannot read the committed workflows list from "
            f"{rerun_yml} -- broken instrument, verdict nul.",
            file=sys.stderr,
        )
        return EXIT_BROKEN

    missing = sorted(set(derived) - set(committed))
    extra = sorted(set(committed) - set(derived))
    print(
        f"[rerun-drift] derived={len(derived)} committed={len(committed)} "
        f"gate-owner(s)-excluded={gate_workflows}"
    )
    if not missing and not extra:
        print("[rerun-drift] in sync -- committed list matches the derivation")
        return EXIT_SYNC
    for name in missing:
        print(f"[rerun-drift] MISSING (workflow not covered by the rerun leg): {name}")
    for name in extra:
        print(f"[rerun-drift] EXTRA (no longer derivable, prune the list): {name}")
    print(
        "[rerun-drift] DRIFT -- regenerate with: python "
        "scripts/ci/derive_pr_gate_rerun_workflows.py --print-yaml"
    )
    return EXIT_DRIFT


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--check",
        action="store_true",
        help="compare the committed pr-gate-rerun.yml list against the "
        "derivation (exit 1 drift / 2 broken instrument / 0 in sync)",
    )
    ap.add_argument(
        "--print-yaml",
        action="store_true",
        help="print the derived list as the YAML workflows: line",
    )
    ap.add_argument("--workflows-dir", default=pr_gate.DEFAULT_WORKFLOWS_DIR)
    ap.add_argument("--rerun-yml", default=DEFAULT_RERUN_YML)
    args = ap.parse_args(argv)

    if args.check:
        return check(args.workflows_dir, args.rerun_yml)

    derived, gate_workflows = derive_rerun_workflows(args.workflows_dir)
    if not gate_workflows:
        print(
            "[rerun-drift] POSITIVE CONTROL FAILED -- refusing to print a "
            "list derived by a broken mapping.",
            file=sys.stderr,
        )
        return EXIT_BROKEN
    names = ", ".join(f'"{w}"' for w in derived)
    print(f"workflows: [{names}]")
    return EXIT_SYNC


if __name__ == "__main__":
    raise SystemExit(main())
