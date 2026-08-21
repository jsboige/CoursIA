#!/usr/bin/env python3
"""Check that PR-triggered workflows render unique check-run names (#11869).

The defect #11869 pins: `scripts/pr_gate.py::dedupe_latest` folds check-runs
by NAME alone. When two distinct workflows declare jobs whose rendered name
collides (e.g. three ratchets all naming their job `Ratchet (base vs PR)`),
the fold keeps whichever started latest and drops the others -- including a
real FAIL sitting underneath a SUCCESS. Measured on `cf968dcf` (PR #11856):
the PR gate reported SUCCESS while `notebook-papermill-ratchet` had
FAILed, because the two success siblings started later than the failure.

The premise `name identifies the job` is FALSE in this repo. Two classes of
collision were measured (#11869 §"les deux classes de collision"):

  1. **Ratchet x3** -- `notebook-papermill-ratchet.yml`,
     `notebook-exec-sequence-ratchet.yml`, `notebook-output-failure-ratchet.yml`
     all declare a single job named `Ratchet (base vs PR)`. ACTIVE (every
     notebook-bearing PR cofires all three).
  2. **`ci` x17** -- the 17 `lean-*.yml` workflows call the reusable
     `lean-build.yml`, whose rendered job name is `Lean CI (<lake>)` -- so
     this is actually unique per lake. NOT a collision in practice.

The guard enumerates every workflow with a `pull_request` trigger, computes
the rendered check-run name for each non-reusable job, and red-lines on any
duplicate. The rendered name is `job.name` if declared, else `job_key`. A
reusable job (with `uses:`) is skipped -- its rendered name is the CALLEE's
job name after templating, which we cannot resolve locally (would require
either fetching the callee or running through GitHub's templating engine).

Positive control (#11869 acceptance 1): running `--check` on `main` BEFORE
the rename is RED (cites the current duplicates). After the rename it goes
GREEN. A green-on-bare-state instrument measures nothing.

Modes:
  --check       print summary + duplicates; exit 0 if unique, exit 1 if
                duplicates found, exit 2 on instrument failure.
  --json        same as --check but emits a JSON document on stdout (used by
                the CI guard workflow to render structured output).

Run: python scripts/ci/check_unique_check_run_names.py --check
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

# Reuse the YAML parsing the rest of the pr_gate family uses (PyYAML with
# the `on:` workaround via a quoted-on string injection upstream). We do
# NOT depend on pr_gate here -- the function is independent of the gate's
# state and must work even if pr_gate.py is mid-rewrite.

EXIT_UNIQUE, EXIT_DUPLICATES, EXIT_BROKEN = 0, 1, 2

DEFAULT_WORKFLOWS_DIR = str(
    Path(__file__).resolve().parents[2] / ".github" / "workflows"
)


def _load_yaml():
    try:
        import yaml
    except ImportError:
        return None
    return yaml


def _parse_workflow(text: str, yaml):
    """Parse one workflow YAML, working around PyYAML's `on:` -> True issue.

    PyYAML 1.1 treats the bareword `on` as a boolean; we rewrite the trigger
    key to a quoted string before parsing. Returns the parsed dict or None.

    The trigger key is always at column 0. Lines like `on: [pull_request]`
    (inline list form) must keep their value: we replace the leading `on:`
    token with `"on":` and leave the rest of the line untouched.
    """
    out_lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("on:") and (
            len(line) == 3 or line[3] in (" ", "[", "\t")
        ):
            out_lines.append('"on":' + line[3:])
        else:
            out_lines.append(line)
    fixed = "\n".join(out_lines)
    try:
        data = yaml.safe_load(fixed)
    except yaml.YAMLError:
        return None
    return data if isinstance(data, dict) else None


def _has_pull_request_trigger(data: dict) -> bool:
    triggers = data.get("on", data.get(True))
    if isinstance(triggers, dict):
        return "pull_request" in triggers or "pull_request_target" in triggers
    if isinstance(triggers, list):
        return "pull_request" in triggers or "pull_request_target" in triggers
    if isinstance(triggers, str):
        return triggers in ("pull_request", "pull_request_target")
    return False


def collect_rendered_names(workflows_dir: str = DEFAULT_WORKFLOWS_DIR):
    """Walk every `pull_request`-triggered workflow and return its rendered
    job names alongside provenance.

    Returns: list of (rendered_name, workflow_file, job_key) tuples. Reusable
    jobs (`uses:`) are SKIPPED -- their rendered name depends on the callee
    after GitHub's templating, which we cannot resolve locally.
    """
    yaml = _load_yaml()
    if yaml is None:
        return None  # broken instrument

    root = Path(workflows_dir)
    out: list[tuple[str, str, str]] = []
    for yml in sorted(root.glob("*.yml")):
        try:
            text = yml.read_text(encoding="utf-8")
        except OSError:
            continue
        data = _parse_workflow(text, yaml)
        if data is None:
            continue
        if not _has_pull_request_trigger(data):
            continue
        jobs = data.get("jobs") or {}
        for job_key, job_def in jobs.items():
            if not isinstance(job_def, dict):
                continue
            # Reusable job: rendered name is the callee's job name; skip.
            if "uses" in job_def:
                continue
            name = job_def.get("name") or job_key
            out.append((str(name), str(yml), str(job_key)))
    return out


def find_duplicates(
    workflows_dir: str = DEFAULT_WORKFLOWS_DIR,
) -> tuple[list[tuple[str, list[tuple[str, str]]]], int, int]:
    """Return (duplicates, total_jobs, total_workflows).

    Each duplicate is `(rendered_name, [(workflow_file, job_key), ...])`.
    """
    pairs = collect_rendered_names(workflows_dir)
    if pairs is None:
        return [], 0, 0

    by_name: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for name, wf, job_key in pairs:
        by_name[name].append((wf, job_key))

    dupes = sorted(
        [(name, instances) for name, instances in by_name.items() if len(instances) > 1],
        key=lambda x: (-len(x[1]), x[0]),
    )
    return dupes, len(pairs), len({wf for _, wf, _ in pairs})


def _print_text_report(dupes, total_jobs, total_workflows):
    print(
        f"[unique-check-run-names] PR-workflow jobs scanned: {total_jobs} "
        f"across {total_workflows} workflows"
    )
    if not dupes:
        print("[unique-check-run-names] OK -- no duplicate rendered names.")
        return
    print(f"[unique-check-run-names] DUPLICATES FOUND: {len(dupes)} name(s)")
    for name, instances in dupes:
        print(f"  {name!r}: {len(instances)} instances")
        for wf, job_key in instances:
            print(f"    -> {wf} (job_key={job_key})")


def _main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Check that PR workflows render unique check-run names."
    )
    g = parser.add_mutually_exclusive_group()
    g.add_argument("--check", action="store_true", help="exit 0/1/2 by status")
    g.add_argument("--json", action="store_true", help="JSON output on stdout")
    args = parser.parse_args(argv[1:])

    dupes, total_jobs, total_workflows = find_duplicates()
    if dupes is None and total_jobs == 0:
        print(
            "[unique-check-run-names] BROKEN INSTRUMENT: PyYAML unavailable "
            "or no workflows parsed. Verdict nul.",
            file=sys.stderr,
        )
        return EXIT_BROKEN

    if args.json:
        print(json.dumps({
            "ok": not dupes,
            "total_jobs": total_jobs,
            "total_workflows": total_workflows,
            "duplicates": [
                {"name": n, "instances": [{"workflow": wf, "job_key": jk} for wf, jk in inst]}
                for n, inst in dupes
            ],
        }, indent=2, ensure_ascii=False))
        return EXIT_UNIQUE if not dupes else EXIT_DUPLICATES

    _print_text_report(dupes, total_jobs, total_workflows)
    return EXIT_UNIQUE if not dupes else EXIT_DUPLICATES


if __name__ == "__main__":
    sys.exit(_main(sys.argv))