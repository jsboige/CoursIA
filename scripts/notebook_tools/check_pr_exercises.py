#!/usr/bin/env python3
"""Per-PR advisory check for the ">= 3 exercises" convention (#2161).

This is the missing ORGAN pointed out by issue #8814: the convention
(``.claude/rules/three-exercises-per-notebook.md``) and its tool
(``count_exercises.py``) existed, but nothing wired the tool to a PR, so the
rule relied entirely on reviewer vigilance. This script + the
``exercises-advisory.yml`` workflow make the convention VISIBLE on each PR.

It is ADVISORY by design (issue #8814 acceptance 5): it always exits 0. The
actionable payload is the ``exercises-below-threshold`` LABEL the workflow
posts when a modified notebook is below threshold -- never the green
conclusion of the job, which is green by construction. A reviewer who reads
only "exit 0" as "conforming" has read the wrong signal (the same trap that
let a non-conforming PR through in #8797).

Consumes, never re-implements, the classification of ``count_exercises.py``
(issue #8814 acceptance 4): it calls ``classify_notebook`` (the corpus/kind
logic -- setup/Lean exemptions, out-of-corpus artifacts) and
``count_exercises_in_notebook`` (the count). If the two diverged because this
script reinvented the rules, the label and the canonical tool would disagree.

Scope: only ``*.ipynb`` MODIFIED by the PR (issue #8814 acceptance 1) -- not
a repo-wide scan on every push. The caller passes the changed paths.

Usage:
    python check_pr_exercises.py --paths a.ipynb b.ipynb
    python check_pr_exercises.py --paths a.ipynb --json
    git diff --name-only BASE HEAD -- '*.ipynb' | python check_pr_exercises.py --stdin
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

# Import the canonical classification + counter rather than re-implementing
# them (issue #8814 acceptance 4: the two must not diverge).
_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from count_exercises import (  # noqa: E402
    OUT_OF_CORPUS_KINDS,
    classify_notebook,
    count_exercises_in_notebook,
)

LABEL_NAME = "exercises-below-threshold"
# A SECOND, distinct label for notebooks the checker could NOT READ (issue #8819).
# "I could not measure" and "I measured, it is below threshold" are two different
# states calling for two different reactions, so they get two different labels --
# collapsing them into one would re-create the very defect #8819 fixes (a gate
# whose official signal reassures while the true state sleeps in the log).
LABEL_UNPARSEABLE = "exercises-unparseable"


@dataclass
class NotebookVerdict:
    """One notebook's advisory verdict, with the evidence the label needs."""

    path: str
    kind: str
    threshold: int | None  # None = out of corpus (convention does not apply)
    count: int
    status: str  # 'sub_threshold' | 'ok' | 'out_of_corpus' | 'parse_error'
    detail: str = ""


@dataclass
class CheckResult:
    """Aggregate verdict over all PR-modified notebooks."""

    sub_threshold: list[NotebookVerdict] = field(default_factory=list)
    ok: list[NotebookVerdict] = field(default_factory=list)
    out_of_corpus: list[NotebookVerdict] = field(default_factory=list)
    parse_errors: list[NotebookVerdict] = field(default_factory=list)

    def as_payload(self) -> dict:
        """Machine-readable payload for the workflow to decide the labels.

        Issue #8819: a notebook the checker could not read is NOT conforming --
        it is UNVERIFIED. The summary therefore exposes ``unverified`` (parse
        errors) at the top, and the payload carries TWO labels: one for
        "measured, below threshold" (below_threshold) and one for "could not
        measure" (unparseable). The workflow raises each when its count is > 0,
        and crucially never claims "all conform" while ``unverified > 0``.
        """
        n_sub = len(self.sub_threshold)
        n_parse = len(self.parse_errors)
        n_ok = len(self.ok)
        n_out = len(self.out_of_corpus)
        return {
            "labels": {
                "below_threshold": {"name": LABEL_NAME, "count": n_sub},
                "unparseable": {"name": LABEL_UNPARSEABLE, "count": n_parse},
            },
            "summary": {
                # unverified FIRST (issue #8819 criterion 4): a glance at the
                # payload makes the gap obvious without arithmetic. A gate that
                # claims more than it measured is the defect class #8819 fixes.
                "unverified": n_parse,
                "total": n_sub + n_ok + n_out + n_parse,
                # in_corpus counts everything the convention COULD apply to,
                # including unparseable ones -- an unread notebook is still in
                # the corpus, just not measured.
                "in_corpus": n_sub + n_ok + n_parse,
                "out_of_corpus": n_out,
                "below_threshold": n_sub,
                "sub_threshold": n_sub,  # kept alias for readability
                "parse_errors": n_parse,
            },
            "sub_threshold": [asdict(v) for v in self.sub_threshold],
            "ok": [asdict(v) for v in self.ok],
            "out_of_corpus": [asdict(v) for v in self.out_of_corpus],
            "parse_errors": [asdict(v) for v in self.parse_errors],
        }


def check_notebooks(paths: list[Path]) -> CheckResult:
    """Classify + count each path, bucketing by advisory status.

    A notebook is ``sub_threshold`` only when it is IN the pedagogical corpus
    (threshold is not None) AND its exercise count is below its KIND-SPECIFIC
    threshold. A setup notebook (threshold 0), a Lean notebook (threshold 2),
    or an out-of-corpus artifact is never sub-threshold -- the rule exempts
    them, and this function consumes that exemption rather than overriding it.
    """
    result = CheckResult()
    for path in paths:
        kind, threshold = classify_notebook(path)
        if threshold is None:
            result.out_of_corpus.append(
                NotebookVerdict(
                    path=str(path), kind=kind, threshold=None,
                    count=0, status="out_of_corpus",
                    detail=f"out of corpus (kind={kind}) -- convention does not apply",
                )
            )
            continue

        cnt = count_exercises_in_notebook(path)
        if cnt.parse_error is not None:
            result.parse_errors.append(
                NotebookVerdict(
                    path=str(path), kind=kind, threshold=threshold,
                    count=cnt.count, status="parse_error", detail=cnt.parse_error,
                )
            )
            continue

        verdict = NotebookVerdict(
            path=str(path), kind=kind, threshold=threshold, count=cnt.count,
            status="ok" if cnt.count >= threshold else "sub_threshold",
        )
        if cnt.count < threshold:
            result.sub_threshold.append(verdict)
        else:
            result.ok.append(verdict)
    return result


def _render_text(result: CheckResult) -> str:
    """Human-readable summary (the workflow log; the labels are separate).

    Issue #8819 criterion 2: the closing line asserts ONLY what was measured.
    ``All ... meet their threshold`` is conditional on ``parse_errors == 0`` --
    otherwise the honest statement is "N could not be parsed -- NOT verified",
    never a blanket claim of conformity over notebooks the checker never read.
    """
    s = result.as_payload()["summary"]
    lines = [
        f"Notebooks checked   : {s['total']}",
        f"In corpus           : {s['in_corpus']}",
        f"Out of corpus       : {s['out_of_corpus']}",
        f"Below threshold     : {s['below_threshold']}",
        f"Unverified (parse)  : {s['unverified']}",
    ]
    if result.sub_threshold:
        lines.append(
            f"\n--- Below threshold (label: {LABEL_NAME}) ---"
        )
        for v in result.sub_threshold:
            lines.append(
                f"  [{v.count}/{v.threshold}] ({v.kind}) {v.path}"
            )
    if result.out_of_corpus:
        lines.append("\n--- Out of corpus (exempt, not labelled) ---")
        for v in result.out_of_corpus:
            lines.append(f"  ({v.kind}) {v.path} -- {v.detail}")
    if result.parse_errors:
        lines.append(
            f"\n--- Unverified: could not parse (label: {LABEL_UNPARSEABLE}) ---"
        )
        for v in result.parse_errors:
            lines.append(f"  {v.path}: {v.detail[:120]}")
    # Criterion 2: assert only what was measured. A parse error means we did
    # NOT measure that notebook, so "all meet threshold" would be a false claim.
    if s["unverified"] > 0:
        lines.append(
            f"\n{s['unverified']} notebook(s) could not be parsed -- NOT verified."
        )
    elif not result.sub_threshold:
        lines.append(
            "\nAll in-corpus modified notebooks meet their threshold."
        )
    return "\n".join(lines)


def _collect_paths(argv_paths: list[str], from_stdin: bool) -> list[Path]:
    """Resolve paths from CLI args and/or stdin (one path per line).

    The workflow pipes ``git diff --name-only`` output here. Blank lines and
    duplicates are dropped; non-existent paths are warned and skipped (a
    deleted notebook has nothing to count).
    """
    raw: list[str] = list(argv_paths)
    if from_stdin:
        raw += [ln.strip() for ln in sys.stdin if ln.strip()]
    seen: set[str] = set()
    paths: list[Path] = []
    for r in raw:
        if r in seen:
            continue
        seen.add(r)
        p = Path(r)
        if not p.exists():
            print(f"warning: {r} does not exist (deleted?), skipping", file=sys.stderr)
            continue
        if p.suffix != ".ipynb":
            continue
        paths.append(p)
    return paths


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Per-PR advisory check for the >= 3 exercises convention (#2161). "
            "Always exits 0 (advisory): the signal is the "
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
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON (the workflow parses this for the label).",
    )
    args = parser.parse_args(argv)

    paths = _collect_paths(args.paths, args.stdin)
    if not paths:
        msg = "No modified notebooks in corpus to check."
        if args.json_out:
            payload = CheckResult().as_payload()
            payload["note"] = msg
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            print(msg)
        return 0

    result = check_notebooks(paths)
    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2, ensure_ascii=False))
    else:
        print(_render_text(result))
    # Advisory: NEVER exit non-zero (issue #8814 acceptance 5).
    return 0


if __name__ == "__main__":
    sys.exit(main())
