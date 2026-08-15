#!/usr/bin/env python3
"""Guard: a paths-filtered, label-posing workflow MUST self-cover its own file.

Issue #8822. A ``pull_request`` workflow filtered by ``on.pull_request.paths``
runs ONLY when the PR's ``base...head`` diff touches one of those paths. If such
a workflow also POSES a label (``gh pr edit --add-label`` / ``gh label create``),
then the commit that RETIRES the matching paths from the diff makes the job
unable to re-run -- so its own cleanup branch (``--remove-label``) is dead code
exactly when it is needed. The label survives its cause and becomes a manual
chore. This was demonstrated firsthand on PR #8820 (2026-07-29): the bot posed
``exercises-unparseable`` at 10:56, the corrupt artifact was removed, the paths
filter (``**/*.ipynb``) kept the job from re-running, and a human unlabeled at
11:02 -- the workflow could not undo its own label.

The guard enforces the established convention that fixes this: list the
workflow's OWN path in its ``paths:`` filter. 20 workflows already do
(``scripts-tests.yml``, ``lean-conway.yml``, ``banner-guard.yml``, ...). The two
other label-posers (``stale-base-warning.yml``, ``variation-tag-guard.yml``)
have NO ``paths:`` filter at all, so they always run and can always clean up --
they are correctly out of scope.

This is BLOCKING (issue #8822 acceptance 4): the target is a file invariant
(the workflow's own path appears under ``paths:``), not a content judgement, so
there is nothing to arbitrate and nothing to let slide. Contrast the advisory
exit-0 pattern of ``check_pr_exercises.py`` (#8816) -- that guards pedagogical
content (a judgement); this guards a structural invariant (a fact).

It is auto-covered by construction: the guard scans ``.github/workflows/**``,
which contains its own file. It cannot be the first to violate its own rule.

Acceptance (#8822):
1. Positive control: a label-posing + paths-filtered workflow that does NOT
   self-cover FAILS the guard (unit-tested, and the live run on ``main`` fails
   on ``exercises-advisory.yml`` -- the measured 1/1 violator).
2. Negative control: the 20 already-self-covered workflows pass; the ~48
   path-filtered workflows that pose NO label are not flagged.
3. Denominator printed + FAIL if zero scanned (a guard that enumerates nothing
   is green and mute -- #8678/#8680).
4. Blocking: exit 1 on any violation (or zero denominator); exit 0 only clean.

Usage:
    python scripts/check_workflow_label_paths.py            # scans .github/workflows
    python scripts/check_workflow_label_paths.py --root REPO # scans REPO/.github/workflows
    python scripts/check_workflow_label_paths.py --json      # machine-readable
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

try:
    import yaml  # type: ignore
except ImportError:  # pragma: no cover - pyyaml is an established repo dep
    sys.stderr.write(
        "error: PyYAML is required (pip install pyyaml). It is an established "
        "dependency of scripts/lean/check_target_coverage.py and "
        "scripts/translation/check_translation_sync.py.\n"
    )
    sys.exit(2)

# `.github/workflows` -- the directory this guard (and every workflow) lives in.
WORKFLOWS_DIR = Path(".github/workflows")

# A workflow POSES a label if it creates one or adds one to a PR.
# `gh label create` defines a label; `--add-label` attaches one. We do NOT fire
# on `--remove-label` alone -- a workflow that only removes labels cannot orphan
# one (it cleans up; the danger is the one that sets them). Detection is on raw
# text (the gh calls live inside shell `run:` blocks, which YAML parses as
# strings, not structured keys) -- after stripping PURE-COMMENT lines (see
# ``_strip_comment_lines``), so a workflow that merely DOCUMENTS the convention
# in a header comment (this very file does) is not miscounted as a label-poser.
LABEL_CREATE_RE = re.compile(r"gh\s+label\s+create")
ADD_LABEL_RE = re.compile(r"--add-label\b")

# A pure comment line: first non-whitespace char is `#`. Such a line is a
# comment in BOTH YAML (workflow header) and shell (a `#` line inside a `run:`
# block scalar is a shell no-op comment) -- safe to strip before detection in
# either context. A real command never starts with `#` (echo "# x" starts with
# `echo`), so stripping cannot remove an active label command.
_PURE_COMMENT_LINE_RE = re.compile(r"^\s*#")


def _strip_comment_lines(text: str) -> str:
    """Drop pure-comment lines so the label-poser regexes do not match prose.

    Without this, a workflow that DOCUMENTS the convention in its header (e.g.
    ``# the bot poses a label via gh pr edit --add-label``) is miscounted as a
    label-poser -- inflating the denominator. This very guard's own workflow
    file is the case in point: it mentions the patterns in comments but poses no
    label. Stripping leading-``#`` lines removes that self-count while leaving
    every active ``run:`` command intact (commands do not start with ``#``).
    """
    return "\n".join(
        ln for ln in text.splitlines() if not _PURE_COMMENT_LINE_RE.match(ln)
    )


@dataclass
class WorkflowVerdict:
    """One workflow's guard verdict."""

    path: str  # repo-relative, e.g. .github/workflows/foo.yml
    poses_label: bool
    has_paths: bool
    self_covered: bool
    violation: bool
    detail: str = ""


@dataclass
class GuardResult:
    """Aggregate over all scanned workflows."""

    verdicts: list[WorkflowVerdict] = field(default_factory=list)

    @property
    def violations(self) -> list[WorkflowVerdict]:
        return [v for v in self.verdicts if v.violation]

    def as_payload(self) -> dict:
        n = len(self.verdicts)
        n_label = sum(1 for v in self.verdicts if v.poses_label)
        n_paths = sum(
            1 for v in self.verdicts if v.poses_label and v.has_paths
        )
        n_violations = len(self.violations)
        return {
            "summary": {
                # Denominator FIRST (#8822 criterion 3): a glance shows the
                # coverage. A guard that scanned nothing is blind -- fail.
                "examined": n,
                "label_posers": n_label,
                "path_filtered_label_posers": n_paths,
                "non_covered": n_violations,
            },
            "violations": [asdict(v) for v in self.violations],
            "ok": [
                asdict(v) for v in self.verdicts
                if v.poses_label and v.has_paths and not v.violation
            ],
        }


def _glob_to_regex(pattern: str) -> str:
    """Translate a GitHub Actions ``paths`` glob to an anchored regex.

    GitHub uses gitignore-style globs (``*`` matches within a segment, ``**``
    matches across ``/``). ``pathspec`` is the gold standard but is not a repo
    dependency; this translator covers every pattern observed in the repo's 49
    path-filtered workflows (literal paths, ``.github/workflows/**``,
    ``scripts/**``, ``*.yml``). A leading ``/`` is a no-op (paths are always
    repo-root-relative).
    """
    p = pattern.lstrip("/")
    out: list[str] = []
    i = 0
    while i < len(p):
        two = p[i : i + 2]
        if two == "**":
            out.append(".*")  # across path separators
            i += 2
        elif p[i] == "*":
            out.append("[^/]*")  # within a segment
            i += 1
        elif p[i] == "?":
            out.append("[^/]")
            i += 1
        else:
            out.append(re.escape(p[i]))
            i += 1
    return "".join(out)


def _path_matches(path_globs: list[str], target: str) -> bool:
    """True if ``target`` (repo-relative, forward slashes) matches any glob."""
    for pat in path_globs:
        pat_s = pat if isinstance(pat, str) else str(pat)
        if re.fullmatch(_glob_to_regex(pat_s), target):
            return True
    return False


def _extract_paths(text: str) -> list[str] | None:
    """Return the ``on.pull_request.paths`` list, or None if absent.

    None means "no inclusive paths filter" -- the workflow runs on every PR and
    can always clean up its own labels, so it is out of scope. ``paths-ignore``
    alone does NOT constrain (it excludes rather than includes), so it is
    treated as None too.
    """
    data = yaml.safe_load(text)
    if not isinstance(data, dict):
        return None
    # PyYAML may parse a bare `on:` key as True under the YAML 1.1 spec; handle
    # both spellings.
    trigger = data.get("on", data.get(True))
    if trigger is None:
        return None
    if isinstance(trigger, (str, list)):
        # `on: pull_request` or `on: [push, pull_request]` -- no per-event
        # config block, hence no paths filter.
        return None
    if not isinstance(trigger, dict):
        return None
    pr = trigger.get("pull_request")
    if not isinstance(pr, dict):
        return None
    paths = pr.get("paths")
    if paths is None:
        return None
    if isinstance(paths, str):
        paths = [paths]
    return [str(p) for p in paths]


def classify_workflow(repo_root: Path, wf_path: Path) -> WorkflowVerdict:
    """Classify one workflow file against the self-cover invariant."""
    rel = wf_path.relative_to(repo_root).as_posix()
    text = wf_path.read_text(encoding="utf-8", errors="replace")

    # Detect label-posing on comment-stripped text: a workflow that only
    # DOCUMENTS the gh pattern (header comment) must not count as a label-poser.
    code = _strip_comment_lines(text)
    poses_label = bool(
        LABEL_CREATE_RE.search(code) or ADD_LABEL_RE.search(code)
    )
    paths = _extract_paths(text)
    has_paths = paths is not None
    # Self-coverage only matters when BOTH hold: a label-poser with no paths
    # filter always runs (can clean up); a paths-filtered workflow that poses
    # no label has no label to orphan. The violation is the conjunction:
    # poses_label AND has_paths AND NOT self_covered.
    self_covered = bool(paths is not None and _path_matches(paths, rel))

    violation = poses_label and has_paths and not self_covered
    if violation:
        detail = (
            f"poses a label AND is paths-filtered, but its own path '{rel}' "
            f"is not under on.pull_request.paths -- it cannot re-run (hence "
            f"cannot remove its label) once the matching paths leave the diff. "
            f"Add '- {rel}' to the paths: list."
        )
    elif poses_label and has_paths:
        detail = "self-covered (own path in paths:)."
    elif poses_label and not has_paths:
        detail = "poses a label but has NO paths filter -- always runs, OK."
    else:
        detail = "poses no label -- not subject to the guard."

    return WorkflowVerdict(
        path=rel,
        poses_label=poses_label,
        has_paths=has_paths,
        self_covered=self_covered,
        violation=violation,
        detail=detail,
    )


def scan(repo_root: Path) -> GuardResult:
    """Scan ``repo_root/.github/workflows/*.yml`` and classify each."""
    wf_dir = repo_root / WORKFLOWS_DIR
    result = GuardResult()
    # Sorted for stable, reproducible output (deterministic denominators).
    files = sorted(wf_dir.glob("*.yml")) + sorted(wf_dir.glob("*.yaml"))
    seen: set[str] = set()
    for wf in files:
        if not wf.is_file():
            continue
        key = wf.name
        if key in seen:  # .yml + .yaml twins -- rare, dedup by name
            continue
        seen.add(key)
        result.verdicts.append(classify_workflow(repo_root, wf))
    return result


def _render_text(result: GuardResult) -> str:
    p = result.as_payload()["summary"]
    lines = [
        f"Workflows examined          : {p['examined']}",
        f"Label posers                : {p['label_posers']}",
        f"  ...filtered by paths:     : {p['path_filtered_label_posers']}",
        f"Non-self-covered (VIOLATION): {p['non_covered']}",
    ]
    if result.violations:
        lines.append("")
        lines.append("--- VIOLATIONS (label + paths but not self-covered) ---")
        for v in result.violations:
            lines.append(f"  {v.path}")
            lines.append(f"      {v.detail}")
    # The self-covered label-posers are the positive evidence the guard is not
    # blanket-flagging every path-filtered workflow (#8822 criterion 2).
    ok_posers = [
        v for v in result.verdicts if v.poses_label and v.has_paths
        and not v.violation
    ]
    if ok_posers:
        lines.append("")
        lines.append("--- Self-covered label-posers (pass) ---")
        for v in ok_posers:
            lines.append(f"  {v.path} -- {v.detail}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Guard (#8822): a paths-filtered, label-posing workflow MUST list "
            "its own path under on.pull_request.paths (so it can re-run and "
            "remove its own label). BLOCKING -- exits 1 on violation."
        ),
    )
    parser.add_argument(
        "--root", default=".",
        help="Repository root (default: current dir). Scans <root>/.github/workflows.",
    )
    parser.add_argument(
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON.",
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.root).resolve()
    result = scan(repo_root)
    p = result.as_payload()["summary"]

    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2, ensure_ascii=False))
    else:
        print(_render_text(result))

    # Criterion 3: a guard that scanned nothing is blind -- fail loudly.
    if p["examined"] == 0:
        print(
            "\nFAIL: scanned 0 workflows under "
            f"{repo_root / WORKFLOWS_DIR} -- the guard is blind "
            "(wrong root? missing dir?). A gate that enumerates nothing is "
            "green for the wrong reason (#8678/#8680).",
            file=sys.stderr,
        )
        return 1
    # Criterion 4: blocking. Any self-cover violation is a structural defect.
    if result.violations:
        print(
            f"\nFAIL: {len(result.violations)} workflow(s) pose a label and are "
            "paths-filtered but do not self-cover -- they cannot remove their "
            "own label once the matching paths leave the PR diff (#8822).",
            file=sys.stderr,
        )
        return 1
    # Verdict to stderr so stdout is pure data: in --json mode stdout holds ONLY
    # the JSON document (a trailing PASS line would corrupt `json.loads`); in
    # human mode stdout holds the report. Either way the verdict is a diagnostic.
    print(
        "\nPASS: every paths-filtered label-poser self-covers its own file.",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
