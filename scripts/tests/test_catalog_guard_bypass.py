"""Tests for the catalog-guard.yml bypass logic (issue #10421).

The guard used to exempt by author (`github-actions[bot]`) only. The
GH006 cap on the bot creating PRs (#10136) forces a human author to open
the long-lived PR, so the author-based bypass became structurally wrong:
it let the legitimate catalog-delivery vehicle through by accident when
the bot pushed, but rejected it when a human re-pushed the same branch
under #10348. Issue #10421 adds a branch-based exemption (the PR head
ref) and keeps the author-based bypass as belt-and-braces.

These tests are schema-yaml (the run block of catalog-guard.yml lives
inline and isn't a Python module), so they exercise the bypass logic via
a subprocess that runs the script fragment with controlled env. The
fragment is extracted from the YAML at test setup so the tests stay
synchronized with the workflow.

Acceptance criteria from #10421 acceptance note:
  - feature PR by human author on a feature branch -> FAIL_NO_BYPASS
  - PR from chore/catalog-refresh-pending (human author) -> BYPASS_BRANCH
  - PR from chore/translation-sync-pending (human author) -> BYPASS_BRANCH
  - PR by github-actions[bot] on any branch -> BYPASS_AUTHOR (legacy)
  - workflow_dispatch (no PR_HEAD_REF) -> BYPASS_DISPATCH
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GUARD_YAML = REPO_ROOT / ".github/workflows/catalog-guard.yml"


def _run_block() -> str:
    """Extract the `run:` block of the 'Check for catalog file changes' step.

    Returns the bash shell fragment that decides whether to bypass. The
    fragment sits between `run: |` and the next sibling step / completion
    of the `check` job; we slice by anchor lines, not by depth counting,
    so the extraction tolerates any future whitespace tweaks.
    """
    text = GUARD_YAML.read_text(encoding="utf-8")
    m = re.search(
        r"id:\s+check\n\s*env:\n[\s\S]+?run:\s*\|\n(?P<body>.*?)(?=^[^\s].*run:|\Z)",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if not m:
        raise RuntimeError("could not parse catalog-guard.yml `check` step")
    return m.group("body")


def _should_bypass(env: dict) -> str:
    """Run the bypass logic with the given env and return the verdict.

    The script emits a GitHub Actions notice via `::notice title=...`
    on a bypass path, or runs silently to the file-diff step on the
    fail-to-bypass path. We classify the output as one of:
      `BRANCH`     - branch-based bypass matched
      `AUTHOR`     - author-based bypass matched
      `DISPATCH`   - workflow_dispatch bypass matched
      `FAIL`       - no bypass clause matched; the rest of the script
                     (the 3-dot diff + violation check) runs
    """
    script = _run_block()
    full_env = {**os.environ, **env, "GITHUB_OUTPUT": os.devnull}
    result = subprocess.run(
        ["bash", "-c", script],
        env=full_env,
        capture_output=True,
        text=True,
        timeout=10,
    )
    out = result.stdout or ""
    if "is automation-owned" in out:
        return "BRANCH"
    if "is github-actions[bot]" in out:
        return "AUTHOR"
    if "Manual dispatch" in out:
        return "DISPATCH"
    return "FAIL"


def test_feature_pr_with_human_author_fails():
    """A feature PR attempting to modify catalog files must NOT bypass."""
    verdict = _should_bypass({
        "PR_HEAD_REF": "feature/c10421-catalog-skip-ci",
        "PR_AUTHOR": "jsboige",
        "GITHUB_EVENT_NAME": "pull_request",
    })
    assert verdict == "FAIL", (
        f"feature PR must not bypass; got {verdict!r}"
    )


def test_catalog_refresh_pending_branch_bypasses():
    """The cron delivery branch must bypass the guard (head ref basis)."""
    verdict = _should_bypass({
        "PR_HEAD_REF": "chore/catalog-refresh-pending",
        "PR_AUTHOR": "jsboige",  # human author -- the GH006 consequence
        "GITHUB_EVENT_NAME": "pull_request",
    })
    assert verdict == "BRANCH", (
        f"long-lived catalog branch must bypass; got {verdict!r}"
    )


def test_translation_sync_pending_branch_bypasses():
    """The translation-sync delivery branch must bypass the guard."""
    verdict = _should_bypass({
        "PR_HEAD_REF": "chore/translation-sync-pending",
        "PR_AUTHOR": "jsboige",
        "GITHUB_EVENT_NAME": "pull_request",
    })
    assert verdict == "BRANCH", (
        f"long-lived translation branch must bypass; got {verdict!r}"
    )


def test_github_actions_bot_author_bypasses():
    """Belt-and-braces: bot author still bypasses (legacy contract)."""
    verdict = _should_bypass({
        "PR_HEAD_REF": "feature/something-else",
        "PR_AUTHOR": "github-actions[bot]",
        "GITHUB_EVENT_NAME": "pull_request",
    })
    assert verdict == "AUTHOR", (
        f"bot author must bypass; got {verdict!r}"
    )


def test_workflow_dispatch_bypasses():
    """Manual maintainer dispatch bypasses (no PR context).

    The original catalog-guard.yml used inline `${{ github.event_name }}`
    interpolation for the dispatch check, which the test harness can't
    resolve. We assert the equivalent condition by setting
    GITHUB_EVENT_NAME=workflow_dispatch AND stripping the
    github.event_name literal from a copy of the script -- this is the
    test harness's job, not a code change.
    """
    import re as _re

    script = _run_block()
    # The original script uses inline ${{ github.event_name }}, which
    # GitHub Actions expands at runtime. For the test harness we
    # rewrite that one interpolation to read $GITHUB_EVENT_NAME,
    # matching the env-var pattern that #10421 enforces for head ref.
    script = _re.sub(
        r"\{\{\s*github\.event_name\s*\}\}",
        "GITHUB_EVENT_NAME",
        script,
    )
    # Disable 'set -u' for this test -- workflow_dispatch has no PR
    # context, so PR_HEAD_REF is unset. We don't want the bypass
    # detection to fail on that variable, only on the dispatch check.
    script = "set -eo pipefail\n" + script.replace("set -euo pipefail", "", 1)
    full_env = {**os.environ, "GITHUB_OUTPUT": os.devnull,
                "GITHUB_EVENT_NAME": "workflow_dispatch"}
    result = subprocess.run(
        ["bash", "-c", script],
        env=full_env,
        capture_output=True,
        text=True,
        timeout=10,
    )
    out = result.stdout or ""
    assert "Manual dispatch" in out, (
        f"workflow_dispatch must bypass; got: {out!r}\nstderr: {result.stderr!r}"
    )


def test_branch_check_precedes_author_check():
    """Sanity: a long-lived branch by the bot still routes to BRANCH.

    The branch check is the first `case` in the script, so it must win
    over the author check. If a future refactor reorders them, this
    test catches it before the catalog is blocked again.
    """
    verdict = _should_bypass({
        "PR_HEAD_REF": "chore/catalog-refresh-pending",
        "PR_AUTHOR": "github-actions[bot]",
        "GITHUB_EVENT_NAME": "pull_request",
    })
    assert verdict == "BRANCH", (
        f"branch check must precede author check; got {verdict!r}"
    )
