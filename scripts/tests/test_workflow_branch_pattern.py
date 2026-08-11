#!/usr/bin/env python3
"""Tests for the bot-branch delivery pattern (.github/workflows/*).

Issue #10136 (GH006 / `PR gate` blocks bot push to main): catalog-cron.yml
and translation-sync.yml used to do `git push origin HEAD:main` directly.
That fails on main's branch protection because the `PR gate` status check is
required and a `schedule:` (or `push:` on main itself) trigger never produces
that check. The structural fix is to push to a long-lived branch
(`chore/<name>-pending`) and open / update a PR via github-script.

This test pins the pattern:

  (1) neither workflow pushes directly to main;
  (2) both workflows use a long-lived `chore/<name>-pending` branch;
  (3) both workflows open / update a PR via github-script;
  (4) the push step hard-fails on rejection (no silent skip).

It does NOT execute the workflows — it parses the YAMLs and greps the bash
sections for forbidden / required substrings.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Iterable

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS_DIR = REPO_ROOT / ".github" / "workflows"

CATALOG_CRON = WORKFLOWS_DIR / "catalog-cron.yml"
TRANSLATION_SYNC = WORKFLOWS_DIR / "translation-sync.yml"


def _yaml_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _extract_run_blocks(yaml_text: str) -> list[str]:
    """Return the raw text of every `run: |` shell block (single-line or multi).

    Matches the `run:` directive (with pipe or folded scalar) and captures the
    block contents. We do not parse YAML structurally here because the goal is
    a SUBSTRING pin over the actual shell text — yaml round-trip through
    PyYAML would lose the `# comment` lines that matter for the lint.
    """
    blocks: list[str] = []
    # The pattern: `run: |` or `run: >` followed by indented lines until the
    # next YAML key (line not indented, starting with optional whitespace then
    # non-space). We grab the run-header's first indented run block, naive but
    # sufficient for these two workflows.
    pattern = re.compile(
        r"(?:^|\n)\s*-?\s*run:\s*[|>][+-]?\s*\n((?:\s+.*\n?)+)", re.MULTILINE
    )
    for match in pattern.finditer(yaml_text):
        blocks.append(match.group(1))
    return blocks


def _extract_github_script_blocks(yaml_text: str) -> list[str]:
    """Return the JS source of every `uses: actions/github-script` step."""
    blocks: list[str] = []
    pattern = re.compile(
        r"uses:\s*actions/github-script@[^\n]+\n\s+with:\s*\n\s+script:\s*\|\s*\n"
        r"((?:\s{8,}.*\n?)+)",
        re.MULTILINE,
    )
    for match in pattern.finditer(yaml_text):
        blocks.append(match.group(1))
    return blocks


@pytest.fixture(scope="module")
def catalog_cron_text() -> str:
    return _yaml_text(CATALOG_CRON)


@pytest.fixture(scope="module")
def translation_sync_text() -> str:
    return _yaml_text(TRANSLATION_SYNC)


# ---------------------------------------------------------------------------
# (1) Neither workflow pushes directly to main.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,workflow_label",
    [(CATALOG_CRON, "catalog-cron.yml"), (TRANSLATION_SYNC, "translation-sync.yml")],
)
def test_no_direct_push_to_main(workflow_path: Path, workflow_label: str) -> None:
    """No `git push ... HEAD:main` substring anywhere in the workflow.

    A direct push to main from a `schedule:` (catalog-cron) or a `push:` on
    main (translation-sync) trigger is blocked by GH006 because the `PR gate`
    status check is required and neither trigger produces it (issue #10136,
    catalog-cron run 31293765051, 2026-08-09T04:03Z).
    """
    text = _yaml_text(workflow_path)
    # Match `git push ... HEAD:main` with any separator and any options.
    # `git push origin HEAD:main` is the canonical forbidden form.
    forbidden = re.compile(r"git\s+push[^#\n]*HEAD:main", re.IGNORECASE)
    assert not forbidden.search(text), (
        f"{workflow_label}: contains forbidden `git push ... HEAD:main` "
        f"sub-string. Issue #10136 requires the bot to push to a long-lived "
        f"`chore/<name>-pending` branch and open / update a PR via "
        f"github-script. First match: {forbidden.search(text).group(0)!r}"
    )


# ---------------------------------------------------------------------------
# (2) Both workflows push to a long-lived chore/<name>-pending branch.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,branch,workflow_label",
    [
        (CATALOG_CRON, "chore/catalog-refresh-pending", "catalog-cron.yml"),
        (TRANSLATION_SYNC, "chore/translation-sync-pending", "translation-sync.yml"),
    ],
)
def test_pushes_to_long_lived_branch(
    workflow_path: Path, branch: str, workflow_label: str
) -> None:
    """The push step must target the dedicated long-lived branch.

    The workflow can either inline the branch name (`git push origin
    HEAD:chore/<name>-pending`) or assign it to a bash variable first
    (`BRANCH="chore/<name>-pending"` then `git push origin "HEAD:$BRANCH"`).
    Both patterns are accepted; what matters is the push is NEVER to main.
    """
    text = _yaml_text(workflow_path)
    push_blocks = _extract_run_blocks(text)
    push_block = None
    for block in push_blocks:
        if "git push origin" in block and "HEAD:main" not in block:
            push_block = block
            break
    assert push_block is not None, (
        f"{workflow_label}: no positive push block found (one that does not "
        f"target main)."
    )
    assert branch in text, (
        f"{workflow_label}: branch name {branch!r} does not appear in the "
        f"workflow. The push step must target this branch (whether via "
        f"variable interpolation or literal)."
    )
    # The push block must push to the branch, not to main.
    has_literal = f"HEAD:{branch}" in push_block
    has_via_var = (
        "HEAD:$BRANCH" in push_block
        or "HEAD:${BRANCH}" in push_block
        or "$BRANCH\"" in push_block  # quoted: "HEAD:$BRANCH"
    )
    assert has_literal or has_via_var, (
        f"{workflow_label}: push block does not target {branch!r}. "
        f"Found push block:\n{push_block}"
    )


# ---------------------------------------------------------------------------
# (3) Both workflows open / update a PR via github-script.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,branch,workflow_label",
    [
        (CATALOG_CRON, "chore/catalog-refresh-pending", "catalog-cron.yml"),
        (TRANSLATION_SYNC, "chore/translation-sync-pending", "translation-sync.yml"),
    ],
)
def test_opens_or_updates_pr_via_github_script(
    workflow_path: Path, branch: str, workflow_label: str
) -> None:
    """The workflow must use github-script to open or update the long-lived PR."""
    text = _yaml_text(workflow_path)
    blocks = _extract_github_script_blocks(text)
    assert blocks, (
        f"{workflow_label}: no `actions/github-script` step found. "
        f"Issue #10136 requires the bot to open / update the PR through "
        f"github-script (REST API), not via shell `gh pr create`."
    )
    # All blocks together must mention the long-lived branch AND at least one
    # of the open / update operations.
    joined = "\n".join(blocks)
    assert branch in joined, (
        f"{workflow_label}: github-script block does not mention {branch!r}."
    )
    has_open = "pulls.create" in joined
    has_list = "pulls.list" in joined
    has_comment = "createComment" in joined
    assert has_open and has_list, (
        f"{workflow_label}: github-script must call `pulls.create` (new PR) "
        f"and `pulls.list` (detect existing PR). Found open={has_open}, "
        f"list={has_list}."
    )
    # On subsequent runs an existing PR must be updated (comment at minimum,
    # so a maintainer sees a new commit landed).
    assert has_comment, (
        f"{workflow_label}: github-script must call `createComment` to "
        f"ping the existing PR's maintainer on subsequent pushes."
    )


# ---------------------------------------------------------------------------
# (4) Push step hard-fails on rejection (::error + exit 1).
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,workflow_label",
    [(CATALOG_CRON, "catalog-cron.yml"), (TRANSLATION_SYNC, "translation-sync.yml")],
)
def test_push_hard_fails_on_rejection(
    workflow_path: Path, workflow_label: str
) -> None:
    """The push step must `exit 1` AND echo a `::error` annotation on failure.

    Silent skips hide the GH006 / GH001 failure mode from the Actions tab
    and from on-call maintainers (incident #10136 root cause).
    """
    text = _yaml_text(workflow_path)
    blocks = _extract_run_blocks(text)
    push_block = None
    for block in blocks:
        if "git push origin" in block:
            push_block = block
            break
    assert push_block is not None, (
        f"{workflow_label}: no `git push origin` step found."
    )
    # The push block must check the exit code (via `if !` or explicit $? test)
    # and exit 1 with an ::error annotation.
    assert "::error" in push_block, (
        f"{workflow_label}: push step does not emit `::error` on failure."
    )
    assert "exit 1" in push_block, (
        f"{workflow_label}: push step does not `exit 1` on failure."
    )


# ---------------------------------------------------------------------------
# (5) Concurrency block keeps bot from clobbering its own branch.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,workflow_label",
    [(CATALOG_CRON, "catalog-cron.yml"), (TRANSLATION_SYNC, "translation-sync.yml")],
)
def test_concurrency_block_present(workflow_path: Path, workflow_label: str) -> None:
    """Top-level `concurrency:` block must be present with cancel-in-progress: false."""
    text = _yaml_text(workflow_path)
    # Concurrency block at workflow level (not inside a job).
    pattern = re.compile(
        r"^concurrency:\s*\n(?:\s+\S+.*\n)+", re.MULTILINE
    )
    match = pattern.search(text)
    assert match is not None, (
        f"{workflow_label}: no top-level `concurrency:` block. Two concurrent "
        f"runs would race the push to the long-lived branch and clobber each "
        f"other."
    )
    assert "cancel-in-progress: false" in match.group(0), (
        f"{workflow_label}: concurrency block must use "
        f"`cancel-in-progress: false` (sequential, not cancel-on-collision)."
    )


# ---------------------------------------------------------------------------
# (6) Commit messages carry `[skip ci]` so the bot does not re-trigger.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "workflow_path,workflow_label",
    [(CATALOG_CRON, "catalog-cron.yml"), (TRANSLATION_SYNC, "translation-sync.yml")],
)
def test_skip_ci_in_commit_message(
    workflow_path: Path, workflow_label: str
) -> None:
    """Bot commits must include `[skip ci]` to prevent infinite loops."""
    text = _yaml_text(workflow_path)
    assert "[skip ci]" in text, (
        f"{workflow_label}: bot commit message must contain `[skip ci]` to "
        f"prevent the workflow from re-firing on its own push."
    )


# ---------------------------------------------------------------------------
# (7) The `Prepare` step does NOT rebase on origin/main.
#     Issue #10373 (12 failed runs 2026-08-10): rebasing the previous bot
#     commit on a fresh main produces structural add/add conflicts as soon as
#     any human PR lands a derived file (rendered notebook or CSV). The fix
#     is an unconditional reset (`git checkout -B <branch> origin/main`) -- the
#     bot commit holds no curated state worth preserving because T1->T4
#     regenerate the full derived set, and the cron workflows regenerate the
#     catalog from origin/main directly. This test pins that invariant.
# ---------------------------------------------------------------------------

PREPARE_STEP_RE = re.compile(
    # `- name: Prepare ...` step, capture the run block following it
    r"(?P<header>- name: Prepare [^\n]*\n\s+run:\s*\|\s*\n)"
    r"(?P<body>(?:\s+.*\n?)+)"
)


def _prepare_run_block(yaml_text: str) -> str:
    """Return the run block of the `Prepare chore/...-pending branch` step."""
    match = PREPARE_STEP_RE.search(yaml_text)
    assert match is not None, "no `Prepare ...-pending branch` step found"
    return match.group("body")


@pytest.mark.parametrize(
    "workflow_path,workflow_label",
    [(CATALOG_CRON, "catalog-cron.yml"), (TRANSLATION_SYNC, "translation-sync.yml")],
)
def test_prepare_step_does_not_rebase(
    workflow_path: Path, workflow_label: str
) -> None:
    """The `Prepare` step must reset onto origin/main, never rebase.

    Rebasing the previous bot commit onto a fresh main causes structural
    add/add conflicts (issue #10373, 12 runs failed 2026-08-10). The bot
    commit holds no curated state worth preserving -- the catalog workflows
    regenerate from origin/main directly, and the translation workflow
    regenerates derived files via T1->T4 on every run.
    """
    text = _yaml_text(workflow_path)
    prepare_block = _prepare_run_block(text)
    # Forbidden: `git rebase origin/main` -- the previous failure mode.
    assert "git rebase origin/main" not in prepare_block, (
        f"{workflow_label}: `Prepare` step uses `git rebase origin/main`. "
        f"Issue #10373 shows this fails structurally as soon as any human PR "
        f"touches a derived file. Use `git checkout -B <branch> origin/main` "
        f"instead (unconditional reset). Found:\n{prepare_block}"
    )
    # Required: an unconditional reset to origin/main. Accept `checkout -B`
    # (in-place branch reset) as the canonical form.
    assert "git checkout -B" in prepare_block and "origin/main" in prepare_block, (
        f"{workflow_label}: `Prepare` step must unconditionally reset the "
        f"branch onto origin/main via `git checkout -B <branch> origin/main`. "
        f"Found:\n{prepare_block}"
    )
