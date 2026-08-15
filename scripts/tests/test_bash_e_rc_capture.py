#!/usr/bin/env python3
"""Non-regression: exit-code capture under `bash -e` (#8894).

Every GitHub Actions `run:` step executes with `/usr/bin/bash -e` (errexit
is ON by default -- `.github/workflows/variation-tag-guard.yml` documents
this itself). The workflow's three BLOCKING jobs capture the helper's exit
code with `RC=$?` on the line AFTER the helper call. Under `-e`, when the
helper exits non-zero -- exactly the BLOCK path that needs the stderr +
verdict JSON + PR comment diagnostics -- bash kills the step BEFORE
`RC=$?` runs. The gate goes red with zero diagnostics: a guard whose
failure is silent is not a guard (#10036).

#8894: a unit test cannot observe the interpreter of another job, but it
CAN test the bash semantics themselves. These tests shell out to the real
`bash -e` to prove (1) the bug exists, (2) the `&& RC=0 || RC=$?` fix
survives both branches, (3) the naive `|| RC=$?` alone has its own trap
under the workflow's `set -u`, and (4) the YAML no longer contains the
buggy pattern.

Run:
    python -m pytest scripts/tests/test_bash_e_rc_capture.py
"""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest

WORKFLOW = (
    Path(__file__).resolve().parents[2]
    / ".github"
    / "workflows"
    / "variation-tag-guard.yml"
)

# The three BLOCKING jobs of variation-tag-guard.yml that capture a helper
# exit code. Each must pair its invocation with `&& RC=0 || RC=$?`.
BLOCKING_HELPERS = [
    "python3 scripts/ci/variation_tag_required.py",
    "python3 scripts/ci/variation_prev_guard.py",
    "python3 scripts/ci/pr_close_keyword_guard.py",
]

# Resolve bash ONCE, explicitly. On Windows, `subprocess.run(["bash", ...])`
# does its own CreateProcess PATH search that can land on
# `C:\Windows\System32\bash.exe` -- the WSL launcher stub, which mangles the
# `-c` argument (shell assignments silently vanish, e.g. `A=1` never takes
# effect). `shutil.which` returns the first PATH hit (Git's bash), which is
# also the bash the workflow's `/usr/bin/bash` semantics are modeled on.
BASH = shutil.which("bash") or "bash"


def _run_bash_e(script: str) -> subprocess.CompletedProcess:
    """Run `script` under the exact errexit semantics of a workflow step."""
    return subprocess.run(
        [BASH, "-e", "-c", script],
        capture_output=True,
        text=True,
    )


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash not available")
def test_semicolon_rc_masks_the_failure_under_errexit():
    """The buggy `cmd ; RC=$?` dies at `cmd`: RC never assigned, the code
    after never runs -- the mute red gate."""
    r = _run_bash_e('false ; RC=$?; echo "REACHED $RC"')
    assert r.returncode == 1  # bash -e kills the step
    assert "REACHED" not in r.stdout  # diagnostics after `;` never surface


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash not available")
def test_and_or_idiom_captures_rc_on_both_branches():
    """`cmd && RC=0 || RC=$?` assigns RC on success AND failure, and a
    `&&`/`||` list is exempt from errexit -- the step survives the BLOCK
    path and still surfaces the real exit code."""
    ok = _run_bash_e('true && RC=0 || RC=$?; echo "RC=$RC"')
    assert ok.returncode == 0
    assert "RC=0" in ok.stdout

    blocked = _run_bash_e('false && RC=0 || RC=$?; echo "RC=$RC"')
    assert blocked.returncode == 0  # the step survives
    assert "RC=1" in blocked.stdout  # the real exit code is captured


@pytest.mark.skipif(shutil.which("bash") is None, reason="bash not available")
def test_naive_or_rc_alone_is_unbound_under_set_u():
    """`cmd || RC=$?` alone short-circuits on success: RC is never assigned,
    and the workflow's `set -u` turns the next `$RC` use into an error.
    This is why the fix is the `&&`/`||` pair, not a bare `||`."""
    r = _run_bash_e('set -u; true || RC=$?; echo "RC=$RC"')
    assert r.returncode != 0
    assert "unbound" in r.stderr.lower()


def test_workflow_uses_the_idiom_and_has_no_buggy_pattern():
    """Static guard on the YAML: the `; RC=$?` pattern is banned and each
    blocking helper invocation pairs with `&& RC=0 || RC=$?`."""
    yaml = WORKFLOW.read_text(encoding="utf-8")
    assert "; RC=$?" not in yaml
    for invocation in BLOCKING_HELPERS:
        assert invocation in yaml
        idx = yaml.index(invocation)
        assert "&& RC=0 || RC=$?" in yaml[idx : idx + 800]
