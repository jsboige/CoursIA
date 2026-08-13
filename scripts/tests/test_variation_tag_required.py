#!/usr/bin/env python3
"""Unit tests for variation_tag_required.py (#10045).

The blocking half of the variation-tag-guard. The existing
`check-variation-tag` job in `.github/workflows/variation-tag-guard.yml`
posts labels (advisory, exit 0); the new blocking job (added by #10045)
exits 1 when the tag is absent OR the lane is missing. This file pins the
PURE decision logic that the workflow calls -- the YAML harness is reviewed
by hand, and the coupling with #10036's `is_advisory()` is documented in the
module docstring of `scripts/ci/variation_tag_required.py`.

Run:
    python -m pytest scripts/tests/test_variation_tag_required.py
"""
from __future__ import annotations

import io
import json
import re
import subprocess
import sys
from pathlib import Path

# Insert `scripts/ci/` so the script under test is importable from a flat
# `import variation_tag_required` (the same convention the existing
# `scripts/tests/test_grain_tag.py` uses for `scripts/grain_tag.py`).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_tag_required as vtr  # noqa: E402


# --- canonical form: required_pass=True -----------------------------------


def test_canonical_grain_tag_with_lane_required_pass():
    """The canonical form MUST pass -- this is the happy path that workers
    follow every cycle. If this fails, every legit PR goes red."""
    v = vtr.check("Grain: MED/guard -- lane myia-po-2023:CoursIA-2 -- prev: LIGHT/audit #10041")
    assert v["required_pass"] is True
    assert v["tier"] == "MED"
    assert v["genre"] == "guard"
    assert v["lane"] == "myia-po-2023:CoursIA-2"
    assert v["reason"] == "tag + lane present"


def test_bold_grain_form_with_lane_required_pass():
    """Bold form (`**Grain:**`) is the variant the coordinator uses; the
    shared extractor must accept it (#9485 acceptance), and the blocking
    half must accept it for free."""
    v = vtr.check("**Grain:** LIGHT/ledger -- lane myia-ai-01:CoursIA")
    assert v["required_pass"] is True
    assert v["tier"] == "LIGHT"
    assert v["genre"] == "ledger"
    assert v["lane"] == "myia-ai-01:CoursIA"


def test_title_form_with_lane_required_pass():
    """Title form (`## Grain` then tag on next line) is exactly the form
    that was invisible to the cap for 38% of merges (#9485 motivation).
    The blocking half must inherit the same tolerance."""
    body = (
        "Title intro.\n\n"
        "## Grain\n\n"
        "`MED/tooling (#10045 cost-honesty)` -- lane `myia-po-2023:CoursIA-2` "
        "-- prev: `MED/tooling #10031`.\n\n"
        "Rest of body."
    )
    v = vtr.check(body)
    assert v["required_pass"] is True
    assert v["tier"] == "MED"
    assert v["genre"] == "tooling"
    assert v["lane"] == "myia-po-2023:CoursIA-2"


# --- missing tag: required_pass=False -------------------------------------


def test_empty_body_blocks():
    """An empty PR body MUST block (no tag at all). The reason text is
    machine-parseable but human-readable for the reviewer at the gate."""
    v = vtr.check("")
    assert v["required_pass"] is False
    assert v["tier"] is None
    assert v["genre"] is None
    assert v["lane"] is None
    assert "empty" in v["reason"].lower()


def test_none_body_blocks():
    """`None` body (caller never read the body) MUST block -- same path as
    empty string. Pinning separately so the `if body is None` branch is
    explicit at review time."""
    v = vtr.check(None)
    assert v["required_pass"] is False
    assert "empty" in v["reason"].lower()


def test_body_with_text_but_no_tag_blocks():
    """A body that has only prose, no Grain tag, MUST block. The form
    is exactly what #10045 measured at 3/10 of the 2026-08-08 cycle
    (`#9967`, `#10027`, `#10030`)."""
    body = (
        "This PR touches the docs in `docs/reference/foo.md`.\n\n"
        "It updates the example to use the new convention.\n"
    )
    v = vtr.check(body)
    assert v["required_pass"] is False
    assert v["tier"] is None
    assert "tag" in v["reason"].lower() or "grain" in v["reason"].lower()


def test_body_with_tag_but_no_lane_blocks():
    """The case #10030 fell into: Grain tag present, NO `lane` token
    anywhere. The coordinator could not attribute the PR to any lane
    even reading the body end-to-end. This MUST block."""
    body = (
        "**Grain:** DEEP/research-code -- bridge #2 (no lane on this line)\n\n"
        "Body text, no lane anywhere."
    )
    v = vtr.check(body)
    assert v["required_pass"] is False
    assert v["tier"] == "DEEP"
    assert v["genre"] == "research-code"
    assert v["lane"] is None
    assert "lane" in v["reason"].lower()


# --- shape discipline: the verdict JSON is what the workflow consumes ------


def test_verdict_keys_present_on_success():
    """The workflow parses the JSON output with `python3 -c 'import json; ...'`.
    Every verdict MUST contain the four keys, regardless of branch -- so a
    downstream regression in the YAML can't silently miss a missing key."""
    v_pass = vtr.check("Grain: MED/guard -- lane myia-po-2023:CoursIA-2")
    v_fail = vtr.check("")
    for v in (v_pass, v_fail):
        assert "required_pass" in v
        assert "reason" in v
        assert "tier" in v
        assert "genre" in v
        assert "lane" in v


def test_reason_is_single_line():
    """The workflow emits the `reason` into a PR comment via heredoc; the
    string MUST not contain newlines (would break the bash quoting)."""
    for body in (
        "Grain: MED/guard -- lane myia-po-2023:CoursIA-2",
        "",
        "Grain: DEEP/research-code -- bridge #2",
        "Just text, no tag at all.",
    ):
        v = vtr.check(body)
        assert "\n" not in v["reason"], f"multiline reason for body={body!r}"


# --- CLI shim: the workflow calls the script via subprocess ---------------


def test_cli_body_file_pass_exit_zero():
    """The workflow writes the body to a file and runs
    `python scripts/ci/variation_tag_required.py --body-file <path>`.
    Pin the END-TO-END behavior on the happy path."""
    fixture = Path(__file__).resolve().parent / "_vtr_fixture_pass.md"
    fixture.write_text(
        "Grain: MED/guard -- lane myia-po-2023:CoursIA-2 -- prev: LIGHT/audit #10041\n",
        encoding="utf-8",
    )
    try:
        proc = subprocess.run(
            [sys.executable, "scripts/ci/variation_tag_required.py", "--body-file", str(fixture)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc.returncode == 0, f"expected exit 0, got {proc.returncode}; stderr={proc.stderr!r}"
        verdict = json.loads(proc.stdout)
        assert verdict["required_pass"] is True
        assert verdict["lane"] == "myia-po-2023:CoursIA-2"
    finally:
        fixture.unlink(missing_ok=True)


def test_cli_body_file_fail_exit_one():
    """End-to-end fail path: empty body -> exit 1 + `required_pass: false`."""
    fixture = Path(__file__).resolve().parent / "_vtr_fixture_fail.md"
    fixture.write_text("", encoding="utf-8")
    try:
        proc = subprocess.run(
            [sys.executable, "scripts/ci/variation_tag_required.py", "--body-file", str(fixture)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc.returncode == 1, f"expected exit 1, got {proc.returncode}; stderr={proc.stderr!r}"
        verdict = json.loads(proc.stdout)
        assert verdict["required_pass"] is False
        assert "empty" in verdict["reason"].lower()
    finally:
        fixture.unlink(missing_ok=True)


def test_cli_stdin_blocks_when_tag_missing():
    """End-to-end via stdin: the workflow alternative path `--stdin`."""
    proc = subprocess.run(
        [sys.executable, "scripts/ci/variation_tag_required.py", "--stdin"],
        input="Just text, no tag.\n",
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 1
    verdict = json.loads(proc.stdout)
    assert verdict["required_pass"] is False


def test_cli_missing_body_file_exits_two():
    """The workflow MUST call with `--body-file` on a path that the
    checkout produced. If the file vanished (rolling branch, race), the
    script must exit 2 (caller error) and write the JSON to stderr --
    distinct from the body-fail exit 1 on stdout."""
    proc = subprocess.run(
        [sys.executable, "scripts/ci/variation_tag_required.py", "--body-file", "/nonexistent/path"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 2
    assert proc.stdout == "", f"stdout should be empty on caller error, got {proc.stdout!r}"
    # The script writes the verdict JSON to stderr on caller-error. Any
    # Python warnings that the interpreter emits about the docstring (e.g.
    # `SyntaxWarning: invalid escape sequence`) come on stderr too -- we
    # tolerate them by extracting the LAST `{...}` JSON object.
    last_open = proc.stderr.rfind("{")
    assert last_open >= 0, f"no JSON in stderr: {proc.stderr!r}"
    payload = json.loads(proc.stderr[last_open:])
    assert payload["required_pass"] is False
    assert "caller error" in payload["reason"]


# --- coupling with #10036 --------------------------------------------------

def test_check_name_is_not_advisory_friendly():
    r"""PR #10036 introduces an `is_advisory()` classifier in
    `scripts/pr_gate.py` that RETURNS `true` for jobs whose name matches
    `/advisory|non[-\s]?blocking|^skip[:\s]|optional/i`. The blocking
    workflow MUST be named `check-variation-tag-required` (the `-required`
    suffix is the explicit signal) so the classifier does NOT silence it.

    This is a HARD contract on the file we own -- the gate of #10045
    depends on the workflow name not drifting to something the
    classifier would absorb. The corresponding test lives in PR #10036."""
    workflow_path = (
        Path(__file__).resolve().parents[2] / ".github" / "workflows" / "variation-tag-guard.yml"
    )
    if not workflow_path.exists():
        # Running outside a checkout (rare): skip the source check.
        return
    text = workflow_path.read_text(encoding="utf-8")
    assert "check-variation-tag-required" in text, (
        "The blocking job must be named `check-variation-tag-required` so "
        "PR #10036's `is_advisory()` classifier does NOT absorb it. Rename "
        "the job in `.github/workflows/variation-tag-guard.yml`."
    )
    # And it must NOT be wrapped in `if: ...` clauses that gate it on
    # something other than the body content (e.g. folder filters).
    # The simplest audit: no `paths:` filter as an actual YAML KEY on the
    # workflow. (The string appears in COMMENTS that explain the rule --
    # we look for `paths:` at the start of a line, indented under the
    # top-level `on:` block where the filter would actually be parsed.)
    # The cheapest deterministic check: no `paths:` block inside the YAML
    # `on:` section. We split on the `on:` section and confirm the
    # remainder has no `paths:` key.
    on_match = re.search(r"^on:\s*$", text, flags=re.MULTILINE)
    assert on_match, "Workflow must declare a top-level `on:` block."
    on_section = text[on_match.start():]
    # The `on:` block ends when the next top-level YAML key starts --
    # a line that begins with two spaces (under `on:`) followed by a
    # top-level keyword like `permissions:` or `jobs:`. We take the
    # simpler heuristic: `paths:` indented at exactly 2 spaces (= the
    # path under `on:.<event>.paths`).
    assert not re.search(r"^  paths:", on_section, flags=re.MULTILINE), (
        "Adding a `paths:` filter on the workflow would make the job "
        "report `pending` forever on PRs outside the filter, which is "
        "the failure mode #10045 explicitly rejects."
    )
