#!/usr/bin/env python3
"""Unit tests for resolve_pr_state.py -- single-PR REST lookup (#13735).

The helper exists because GitHub's search API has an indexation lag: a PR
merged minutes ago is invisible to ``gh pr list --search "merged:>=..."``
until the index catches up. The REST endpoint reads straight from the merge
table and has no lag. These tests pin the parser / resolver contract:

  - parse_pr handles the single-line JSON output (the --jq template emits a
    compact JSON object; bodies with embedded CRLF cannot shift the parser
    the way they did with the earlier line-based template)
  - field rename ``merged_at`` -> ``mergedAt`` is normalised server-side
    via the --jq template
  - parse_pr returns None for: empty stdout, invalid JSON, null mergedAt,
    state != closed
  - resolve() returns the parsed dict on success, None on gh failure
  - main() exit 0 on merged, exit 1 on not-merged / not-found

A live-control test (``test_run_gh_argv_is_accepted_by_gh``) is included so
the argv shape is asserted against the real ``gh api`` binary -- the same
control that escaped the `--page` regression in fetch_merged_prs_since.py
for the whole life of that script.
"""
import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import resolve_pr_state as rps  # noqa: E402


# --- parse_pr ---------------------------------------------------------------


def test_parse_pr_normalises_merged_at_to_camel_case():
    """The --jq template renames ``merged_at`` -> ``mergedAt`` server-side so
    callers see the same shape as ``gh pr list --json mergedAt``. parse_pr
    just unpacks what the template emitted."""
    payload = json.dumps({
        "number": 13877,
        "body": "Some PR body",
        "mergedAt": "2026-08-31T23:55:03Z",
        "state": "closed",
    })
    pr = rps.parse_pr(payload)
    assert pr == {
        "number": 13877,
        "body": "Some PR body",
        "mergedAt": "2026-08-31T23:55:03Z",
    }


def test_parse_pr_handles_body_with_embedded_crlf():
    """Real PR bodies from GitHub's web editor contain CRLF (\\r\\n) sequences.
    The earlier line-based template (``.number, .body, .merged_at, .state``)
    shifted its parser alignment on these; the JSON template is line-agnostic
    so embedded newlines and CR characters are preserved verbatim in the
    returned body. This pins that invariant -- a regression here would mean
    callers see a truncated body and could miss keyword matches."""
    payload = json.dumps({
        "number": 13877,
        "body": "line1\r\nline2\r\nline3",
        "mergedAt": "2026-08-31T23:55:03Z",
        "state": "closed",
    })
    pr = rps.parse_pr(payload)
    assert pr is not None
    assert pr["number"] == 13877
    assert "\r\n" in pr["body"], "CRLF body must be preserved verbatim"
    assert pr["mergedAt"] == "2026-08-31T23:55:03Z"


def test_parse_pr_returns_none_for_empty_stdout():
    """gh errored to stderr (e.g. 404); stdout is empty -> no merge evidence."""
    assert rps.parse_pr("") is None
    assert rps.parse_pr("   \n  ") is None


def test_parse_pr_returns_none_for_invalid_json():
    """If gh returned non-JSON (e.g. a raw error message), refuse rather than
    guess -- downstream callers treat None as 'no merge evidence'."""
    assert rps.parse_pr("not json") is None
    assert rps.parse_pr("{ broken json") is None


def test_parse_pr_returns_none_when_merged_at_is_null_or_empty():
    """An open PR has ``merged_at: null`` which the --jq template passes
    through as ``null`` (JSON) or ``""`` (if a caller forgets the field).
    No merge -> no normalised dict -> None."""
    assert rps.parse_pr(json.dumps({"number": 1, "body": "", "mergedAt": None, "state": "open"})) is None
    assert rps.parse_pr(json.dumps({"number": 1, "body": "", "mergedAt": "", "state": "open"})) is None


def test_parse_pr_returns_none_when_state_is_open():
    """An open PR has state=open. No merge evidence -> None."""
    payload = json.dumps({"number": 1, "body": "", "mergedAt": "", "state": "open"})
    assert rps.parse_pr(payload) is None


def test_parse_pr_returns_none_when_state_is_unknown():
    """Defensive: anything that isn't ``closed`` cannot be merged (the merge
    table transitions state to ``closed`` atomically with the merge commit).
    If gh ever emits a future state string we don't know about, refuse rather
    than guess."""
    payload = json.dumps({
        "number": 13877, "body": "",
        "mergedAt": "2026-08-31T23:55:03Z", "state": "merged",
    })
    assert rps.parse_pr(payload) is None


# --- resolve ----------------------------------------------------------------


def test_resolve_returns_dict_on_success():
    """Happy path: gh returns rc=0 with valid JSON payload -> normalised dict."""

    def fake_run(n, repo="jsboige/CoursIA"):
        return 0, json.dumps({
            "number": 13877, "body": "body",
            "mergedAt": "2026-08-31T23:55:03Z", "state": "closed",
        }), ""

    pr = rps.resolve(13877, run=fake_run)
    assert pr == {"number": 13877, "body": "body", "mergedAt": "2026-08-31T23:55:03Z"}


def test_resolve_returns_none_when_gh_fails():
    """gh error -> rc != 0 -> None (caller treats this as "no merge evidence
    via REST"; downstream code falls through to its other sources)."""

    def fake_run(n, repo="jsboige/CoursIA"):
        return 1, "", "gh: Not Found (HTTP 404)"

    assert rps.resolve(99999, run=fake_run) is None


def test_resolve_returns_none_when_pr_is_open():
    """An open PR has mergedAt=null -> parse_pr returns None -> resolve
    returns None. Caller knows the PR exists but is unmerged."""

    def fake_run(n, repo="jsboige/CoursIA"):
        return 0, json.dumps({
            "number": 13877, "body": "body",
            "mergedAt": None, "state": "open",
        }), ""

    assert rps.resolve(13877, run=fake_run) is None


# --- main -------------------------------------------------------------------


def test_main_returns_0_on_merged_pr(capsys):
    """Patched on ``resolve`` (not ``run_gh``): ``resolve`` binds ``run=run_gh``
    as a DEFAULT ARGUMENT evaluated once at definition time -- rebinding
    ``rps.run_gh`` never reaches the call site. The sibling script
    fetch_merged_prs_since.py has the same trap, and ``test_main_returns_1_...
    there`` documents it. Patch the function that ``main`` actually calls."""

    def fake_resolve(n, repo="jsboige/CoursIA"):
        return {"number": 13877, "body": "body", "mergedAt": "2026-08-31T23:55:03Z"}

    original = rps.resolve
    rps.resolve = fake_resolve
    try:
        rc = rps.main(["13877"])
    finally:
        rps.resolve = original
    captured = capsys.readouterr()
    assert rc == 0
    out = json.loads(captured.out.strip())
    assert out["number"] == 13877
    assert out["mergedAt"] == "2026-08-31T23:55:03Z"


def test_main_returns_1_on_not_merged(capsys):
    def fake_resolve(n, repo="jsboige/CoursIA"):
        return None

    original = rps.resolve
    rps.resolve = fake_resolve
    try:
        rc = rps.main(["13877"])
    finally:
        rps.resolve = original
    assert rc == 1
    assert "not merged" in capsys.readouterr().err.lower()


def test_main_returns_1_on_gh_error(capsys):
    def fake_resolve(n, repo="jsboige/CoursIA"):
        return None

    original = rps.resolve
    rps.resolve = fake_resolve
    try:
        rc = rps.main(["99999"])
    finally:
        rps.resolve = original
    assert rc == 1


# --- live control -----------------------------------------------------------


@pytest.mark.skipif(shutil.which("gh") is None, reason="gh binary absent")
def test_run_gh_argv_is_accepted_by_gh():
    """THE control that escaped the `--page` regression in the sibling script
    for its whole life: every other test injects ``run``, so the argv was
    never executed against the real binary. Here we capture the argv and
    assert every flag we pass is one ``gh api`` advertises.

    We do NOT actually hit the network -- we ``raise SystemExit`` to abort
    before the HTTP call. The argv-shape check is the only thing that
    matters; a future PR that adds ``--page`` (or any other fake flag) to
    the argv will fail this test loudly.
    """
    help_out = subprocess.run(
        ["gh", "api", "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    ).stdout

    calls = {}

    def fake_subprocess_run(cmd, **kwargs):
        calls["cmd"] = cmd
        # Do not actually hit the network
        raise SystemExit

    original = subprocess.run
    subprocess.run = fake_subprocess_run
    try:
        try:
            rps.run_gh(13877)
        except SystemExit:
            pass
    finally:
        subprocess.run = original

    cmd = calls["cmd"]
    # argv shape: gh, api, repos/$REPO/pulls/<N>, --jq, <template>
    assert cmd[0] == "gh"
    assert cmd[1] == "api"
    assert cmd[2].startswith("repos/"), cmd[2]
    assert cmd[2].endswith("/pulls/13877"), cmd[2]
    assert cmd[3] == "--jq"
    flags = [tok for tok in cmd if tok.startswith("--")]
    unknown = [f for f in flags if f not in help_out]
    assert not unknown, (
        "run_gh passe des flags que `gh api` n'a pas : {} "
        "(c'est exactement la faute `--page` du module voisin)".format(unknown)
    )
