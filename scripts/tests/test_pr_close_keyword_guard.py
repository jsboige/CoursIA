#!/usr/bin/env python3
r"""Unit tests for ``pr_close_keyword_guard.py`` (#10101).

Acceptance point 4 (no network): the resolver is **injected** as a table,
so these tests never call ``gh``. They cover the seven mandated cases from
#10101:

  - ``Closes #<issue>``         -> PASS  (intended close, catalog-pr-hygiene HARD 4)
  - ``Closes #<PR>``            -> BLOCK (closing a PR by keyword is never intended)
  - specimen ``CLOSED <PR> ... without merging it`` -> BLOCK (the #10094 incident)
  - the nine keyword flexions  -> each blocks when N is a PR
  - ``#N`` without a keyword    -> PASS  (bare reference is not an auto-close)
  - non-existent number         -> PASS + WARN (fail-open, not a crash)
  - API error                   -> PASS + WARN (fail-open on a network blip)
"""
import json
import sys
from pathlib import Path

# Make ``scripts/ci`` importable (sibling of ``scripts/tests``).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pr_close_keyword_guard as pkg  # noqa: E402


def _table_resolver(table: dict):
    """Build an injectable resolver from ``{number: kind}``; unmapped -> 'missing'."""
    return lambda n: table.get(n, "missing")


# --- acceptance #4: Closes #<issue> PASSES (intended close) -----------------

def test_closes_issue_passes():
    body = "This PR refactors the search module. Closes #42"
    verdict = pkg.check(body, resolver=_table_resolver({42: "issue"}))
    assert verdict["guard_pass"] is True
    assert verdict["hits"] == []
    assert verdict["warnings"] == []  # silence, not even a warning


# --- acceptance #4: Closes #<PR> BLOCKS -------------------------------------

def test_closes_pr_blocks():
    body = "Refactor the search module. Closes #10067"
    verdict = pkg.check(body, resolver=_table_resolver({10067: "pr"}))
    assert verdict["guard_pass"] is False
    assert len(verdict["hits"]) == 1
    assert verdict["hits"][0]["number"] == 10067
    assert verdict["hits"][0]["kind"] == "pr"
    assert verdict["hits"][0]["location"] == "body"
    # acceptance #5: failure message cites the offender AND the remediation
    assert "10067" in verdict["reason"]
    assert "remov" in verdict["reason"].lower() or "without the leading" in verdict["reason"].lower()


# --- acceptance #4: the #10094 specimen BLOCKS ------------------------------
# The exact incident from #10101: a commit claiming it CLOSED a PR "without
# merging it". The number resolves to a PR -> BLOCK. (We scan a commit message,
# matching where #10094's offending text actually lived.)

def test_specimen_closed_pr_without_merging_blocks():
    commit_msg = (
        "chore: drain translation work\n\n"
        "CLOSED #10067 without merging it -- the translation core deliverable."
    )
    verdict = pkg.check(None, commits=[commit_msg],
                        resolver=_table_resolver({10067: "pr"}))
    assert verdict["guard_pass"] is False
    assert verdict["hits"][0]["number"] == 10067
    assert verdict["hits"][0]["keyword"] == "closed"
    assert verdict["hits"][0]["location"] == "commit[0]"


# --- acceptance #4: the NINE flexions each BLOCK when N is a PR -------------

def test_nine_flexions_block():
    flexions = ["close", "closes", "closed", "fix", "fixes", "fixed",
                "resolve", "resolves", "resolved"]
    for kw in flexions:
        body = f"Work done. {kw} #10067 -- done."
        verdict = pkg.check(body, resolver=_table_resolver({10067: "pr"}))
        assert verdict["guard_pass"] is False, f"flexion '{kw}' should block"
        assert verdict["hits"][0]["keyword"] == kw


# --- acceptance #4: #N WITHOUT a keyword PASSES -----------------------------

def test_bare_number_without_keyword_passes():
    body = "Follow-up to PR 10067 and issue #42 for context."
    verdict = pkg.check(body, resolver=_table_resolver({10067: "pr", 42: "issue"}))
    # No closing keyword precedes either number -> nothing to resolve as a hit.
    assert verdict["guard_pass"] is True
    assert verdict["hits"] == []


# --- acceptance #4: non-existent number FAILS-OPEN (warn, not crash) --------

def test_nonexistent_number_fails_open():
    body = "Cleanup. Closes #99999 (old ref)."
    verdict = pkg.check(body, resolver=_table_resolver({}))  # 99999 -> missing
    assert verdict["guard_pass"] is True  # fail-open, not blocking
    assert len(verdict["warnings"]) == 1
    assert "99999" in verdict["warnings"][0]
    assert "missing" in verdict["warnings"][0]


# --- acceptance #4: API error FAILS-OPEN (warn, not crash) ------------------

def test_api_error_fails_open():
    def error_resolver(_n):
        return "error"
    body = "Cleanup. Closes #10067."
    verdict = pkg.check(body, resolver=error_resolver)
    assert verdict["guard_pass"] is True  # fail-open on network blip
    assert len(verdict["warnings"]) == 1
    assert "error" in verdict["warnings"][0]


# --- extra: body empty / no refs -> PASS ------------------------------------

def test_empty_body_passes():
    assert pkg.check("", resolver=_table_resolver({}))["guard_pass"] is True
    assert pkg.check(None, resolver=_table_resolver({}))["guard_pass"] is True


# --- extra: an ISSUE and a PR in the same body -> BLOCKS on the PR ----------

def test_mixed_issue_and_pr_blocks_on_pr():
    body = "Refactor. Closes #42 (issue) and closes #10067 (pr)."
    verdict = pkg.check(body, resolver=_table_resolver({42: "issue", 10067: "pr"}))
    assert verdict["guard_pass"] is False
    assert len(verdict["hits"]) == 1
    assert verdict["hits"][0]["number"] == 10067  # only the PR blocks


# --- extra: commit-message-only block (the #10094 path) ---------------------

def test_commit_message_only_blocks():
    commits = ["fix: thing", "Docs done. fixed #10067"]
    verdict = pkg.check(None, commits=commits,
                        resolver=_table_resolver({10067: "pr"}))
    assert verdict["guard_pass"] is False
    assert verdict["hits"][0]["location"] == "commit[1]"


# --- extra: CLI end-to-end with a table resolver monkeypatch ----------------

def test_cli_blocks_on_pr(tmp_path, monkeypatch):
    body_file = tmp_path / "body.txt"
    body_file.write_text("Done. closes #10067", encoding="utf-8")
    # Inject the table resolver so the CLI path needs no network.
    monkeypatch.setattr(pkg, "gh_resolver", _table_resolver({10067: "pr"}))
    rc = pkg.main(["--body-file", str(body_file)])
    assert rc == 1  # BLOCKING exit


def test_cli_passes_on_issue(tmp_path, monkeypatch):
    body_file = tmp_path / "body.txt"
    body_file.write_text("Done. closes #42", encoding="utf-8")
    monkeypatch.setattr(pkg, "gh_resolver", _table_resolver({42: "issue"}))
    rc = pkg.main(["--body-file", str(body_file)])
    assert rc == 0


if __name__ == "__main__":
    # Allow ``python test_pr_close_keyword_guard.py`` to run directly.
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
