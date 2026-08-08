#!/usr/bin/env python3
"""Unit tests for variation_prose_close_guard.py -- the BLOCKING prose
close-keyword gate (#10101).

The #10101 spec: extend the existing `prev:` close-keyword gate (#10093) to
also detect `<mot-cle> #N` in **free prose** (body AND commit messages),
and **discriminate** PR vs issue via an injectable resolver. A PR hit is
blocking; an issue hit is silent (intended closes are catalog-pr-hygiene
HARD 4 territory -- the discipline WANTS them).

The discriminator is the **nature of the N**, not the surface syntax. The
#10093 incident started from `prev: MED/fix #10067` (genre-slot misuse);
the wider hazard is the same shape in prose: the message body or commit
message of #10094 itself contained a `Closes #10067`-shaped fragment when
the worker transcribed the incident for the audit, and a naive squash of
#10094 would have re-closed #10067.

Run:
    python -m pytest scripts/tests/test_variation_prose_close_guard.py
"""
import sys
from pathlib import Path

# Insert `scripts/ci/` so the script under test is importable from a flat
# `import variation_prose_close_guard` (same convention as the sibling tests).
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_prose_close_guard as vpcg  # noqa: E402


# A small PR/issue resolver pinned by the tests. The Ns of interest are the
# ones the corpus has actually exercised (#10093 issue, #10067 PR, etc.).
def make_resolver(table: dict[int, str]):
    """Build a resolver from an int -> "pr"|"issue" dict, with fail-open on
    anything not in the table (`unknown` -> the gate does NOT block)."""
    def resolve(n: int) -> str:
        return table.get(n, "unknown")
    return resolve


# --- acceptance #4 concrete cases ------------------------------------------

def test_close_issue_passes():
    """`Closes #<issue>` is an INTENDED close: silent (catalog-pr-hygiene
    HARD 4). Gate stays PASS."""
    resolver = make_resolver({10093: "issue"})
    v = vpcg.check(
        "Grain: MED/guard. Closes #10093.",
        resolver=resolver,
    )
    assert v["guard_pass"] is True
    # The issue hit is reported in transparency layer, but it does not block.
    assert len(v["hits"]["issues_allowed"]) == 1
    assert v["hits"]["issues_allowed"][0]["number"] == 10093
    assert v["hits"]["pr"] == []


def test_close_pr_blocks():
    """`Closes #<PR>` is never intended: PRs are merged or explicitly
    closed, not resolved by prose. The gate MUST block."""
    resolver = make_resolver({10067: "pr"})
    v = vpcg.check(
        "Grain: MED/guard. Closes #10067.",
        resolver=resolver,
    )
    assert v["guard_pass"] is False
    assert len(v["hits"]["pr"]) == 1
    assert v["hits"]["pr"][0]["number"] == 10067
    assert "#10067" in v["reason"]
    assert "Remove the keyword" in v["reason"] or "drop the" in v["reason"]


def test_specimen_exact_closed_hash_10067_blocks():
    """The exact symptom from the #10101 spec: `CLOSED <hash>10067 ...` in
    prose, capitalised, without a `prev:` prefix. The discriminator is the
    N (#10067 IS a PR), not the surface form.

    The specimen uses `<hash>10067` (hash symbol + number) -- this is NOT
    what GitHub parses as a reference (the `#` is the trigger). The gate
    is by design `#<N>`-shaped, so the literal `<hash>10067` does NOT
    fire: the gate fires on the equivalent ALARM shape, which is
    `Closes #10067` (the canonical `#N` reproducer).

    What the gate MUST catch is the case where a worker transcribed the
    incident for the audit and wrote a paragraph containing the
    actionable shape -- the form `Closes #<PR>` -- which is the next
    assertion below. This is the #10101 hazard: a worker fixing
    #10094 (a prev-close-keyword PR) documented the original incident
    with a `Closes #10067` sentence that, if it landed in a commit
    message, would have re-closed #10067 at the squash of #10094.
    """
    resolver = make_resolver({10067: "pr"})
    # Case A: the literal `<hash>10067` shape does NOT fire (no `#`).
    # The gate is `#<N>`-shaped, intentionally: GitHub's auto-close
    # parser matches `#<N>`, not bare digit runs.
    body = (
        "Editing this PR is fine. CLOSED <>10067 as a deliberate test -- "
        "do not run CI on it, that PR is fine."
    )
    v = vpcg.check(body, resolver=resolver)
    assert v["guard_pass"] is True, "specimen uses no `#` -- gate is silent by design"
    # Case B: the canonical `#10067` reproducer -- the form GitHub parses
    # as a reference -- DOES fire. This is the actionable shape the gate
    # exists to catch.
    fragment = "Closes #10067 (unintended)"
    v2 = vpcg.check(fragment, resolver=resolver)
    assert v2["guard_pass"] is False
    assert v2["hits"]["pr"][0]["number"] == 10067


def test_all_nine_keyword_inflections():
    """The nine GitHub closing-keyword inflections # all fire on a PR N."""
    resolver = make_resolver({10067: "pr"})
    for kw in ("close", "closes", "closed",
               "fix", "fixes", "fixed",
               "resolve", "resolves", "resolved"):
        body = f"Grain: MED/guard. {kw.capitalize()} #10067."
        v = vpcg.check(body, resolver=resolver)
        assert v["guard_pass"] is False, f"keyword {kw!r} must block on PR N"
        assert v["hits"]["pr"][0]["keyword"] == kw.lower()


def test_hash_without_keyword_passes():
    """A `#N` mention without a close-keyword is innocuous (the discipline
    uses `See #N` / `refs #N` for cross-references). The gate must not
    confuse `See #10067` with `Closes #10067`."""
    resolver = make_resolver({10067: "pr"})
    body = "Grain: MED/guard. See #10067 for context. Related to #10093."
    v = vpcg.check(body, resolver=resolver)
    assert v["guard_pass"] is True


def test_unknown_n_fails_open():
    """A hit whose N cannot be resolved (API blip, transient outage) MUST
    NOT block -- the worker has already pushed the prose, and a blocking
    verdict on a transient error would be a DoS on its own. The gate
    reports the unknown transparently, then passes."""
    resolver = make_resolver({})  # nothing resolved -> "unknown" everywhere
    body = "Grain: MED/guard. Closes #99999."
    v = vpcg.check(body, resolver=resolver)
    assert v["guard_pass"] is True
    assert len(v["hits"]["unknowns"]) == 1
    assert v["hits"]["unknowns"][0]["number"] == 99999


# --- body + commits ---------------------------------------------------------

def test_commit_message_only_blocks():
    """The #10101 hazard in its mirror form: the body is clean, the commit
    message carries the offending `Closes #<PR>`. Same shape as #10093,
    different keyword location (#10093 was `prev:` genre spillover)."""
    resolver = make_resolver({10067: "pr"})
    v = vpcg.check(
        "Grain: MED/guard. See #10067.",
        commits=["fix: transcript", "Closes #10067 (audit logging)."],
        resolver=resolver,
    )
    assert v["guard_pass"] is False
    assert len(v["hits"]["pr"]) == 1
    assert v["hits"]["pr"][0]["commit_index"] == 1
    assert "commit" in v["reason"]


def test_both_body_and_commit_hits_aggregated():
    """Offending prose in BOTH body and commits -> both reported, still blocks."""
    resolver = make_resolver({10067: "pr", 10068: "pr"})
    v = vpcg.check(
        "Closes #10067 (one).",
        commits=["Closes #10068 (two)."],
        resolver=resolver,
    )
    assert v["guard_pass"] is False
    assert len(v["hits"]["pr"]) == 2
    numbers = sorted(h["number"] for h in v["hits"]["pr"])
    assert numbers == [10067, 10068]


# --- the discriminator (nature of N, not surface syntax) -------------------

def test_keyword_inside_identifier_is_not_a_hit():
    """A keyword substring INSIDE a longer identifier (no word boundary)
    is NOT a hit. `prefix` does not match `fix`, `closely` does not match
    `close`, `unfixable` does not match `fix`. The regex uses `\b`
    boundaries so the gate does not fire on every PR that mentions
    `prefix-matching` or `unresolvable`."""
    resolver = make_resolver({10067: "pr"})
    # `prefix` contains `fix` as substring but `\b` rejects it
    # (no word boundary between `pre` and `fix`).
    # `closely` contains `close` but `\b` rejects it.
    # `unfixable` contains `fix` but `\b` rejects it.
    # The body ends with `See #10067` -- `See` is NOT a closing keyword
    # so this stays PASS.
    body = (
        "We use a prefix-based matcher. The closely-related term is "
        "unfixable in this context. See #10067."
    )
    v = vpcg.check(body, resolver=resolver)
    assert v["guard_pass"] is True, (
        f"unexpected hit: {v['hits']!r}"
    )


def test_far_keyword_not_paired_with_far_hash():
    """The gate pairs a keyword with the NEAREST `#N` reference within a
    200-char window. A `Closes #100` followed by a long intervening
    paragraph and then `See #200` should NOT pair the two -- they are
    not the same syntactic unit."""
    resolver = make_resolver({100: "pr", 200: "issue"})
    # 250 'x' chars between the keyword and the hash means the window
    # cap (200) drops the hit.
    body = "Closes #100 " + ("x" * 250) + " #200"
    v = vpcg.check(body, resolver=resolver)
    # The keyword hit at offset 7 IS within 200 chars of `#100`, so it
    # pairs with #100 (a PR in resolver). The block fires on #100.
    assert v["guard_pass"] is False
    assert v["hits"]["pr"][0]["number"] == 100


def test_failure_message_quotes_offending_fragment():
    """Acceptance #5: the failure message must let the worker debug from
    the job log alone. We assert the reason names the offending PR numbers
    and tells the worker what to do."""
    resolver = make_resolver({10067: "pr"})
    v = vpcg.check("Closes #10067", resolver=resolver)
    assert "#10067" in v["reason"]
    # The verbs the worker expects: "Remove" / "drop" / "#".
    lo = v["reason"].lower()
    assert any(w in lo for w in ("remove", "drop", "rewrite"))


# --- empty / inert ----------------------------------------------------------

def test_empty_inputs_pass():
    """Empty body / no commits / None inputs all PASS."""
    assert vpcg.check(None)["guard_pass"] is True
    assert vpcg.check("")["guard_pass"] is True
    assert vpcg.check("", [])["guard_pass"] is True


def test_inert_resolver_always_passes():
    """The default resolver (inert) classifies every N as `issue`, so the
    gate is PASS-by-default offline. This is the safety floor for
    misconfigured runs: a worker who forgets `--resolver-table` gets a
    no-op, not a DoS."""
    v = vpcg.check("Closes #10067. Fixes #99999." * 5)
    assert v["guard_pass"] is True
    # Issues all reported in the transparent layer.
    assert len(v["hits"]["issues_allowed"]) >= 1


# --- commits file I/O -------------------------------------------------------

def test_read_commits_file_passes_through():
    """`_read_commits_file` eats a JSON array of strings, the shape the
    workflow writes via `gh pr view --json commits --jq '[.[].messageBody]'`."""
    import json
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
        json.dump(["commit 1", "Closes #10067 inside", "commit 3"], f)
        path = f.name
    resolver = make_resolver({10067: "pr"})
    v = vpcg.check("clean body", vpcg._read_commits_file(path), resolver=resolver)
    assert v["guard_pass"] is False
    assert v["hits"]["pr"][0]["commit_index"] == 1


def test_read_commits_file_missing_returns_empty():
    """A missing commits file yields an empty list (no commits to scan),
    not an exception. The workflow can supply the flag conditionally."""
    assert vpcg._read_commits_file("/nonexistent/path/commits.json") == []
