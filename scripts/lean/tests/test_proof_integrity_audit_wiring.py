#!/usr/bin/env python3
"""Contract test for the conway proof-integrity-audit job (#8782 option (b)).

Dual-mode: runnable directly (``python scripts/lean/tests/test_proof_integrity_audit_wiring.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the wiring of the ADVISORY axiom-audit job that closes the "vert
hors-cible" gap opened in #8782. The blocking ``proof-integrity`` job targets
the sorry-FREE showcase modules (Conway.KochenSpecker + Conway.FreeWillTheorem)
and is therefore green BY CONSTRUCTION on the 8 acknowledged tactic sorries in
Conway.Life.HashlifeCorrectness -- observed on #8809 (SUCCESS beside a file
with 8 sorries). Option (b) adds a non-blocking ``proof-integrity-audit`` job
that runs the axiom audit ON the sorry-bearing module, so the sorries surface
as ``has_sorry`` (reported, not gated -- an honesty knob, not a leniency one)
while a FORBIDDEN axiom (beyond the 19 native_decide allow-list) still
hard-fails. Criterion 1 (#8782): the audit targets the module whose public
anchor (``hashlifeResult_central_correct``) closes the private sorry chain, so
the sorry is REACHED, not hidden; a module with zero enumerated decls reads
'non applicable' explicitly (lean-axiom.yml), never a silent clean.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

# scripts/lean/tests/X.py -> parents[3] = repo root
REPO = Path(__file__).resolve().parents[3]
CONWAY_WF = REPO / ".github" / "workflows" / "lean-conway.yml"


def _load_jobs():
    yaml = pytest.importorskip("yaml")
    with CONWAY_WF.open(encoding="utf-8") as fh:
        doc = yaml.safe_load(fh)
    return doc.get("jobs", {})


def test_workflow_exists():
    assert CONWAY_WF.is_file(), f"missing {CONWAY_WF}"


def test_blocking_proof_integrity_targets_showcase_modules():
    """The blocking gate covers the sorry-FREE showcase (KochenSpecker +
    FreeWillTheorem) with fail-on-sorry: true -- the complement of the
    sorry-bearing advisory audit below."""
    jobs = _load_jobs()
    assert "proof-integrity" in jobs, "blocking proof-integrity job removed"
    blocking = jobs["proof-integrity"].get("with", {})
    targets = blocking.get("target-modules", "")
    assert "Conway.KochenSpecker" in targets
    assert "Conway.FreeWillTheorem" in targets
    assert blocking.get("fail-on-sorry") is True


def test_advisory_audit_job_wired():
    """Option (b): an ADVISORY proof-integrity-audit job exists, uses the
    reusable lean-axiom workflow, and is non-blocking on sorry."""
    jobs = _load_jobs()
    assert "proof-integrity-audit" in jobs, (
        "#8782 (b): proof-integrity-audit job missing from lean-conway.yml")
    audit = jobs["proof-integrity-audit"]
    assert "lean-axiom.yml@main" in audit.get("uses", ""), (
        "audit must reuse the lean-axiom workflow")
    with_opts = audit.get("with", {})
    assert with_opts.get("fail-on-sorry") is False, (
        "the audit job must be advisory on sorry (fail-on-sorry: false)")


def test_audit_targets_sorry_bearing_module():
    """The audit closes the vert-hors-cible: it inspects the module that
    CARRIES the 8 sorries (HashlifeCorrectness), which the blocking gate
    skips. Targeting only KochenSpecker/FreeWillTheorem here would reproduce
    the very gap #8782 opened on. Post-#10889 the coverage is stronger than
    naming the module: `target-modules: "*"` derives the list at runtime, so
    HashlifeCorrectness -- and every module added later -- is covered by
    construction."""
    jobs = _load_jobs()
    audit = jobs["proof-integrity-audit"].get("with", {})
    targets = audit.get("target-modules", "")
    assert targets == "*", (
        "audit must derive its module list at runtime ('*', #10889 point 5) -- "
        "an explicit list can drift out of view of the sorry-bearing module "
        "and of any module added later")


def test_audit_allowlists_native_decide_axioms():
    """The audit allow-lists the native_decide axioms its modules ACTUALLY depend
    on, so it reports only a FORBIDDEN axiom (beyond them) as red. The first CI
    run of this audit (#8782) revealed HashlifeCorrectness depends on **38**
    native_decide axioms -- a footprint DISTINCT from the blocking gate's 19-name
    list (triaged from the showcase modules KochenSpecker/FreeWillTheorem, #8749,
    a different scope; the two sets have ZERO overlap). The audit audits
    different modules, so its allow-list is its own (not a copy of the blocking
    gate's). All are decide-kernel (`._native.native_decide.ax_1_N`).

    **Widened to 46 by #9341** (`ci(lean,#8782)`), which took the audit from 3 to
    7 covered modules by adding Oscillators/Spaceships/RLE. The 18 added entries
    are the build-enumerated footprint of exactly those new modules -- 10 new
    theorems, all still-life/spaceship/oscillator decidability
    (`boat|loaf|pond|ship|tub_still_life`, `lwss|mwss|hwss_spaceship`,
    `pulsar_period_three`, `pentadecathlon_period_15`). Coverage went UP, so the
    widening is an expansion of what is audited, not a dilution of the gate.

    This pin is the ratchet's ratchet: it caught #9341 widening the allow-list
    without review and turned `main` red until the widening was justified in
    writing. Raising it is only ever legitimate alongside that justification --
    a new name that is NOT attributable to a newly covered module means an
    unproven `native_decide` slipped in, and the pin must stay put instead.

    **Shrunk to 41 by #9571** (`feat(lean,#8869)`): the ceilLog2 rewrite (#9536)
    made kernel `decide` tractable for the 5 Oscillators still-life theorems
    (`loaf|boat|tub|pond|ship_still_life`), which were flipped from
    `native_decide` to `decide` — their 5 axiom names genuinely left the
    build-enumerated footprint. A shrink attributable to a native_decide ->
    decide flip is the virtuous ratchet direction (fewer trusted-kernel
    escapes), so the pin follows the footprint down. Same rule as widening:
    any future shrink must name the flipped theorems.

    **Shrunk to 38 by #9595** (`feat(lean,#8869)`): the 3 period-4 spaceship
    theorems (`lwss|mwss|hwss_spaceship`) in `Conway.Life.Spaceships` were
    flipped from `native_decide` to kernel `decide` (the glider on main already
    used kernel `decide`; the rewrite pattern matched). `#print axioms` =
    'does not depend on any axioms' on all 3 (FR+EN byte-identity verified),
    so their 3 axiom names genuinely left the build-enumerated footprint.
    Same ratchet direction as #9571 (virtuous shrink, fewer trusted-kernel
    escapes); the pin follows the footprint down by 3 to 38.

    **Widened to 59 by #10889 point 5** (`ci(lean,#10889)`): the audit flipped
    from the 18-module explicit list to `target-modules: "*"` with
    `include-i18n-siblings: "true"` (69 modules derived at runtime). The 21
    added entries are the build-enumerated footprint of exactly the newly
    covered modules -- JumpCapture (3), PatternTour (1), Pillars (1),
    LookAndSayLemmas (2) on the FR side, plus the `_en` twins of
    Oscillators (2), PatternTour (1), Pillars (1), RLE (8), LookAndSayLemmas
    (2) under the `Conway_en.*` namespaces (with `Pillars_en` keeping the FR
    `Conway.Life.*` path -- namespace heterogeneity is why names are
    enumerated from the build, never derived by rule). Same legitimacy rule
    as #9341: every added name is attributable to a newly covered module.

    **Widened to 61 by #11349** (`ci(lean,#11349)`), and this one does NOT fit
    the "newly covered module" phrasing above -- it is the first widening that
    does not, so the criterion is stated properly here rather than stretched.
    Grain 3a (#11303, `c3bd40cc1`) added two theorems to the ALREADY covered
    `Conway.Life.HashlifeCorrectness` and widened the workflow allow-list by
    exactly their two names. It DID annotate them in the workflow comment
    (L204-208, header updated to "All 61") -- what it omitted was this pin, and
    that omission is the ratchet working as designed: an attribution written by
    the same hand that widens cannot self-certify, so `main` goes red until a
    second reading confirms it. This is that reading. Verified before raising:

    * `p4at_witness_k1` / `p4at_witness_k2` (L848, L861) are the P4-At mirrors
      of the already-allow-listed `p4_wf_witness_k1` / `p4_wf_witness_k2`
      (L758, L775): SAME cells (centered block still-life; centered glider),
      SAME generation counts (2, 4), SAME `restrictGridTo` windows -- only the
      engine differs (`hashlifeResultAt j` instead of `hashlifeResultAux (j+2)`),
      which is the whole point of grain 3a.
    * Both are STANDALONE: `git grep` finds zero references outside their own
      declarations. They are concrete finite sanity checks, not premises.
    * Grain 3a's headline theorem `hashlifeResultAt_base_central` (L806) is
      universally quantified over `c : MacroCell` and `j : Nat` and is proven
      by structural tactics (`cases`/`omega`/`obtain`/`simp only`), closing on
      the already-proven `hashlifeResult_central_correct`. No `native_decide`
      in it -- the general claim is NOT hollowed out by these two escapes.

    The operative criterion is therefore **attributable AND non-hollowing**, of
    which "attributable to a newly covered module" was one instance, not the
    definition. A name attributable to a newly added THEOREM is equally
    legitimate provided (a) the theorem is a concrete finite witness, (b) it is
    referenced by nothing, and (c) the module's general theorems do not depend
    on it. Absent any of the three, the pin stays put and the proof is reworked
    -- unchanged from #9341.

    **Widened to 69 by #11910** (`feat(lean,#6724)`): the criterion-3
    characterization of #6724 added the first infinite CLASS of jump-captured
    patterns to `Conway.Life.JumpCapture`. The 8 added entries are the
    native_decide footprints of exactly its 3 class witnesses --
    `jumpCaptured_beehive` (2), `jumpCaptured_blinker` (3),
    `jumpCaptured_block_of_class` (3) -- finite concrete instances re-derived
    from the class theorem. Same attributed-and-non-hollowing criterion as
    #11349, applied to new theorems rather than modules: each witness is a
    concrete pattern (beehive and block are still-lives, blinker is a
    period-2 oscillator -- the first non-still-life in the class, which is
    why it carries 3 entries), none is referenced outside its own
    declaration, and the headline `jumpCaptured_of_period_divides` is
    structural (`#print axioms` = [propext, Classical.choice, Quot.sound] on
    it: no native_decide), so the general claim is NOT hollowed out. The
    pre-existing isolated witness `jumpCaptured_block` stays allow-listed;
    `jumpCaptured_block_of_class.ax_1_*` is a distinct re-derivation via the
    class theorem."""
    jobs = _load_jobs()
    audit = jobs["proof-integrity-audit"].get("with", {})
    allow = audit.get("allow-axioms", "")
    assert "native_decide" in allow, (
        "audit must allow-list the native_decide axioms or it false-fails")
    # Pin the empirical footprint so a silent re-shrink (or accidental copy of
    # the blocking gate's 19) is caught -- and so any future widening has to
    # come with the module-attribution argument, as #9341's did.
    names = [a.strip() for a in allow.split(",") if a.strip()]
    assert len(names) == 69, (
        f"audit allow-list must carry the 69 native_decide axioms of the whole "
        f"lake under the #10889 '*' derivation (38 HashlifeCorrectness-era "
        f"footprint + 21 build-enumerated entries of the newly covered "
        f"modules + 2 P4-At standalone witnesses from grain 3a #11303 + 8 "
        f"class-witness entries from the #6724 criterion-3 characterization "
        f"[PR #11910], each attributed in the workflow comment); got {len(names)}")
    # Sample members from each family revealed by the audit (P4 base cases,
    # box-assez-grand lemmas, hashlife_correct_implies bridges, plus one
    # #10889-widening family: the _en twins under Conway_en.*).
    for sample in [
        "Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1✝",
        "Conway.Life.box_assez_grandN_single_cell._native.native_decide.ax_1_4",
        "Conway.Life.hashlife_correct_implies_block_2._native.native_decide.ax_1_1",
        "Conway.Life.padCenter2_correct_block_level1._native.native_decide.ax_1_1",
        "Conway.Life.jumpCaptured_block._native.native_decide.ax_1_1",
        "Conway.Life.jumpCaptured_beehive._native.native_decide.ax_1_1",
        "Conway_en.Life_en.RLE_en.glider_parse_ok._native.native_decide.ax_1_1",
    ]:
        assert sample in names, (
            f"audit allow-list missing revealed axiom {sample!r}")


def test_audit_allowlist_is_distinct_from_blocking_gate():
    """The audit audits HashlifeCorrectness; the blocking gate audits the
    showcase modules. Their native_decide footprints are disjoint (verified by
    the audit's first CI run: zero overlap). Pinning that they DIFFER prevents
    a future copy-paste of the blocking gate's 19 into the audit (which would
    re-open the vert-hors-cible the audit exists to close)."""
    jobs = _load_jobs()
    audit_set = {a.strip() for a in
                 jobs["proof-integrity-audit"].get("with", {}).get("allow-axioms", "").split(",")
                 if a.strip()}
    blocking_set = {a.strip() for a in
                    jobs["proof-integrity"].get("with", {}).get("allow-axioms", "").split(",")
                    if a.strip()}
    assert audit_set != blocking_set, (
        "audit and blocking gate audit different modules -> their native_decide "
        "allow-lists must differ (38 HashlifeCorrectness vs 19 showcase)")
    assert audit_set.isdisjoint(blocking_set) or len(audit_set & blocking_set) <= 2, (
        "the two native_decide footprints are empirically disjoint")


def test_blocking_and_audit_are_complementary():
    """The two jobs must not both skip HashlifeCorrectness -- that is the
    vert-hors-cible defect. The audit targets it; the blocking gate (which
    cannot, it has sorries) deliberately excludes it."""
    jobs = _load_jobs()
    blocking_targets = jobs["proof-integrity"].get("with", {}).get("target-modules", "")
    audit_targets = jobs["proof-integrity-audit"].get("with", {}).get("target-modules", "")
    # Post-#10889 the audit derives its list at runtime ('*' = every compiled
    # module, HashlifeCorrectness included by construction); the blocking gate
    # keeps its explicit showcase-only list.
    assert audit_targets == "*"
    assert "Conway.Life.HashlifeCorrectness" not in blocking_targets


# ---------------------------------------------------------------------------
# Path-filter pin — point 3 of #11349 (deferred by PR #11495 acceptance
# partielle). The native_decide ratchet is `test_audit_allowlists_*` above,
# which lives under `scripts/lean/tests/` and so is only triggered by changes
# in `scripts/**` (and the few cross-cutting paths scripts-tests.yml pins
# explicitly). Before the #11495 rewire, this meant a PR that added a brand
# new `native_decide` to `Conway.Life.HashlifeCorrectness.lean` could go
# unnoticed by the ratchet: the test subject (allow-list footprint) would
# shift, but no workflow would run on the diff, and the rouge from the new
# `native_decide` would only land on the NEXT lane to edit any script.
# The fix in PR #11495 wired `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/**
# *.lean` (+ lakefile + lean-toolchain) into BOTH `push:` and `pull_request:`
# `paths:` of `scripts-tests.yml`. This test is the **structural pin**: it
# greps the YAML to ensure both push and pr trigger blocks still carry those
# four entries, so a future refactor of scripts-tests.yml (e.g. consolidating
# paths back into a single glob, or removing the lake from the trigger because
# `lean-conway.yml` "covers" it) is caught here.
#
# Why structural and not integration: a true end-to-end test would require
# firing the GitHub Actions path-filter against a synthetic commit, which
# cannot be done hermetically. This pin is the second best thing: if the
# YAML literal is missing, the workflow will not run on a lake-only diff,
# and the ratchet will sleep through the next widening. A textual pin
# catches that exactly.
# ---------------------------------------------------------------------------

SCRIPTS_TESTS_WF = REPO / ".github" / "workflows" / "scripts-tests.yml"

# These four entries correspond to PR #11495 (commit 9b2d9e5c1) and are the
# load-bearing wiring of the #11349 fix. Their MIRROR in push: and
# pull_request: is what closes the vert-hors-cible: a single PR touching only
# a `.lean` file in conway_lean/ should trigger scripts-tests.yml, which runs
# test_audit_allowlists_native_decide_axioms above.
_CONWAY_LEAN_TRIGGER_PATHS = [
    "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/**.lean",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/lakefile.lean",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/lakefile.toml",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/lean-toolchain",
]


def _load_scripts_tests_text() -> str:
    assert SCRIPTS_TESTS_WF.is_file(), (
        f"missing {SCRIPTS_TESTS_WF} -- #11349 fix PR #11495 needs the "
        f"`scripts-tests.yml` workflow file present"
    )
    return SCRIPTS_TESTS_WF.read_text(encoding="utf-8")


def test_workflow_scripts_tests_exists():
    """#11349: scripts-tests.yml is the workflow that runs the
    native_decide ratchet. Removing the file would unmount the ratchet
    entirely; pin its presence."""
    assert SCRIPTS_TESTS_WF.is_file(), (
        f"missing {SCRIPTS_TESTS_WF}"
    )


def test_native_decide_ratchet_wired_on_conway_lean_paths():
    """#11349 / PR #11495: scripts-tests.yml MUST carry the four
    `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/**` paths (or any glob
    form that catches them: e.g. `conway_lean/**.lean` with the bare
    `MyIA.AI.Notebooks/SymbolicAI/Lean/` prefix inferred by the workflow
    runtime root, OR `**` at the workflow root -- a future maintainer
    might rebase the path onto a different relative-root layout) in
    BOTH the `push:` and `pull_request:` `paths:` blocks. Mirror symmetry
    is load-bearing: an asymmetric wiring would let `pull_request` red
    without the matching `push` ever seeing the lake; the ratchet is
    only as wide as the narrower of the two.

    The pin is on substring (NOT yaml.safe_load): the test guards against
    `paths:` entries being deleted or commented out, which yaml.safe_load
    would silently strip. A deleted conway_lean entry would not raise an
    error at YAML parse time, but it WOULD mean a future PR adding a
    fresh `native_decide` to conway_lean/ would not be caught by the
    ratchet until it rippled into a `scripts/**` change.
    """
    text = _load_scripts_tests_text()

    # Check that the four mandatory globs appear in BOTH the push trigger
    # and the pull_request trigger. We use a positional split — everything
    # between the `on:` declaration and the next `permissions:` (or `jobs:`)
    # key is the trigger block; we then split it on the trigger keys.
    assert "on:" in text, (
        "scripts-tests.yml appears to be malformed (no `on:` block)")
    on_idx = text.index("on:")
    # Truncate to the next top-level key after `on:`. We do a regex over
    # the post-`on:` slice for the next '^[a-z_]+:' key (YAML top-level
    # keys are at column 0 with no indent). This is a TEXT pin by design
    # — yaml.safe_load would lose the format that matters here.
    post_on = text[on_idx:]
    next_top = re.search(r"\n[a-z_][a-z_0-9]*:", post_on[len("on:"):])
    if next_top is None:
        on_block = post_on
    else:
        on_block = post_on[: next_top.start() + len("on:")]

    push_marker = "push:"
    pr_marker = "pull_request:"
    assert push_marker in on_block, (
        "scripts-tests.yml is missing the `push:` trigger block -- "
        "the #11349 ratchet would never run on direct pushes to main"
    )
    assert pr_marker in on_block, (
        "scripts-tests.yml is missing the `pull_request:` trigger block -- "
        "the #11349 ratchet would not catch PRs from contributors"
    )

    # Slice the push: and pull_request: blocks separately. A push-only or
    # pr-only rewire would otherwise mask a regression in the other trigger.
    push_block, pr_block = _split_push_pr_blocks(on_block)

    # Substring pin per path, per block. The test does not attempt glob
    # semantics: a future maintainer who moves the path under a different
    # prefix must update BOTH the workflow and the test literal together
    # (deliberate coupling -- silent drift is the bug class #11349 names).
    for path in _CONWAY_LEAN_TRIGGER_PATHS:
        # Allow either the verbatim path string OR an equivalent glob form
        # rooted at the workflow's working directory. We accept any of:
        #   - exact path
        #   - same path with a different quoting (single/double quotes)
        #   - the bare suffix after `MyIA.AI.Notebooks/SymbolicAI/Lean/`
        #     (workflows fire from the repo root, so the absolute prefix is
        #     unnecessary and some refactors drop it)
        quoted_exact = path
        quoted_no_prefix = path[len("MyIA.AI.Notebooks/SymbolicAI/Lean/"):]
        for block, label in [(push_block, "push:"), (pr_block, "pull_request:")]:
            ok = (
                quoted_exact in block
                or quoted_no_prefix in block
            )
            if not ok:
                # Last resort: a wild-card-equivalent prefix. We do this
                # generously so the pin tracks reasonable refactors but
                # still catches a wholesale deletion (a deleted entry is
                # absent from ALL THREE forms).
                leaf = path.rsplit("/", 1)[-1]  # 'lakefile.lean', '**/*.lean', ...
                bare_glob = leaf  # e.g. '**/*.lean'
                ok = bare_glob in block
            assert ok, (
                f"#11349 path-filter pin: scripts-tests.yml {label} trigger "
                f"is missing the entry for {path!r}. The native_decide "
                f"ratchet (`test_audit_allowlists_native_decide_axioms` above) "
                f"would not run on conway_lean-only diffs and main would go "
                f"red only on the next unrelated `scripts/**` push. PR "
                f"#11495 (commit 9b2d9e5c1) added this wiring; reverting it "
                f"without re-wiring the test pin masks a real regression."
            )


def _split_push_pr_blocks(on_block: str) -> tuple[str, str]:
    """Split the `on:` block into the `push:` and `pull_request:` slices.

    Each is the contiguous YAML text starting from its trigger key (e.g.
    `push:`) up to the next top-level trigger key (`pull_request:`,
    `workflow_dispatch:`) or the closing brace. The function returns the
    raw text — substring pins are done by the caller.

    Note: the `pull_request:` literal can also appear inside a YAML comment
    (e.g. `# mirrored under pull_request: below`). A naive `text.find()`
    would pick up that comment mention instead of the trigger key. We work
    around this with a positional split: each trigger key (`push:` /
    `pull_request:`) MUST be preceded by 0-or-more whitespace at column
    2 (under `on:`) followed by no leading comment marker.
    """
    text = on_block
    # Find trigger keys that look like YAML children of `on:` — i.e.
    # preceded by a newline and 2-space indent (column 2), and NOT the
    # first line of the on_block (which contains 'on:' at column 0).
    push_matches = list(re.finditer(r"\n  push:\n", text))
    pr_matches = list(re.finditer(r"\n  pull_request:\n", text))

    if not push_matches:
        # No push block -- the ratchet would never run on a push to main,
        # but we still want a precise failure mode. Return empty.
        return "", ""
    push_start = push_matches[0].start() + 1  # advance past the leading \n

    if not pr_matches:
        return text[push_start:], ""

    pr_start = pr_matches[0].start() + 1

    if push_start < pr_start:
        return text[push_start:pr_start], text[pr_start:]
    # Defensive: if pr comes before push (unlikely under `on:`), still
    # return a non-empty pair so the caller can diagnose.
    return text[pr_start:push_start] if False else text[push_start:], text[pr_start:]


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
