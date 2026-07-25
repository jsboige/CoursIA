"""Tests for check_twin_parity --per-pair classification (_classify_per_pair).

Pins the edge-case fix for ADDED pairs (forensic po-2026 c.709, executable proof).

Before the fix, a pair ADDED by the PR (absent from the base-ref registry,
base_status="MISSING") that was NOT OK at HEAD (head_status="DRIFT") was
mis-classified as DRIFT_PRE_EXISTING -- which does NOT fail the gate (the gate
fails only on DRIFT_INTRODUCED). So a PR that added a new twin_pairs.yaml entry
with driftant SHAs passed the per-pair gate. That contradicted the inline comment
("paire ajoutee -> si pas OK au HEAD, c'est du drift introduit") and the
"sound edge case" LGTM claim.

The fix: a pair absent from the base-ref has NO pre-existing state -- its HEAD
state IS what the PR introduces. So MISSING+DRIFT -> DRIFT_INTRODUCED (gate
fails), and MISSING+OK -> OK (not the misleading DRIFT_RESOLVED).

All 9 combos of base_status x head_status are pinned here so the classification
table is regression-locked.
"""
from __future__ import annotations

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import _classify_per_pair  # noqa: E402


# --- the full 9-combo classification table (base_status x head_status) --------
# (base, head) -> (verdict, fails_gate)
# fails_gate = True iff verdict == "DRIFT_INTRODUCED" (the --check --per-pair exit 1).
EXPECTED = {
    # Existing pair, clean at base
    ("OK", "OK"): ("OK", False),
    ("OK", "DRIFT"): ("DRIFT_INTRODUCED", True),
    ("OK", "MISSING"): ("DRIFT_INTRODUCED", True),
    # Existing pair, already driftant at base
    ("DRIFT", "OK"): ("DRIFT_RESOLVED", False),
    ("DRIFT", "DRIFT"): ("DRIFT_PRE_EXISTING", False),
    ("DRIFT", "MISSING"): ("DRIFT_PRE_EXISTING", False),
    # Pair ADDED by the PR (absent at base) -- the fixed edge cases
    ("MISSING", "OK"): ("OK", False),              # PR adds a clean pair
    ("MISSING", "DRIFT"): ("DRIFT_INTRODUCED", True),   # <-- the bug: was PRE_EXISTING
    ("MISSING", "MISSING"): ("DRIFT_INTRODUCED", True), # <-- the bug: was PRE_EXISTING
}


@pytest.mark.parametrize("base,head", sorted(EXPECTED.keys()))
def test_classify_all_combos(base, head):
    verdict, fails_gate = EXPECTED[(base, head)]
    got = _classify_per_pair(base, head)
    assert got == verdict, (
        f"_classify_per_pair({base!r}, {head!r}) = {got!r}, expected {verdict!r}"
    )
    # The gate (--check --per-pair) returns 1 iff there is >=1 DRIFT_INTRODUCED.
    assert (got == "DRIFT_INTRODUCED") == fails_gate


# --- the two founding-bug cases, spelled out explicitly ----------------------


def test_added_pair_driftant_at_head_fails_gate():
    """The founding bug: an ADDED pair (base MISSING) that is DRIFT at HEAD must
    be classified DRIFT_INTRODUCED (gate fails), NOT DRIFT_PRE_EXISTING (gate pass).
    """
    assert _classify_per_pair("MISSING", "DRIFT") == "DRIFT_INTRODUCED"


def test_added_pair_with_missing_files_at_head_fails_gate():
    """Same bug, files-missing variant: ADDED pair whose files don't exist at HEAD
    must be DRIFT_INTRODUCED, not silently passed as PRE_EXISTING."""
    assert _classify_per_pair("MISSING", "MISSING") == "DRIFT_INTRODUCED"


def test_added_clean_pair_is_OK_not_resolved():
    """An ADDED pair that is OK at HEAD is OK (the PR adds a clean pair), NOT
    DRIFT_RESOLVED (nothing was resolved -- there was no prior driftant state)."""
    assert _classify_per_pair("MISSING", "OK") == "OK"


def test_pre_existing_drift_does_not_fail_gate():
    """Sanity: a pair driftant at BOTH base and HEAD is PRE_EXISTING (not the PR's
    fault) and must NOT fail the gate. This is the whole point of --per-pair mode."""
    assert _classify_per_pair("DRIFT", "DRIFT") == "DRIFT_PRE_EXISTING"


# --- --update guard + --pair selector (#8508) ---------------------------------
# Bare --update rebaselines the WHOLE registry (silent drift-signal corruption,
# L963/L974). The fix refuses it unless --family / --pair / --yes-all-pairs is
# given. These tests pin the guard + the selective rebaseline behaviour.


def _tmp_registry(tmp_path, names):
    """Build a throwaway registry whose pair paths point at stable tracked files
    (the blob-SHA logic is path-agnostic; we only test the selector/guard here)."""
    import yaml
    # two stable tracked files in the repo (exist in git -> _git_blob_sha works)
    stable_a = "scripts/notebook_tools/check_twin_parity.py"
    stable_b = "scripts/notebook_tools/validate_pr_notebooks.py"
    paths = [stable_a, stable_b]
    pairs = []
    for i, name in enumerate(names):
        pairs.append({
            "name": name,
            "family": f"FAM{i}",
            "python": paths[i % len(paths)],
            "csharp": paths[(i + 1) % len(paths)],
            "parity_level": "semantic",
            "last_audit": {"date": "2020-01-01", "by": "test", "python_sha": "old", "csharp_sha": "old"},
        })
    reg = tmp_path / "twin_pairs.yaml"
    reg.write_text(yaml.safe_dump(pairs, sort_keys=False, allow_unicode=True), encoding="utf-8")
    return reg


def test_bare_update_is_refused(tmp_path):
    """#8508: bare `--update` must refuse (would rebaseline ALL pairs silently)."""
    from check_twin_parity import main
    reg = _tmp_registry(tmp_path, ["A", "B"])
    with pytest.raises(SystemExit):
        main(["--registry", str(reg), "--update"])


def test_update_pair_selects_one_pair_only(tmp_path):
    """`--update --pair <name>` rebaselines ONLY the named pair; the other's
    last_audit is unchanged."""
    import yaml
    from check_twin_parity import main
    reg = _tmp_registry(tmp_path, ["AAA", "BBB"])
    rc = main(["--registry", str(reg), "--update", "--pair", "AAA"])
    assert rc == 0
    pairs = yaml.safe_load(reg.read_text(encoding="utf-8"))
    by_name = {p["name"]: p for p in pairs}
    # AAA rebaselined (SHA no longer the 'old' sentinel)
    assert by_name["AAA"]["last_audit"]["python_sha"] != "old"
    # BBB untouched (its sentinel 'old' SHA preserved)
    assert by_name["BBB"]["last_audit"]["python_sha"] == "old"


def test_update_unknown_pair_errors(tmp_path):
    """`--update --pair <nonexistent>` must error (no silent no-op)."""
    from check_twin_parity import main
    reg = _tmp_registry(tmp_path, ["AAA", "BBB"])
    with pytest.raises(SystemExit):
        main(["--registry", str(reg), "--update", "--pair", "ZZZ"])


def test_update_yes_all_pairs_rebaselines_everything(tmp_path):
    """`--update --yes-all-pairs` is the explicit opt-in that rebaselines ALL
    pairs (backward-compat for intentional full rebaseline)."""
    import yaml
    from check_twin_parity import main
    reg = _tmp_registry(tmp_path, ["AAA", "BBB"])
    rc = main(["--registry", str(reg), "--update", "--yes-all-pairs"])
    assert rc == 0
    pairs = yaml.safe_load(reg.read_text(encoding="utf-8"))
    # BOTH pairs rebaselined (no 'old' sentinel remains)
    assert all(p["last_audit"]["python_sha"] != "old" for p in pairs)


def test_pair_without_update_errors(tmp_path):
    """`--pair` without `--update` makes no sense -> argparse error."""
    from check_twin_parity import main
    reg = _tmp_registry(tmp_path, ["AAA", "BBB"])
    with pytest.raises(SystemExit):
        main(["--registry", str(reg), "--pair", "AAA"])


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
