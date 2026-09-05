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

Fusion #14615 famille 6 partie 2 : la couche NUMBERING-DRIFT (EPIC #12933,
16 tests avec fixtures git mini-repo, ex scripts/tests/test_check_twin_parity.py)
est portee ci-dessous en fin de fichier. Dedupe documentee : les 3 combos
content-drift de son test_classify_per_pair ((OK,DRIFT), (DRIFT,OK), (OK,OK))
sont deja dans la table 9-combos EXPECTED ci-dessus -- seuls les 4 combos
NUMBERING-DRIFT sont portes.
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_twin_parity import (  # noqa: E402
    _classify_per_pair,
    _git_blob_sha,
    _twin_base_number,
    check_pair,
    main,
    validate_pair_fields,
)


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


# =============================================================================
# Couche NUMBERING-DRIFT (EPIC #12933) -- portee de la suite dupliquee
# scripts/tests/test_check_twin_parity.py (#14615 famille 6 partie 2).
#
# EPIC #12933 (« renumerotation paritaire des series paralleles ») pose le
# principe « parite des identifiants, liberte des contenus » : deux jumeaux
# declares d'une meme paire partagent leur NUMERO DE BASE. The guard catches a
# unilateral renumber (one side renamed 10 -> 11, the class of defect #5361)
# that content-SHA comparison cannot see -- the paths themselves diverge.
#
# Scope (mirrors the claim on #12933):
#   1. _twin_base_number : base-number extraction, companion suffix `b` ignored;
#   2. validate_pair_fields : numbering_exception must be a non-empty string
#      (pattern bridge_verdict_reason, #10439);
#   3. check_pair : OK / NUMBERING-DRIFT / companion OK / documented exception OK;
#   4. _classify_per_pair : numbering drift introduced/resolved per-PR semantics
#      (content-drift combos deduped against the 9-combo table above);
#   5. fleet-wide --check : exit 1 + tallies when a pair numbering-diverges.
# =============================================================================


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-c", "user.name=test", "-c", "user.email=test@example.com", *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=str(repo), check=True,
    )


def _make_repo(tmp_path: Path, files: dict[str, str]) -> Path:
    """Mini git repo with the given files committed at HEAD."""
    repo = tmp_path / "mini_repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    for rel, content in files.items():
        f = repo / rel
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(content, encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "fixture")
    return repo


_MINIMAL_NB = '{"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5}'


def _pair(name: str, py: str, cs: str, **extra) -> dict:
    return {"name": name, "family": "Fixture", "python": py, "csharp": cs,
            "parity_level": "surface", **extra}


def _audited_pair(repo: Path, name: str, py: str, cs: str, **extra) -> dict:
    """Pair whose legacy last_audit records the CURRENT blob SHAs (status OK)."""
    pair = _pair(name, py, cs, **extra)
    pair["last_audit"] = {
        "date": "2026-08-26",
        "by": "test-fixture",
        "python_sha": _git_blob_sha(repo, py, "HEAD"),
        "csharp_sha": _git_blob_sha(repo, cs, "HEAD"),
    }
    return pair


# --- 1. _twin_base_number -----------------------------------------------------

@pytest.mark.parametrize("rel_path, expected", [
    ("MyIA.AI.Notebooks/ML/ML-3/ML-3.ipynb", "3"),
    ("Some/App-10-CSharp.ipynb", "10"),
    # Companion suffix (3rd notebook of the serie) : only the numeric part counts.
    ("Some/App-10b-CSharp.ipynb", "10"),
    ("Some/SW-10b-Python.ipynb", "10"),
    # Multi-digit and number NOT in first position.
    ("Probas/Infer-19-Classifier.ipynb", "19"),
    ("x/Prefix-2b3-Toto.ipynb", "2"),
    # Windows separators accepted.
    ("MyIA.AI.Notebooks\\ML\\ML-3\\ML-3.ipynb", "3"),
    # Unnumbered basename -> None (never compared).
    ("Some/README.ipynb", None),
])
def test_twin_base_number(rel_path, expected):
    assert _twin_base_number(rel_path) == expected


def test_twin_base_number_companion_suffix_is_not_a_divergence():
    """App-10 vs App-10b : same base number -- the sibling convention."""
    assert _twin_base_number("Some/App-10-Python.ipynb") == \
           _twin_base_number("Some/App-10b-CSharp.ipynb")


# --- 2. validate_pair_fields --------------------------------------------------

def test_validate_numbering_exception_absent_ok():
    assert validate_pair_fields(_pair("P", "a-1.py", "a-1.cs")) == []


def test_validate_numbering_exception_string_ok():
    errs = validate_pair_fields(
        _pair("P", "a-1.py", "a-2.cs", numbering_exception="justifie le 2026-08-26 (historique)")
    )
    assert errs == []


@pytest.mark.parametrize("bad", [True, False, 1, "", "   "])
def test_validate_numbering_exception_bad_values_fail(bad):
    """Boolean / empty : says THAT we escape, not WHY -- refused (#10439 pattern)."""
    errs = validate_pair_fields(_pair("P", "a-1.py", "a-2.cs", numbering_exception=bad))
    assert any("numbering_exception" in e for e in errs), errs


def test_validate_bridge_verdict_regression_guard():
    """The existing INTRINSIC-without-reason rule still holds (untouched by #12933)."""
    errs = validate_pair_fields(
        _pair("P", "a-1.py", "a-1.cs", bridge_verdict="INTRINSIC")
    )
    assert any("bridge_verdict_reason" in e for e in errs), errs


# --- 3. check_pair : the verdict itself ---------------------------------------

def test_check_pair_aligned_numbers_ok(tmp_path):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _audited_pair(repo, "P-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"))
    assert r["status"] == "OK", r["details"]


def test_check_pair_divergent_numbers_numbering_drift(tmp_path):
    """The #5361-class defect : one side renamed unilaterally 10 -> 11."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _audited_pair(repo, "P-10", "nb/py-10.ipynb", "nb/cs-11.ipynb"))
    assert r["status"] == "NUMBERING-DRIFT", r["details"]
    assert any("python=10" in d and "csharp=11" in d for d in r["details"]), r["details"]
    assert any("numbering_exception" in d for d in r["details"]), r["details"]


def test_check_pair_companion_suffix_ok(tmp_path):
    """App-10 vs App-10b : companion suffix is NOT a numbering divergence."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10b.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _audited_pair(repo, "P-10b", "nb/py-10.ipynb", "nb/cs-10b.ipynb"))
    assert r["status"] == "OK", r["details"]


def test_check_pair_documented_exception_stays_ok(tmp_path):
    """numbering_exception with a real reason : OK + detail, never red."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _audited_pair(
        repo, "P-doc", "nb/py-10.ipynb", "nb/cs-11.ipynb",
        numbering_exception="publication decallee, numero 11 deja pris (2026-08-26)",
    ))
    assert r["status"] == "OK", r["details"]
    assert any("documentee" in d for d in r["details"]), r["details"]


def test_check_pair_bool_exception_is_not_an_escape(tmp_path):
    """numbering_exception: true (non-string) must NOT silence the verdict --
    check_pair does not run validate_pair_fields, so it guards on its own."""
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = check_pair(repo, _audited_pair(
        repo, "P-bool", "nb/py-10.ipynb", "nb/cs-11.ipynb",
        numbering_exception=True,
    ))
    assert r["status"] == "NUMBERING-DRIFT", r["details"]


def test_check_pair_missing_wins_over_numbering(tmp_path):
    """A missing twin is the more severe state : MISSING, not NUMBERING-DRIFT."""
    repo = _make_repo(tmp_path, {"nb/py-10.ipynb": _MINIMAL_NB})
    pair = _pair("P-miss", "nb/py-10.ipynb", "nb/cs-11.ipynb")
    r = check_pair(repo, pair)
    assert r["status"] == "MISSING", r["details"]


# --- 4. _classify_per_pair : numbering per-PR semantics -----------------------
# (les 3 combos content-drift du port sont dedupliques -- table 9-combos above)

@pytest.mark.parametrize("base, head, expected", [
    ("OK", "NUMBERING-DRIFT", "DRIFT_INTRODUCED"),   # unilateral rename IN this PR
    ("NUMBERING-DRIFT", "OK", "DRIFT_RESOLVED"),     # realigned, or exception added
    ("NUMBERING-DRIFT", "NUMBERING-DRIFT", "DRIFT_PRE_EXISTING"),
    ("MISSING", "NUMBERING-DRIFT", "DRIFT_INTRODUCED"),  # pair added by the PR, drifted
])
def test_classify_numbering_per_pair(base, head, expected):
    assert _classify_per_pair(base, head) == expected


# --- 5. Fleet-wide --check gate ------------------------------------------------

def _write_registry(tmp_path: Path, pairs: list) -> Path:
    import yaml
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir(exist_ok=True)
    for pp in pairs:
        slug = pp["name"].lower().replace(" ", "-")
        (reg / f"{slug}.yaml").write_text(
            yaml.safe_dump(pp, allow_unicode=True, sort_keys=False), encoding="utf-8"
        )
    return reg


def test_fleet_check_green_when_aligned(tmp_path, capsys):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(repo, "Fixture-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"),
    ])
    rc = main(["--registry", str(reg), "--repo-root", str(repo), "--check"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "NUMBERING-DRIFT=0" in out


def test_fleet_check_red_on_numbering_drift(tmp_path, capsys):
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/py-21.ipynb": _MINIMAL_NB,
        "nb/cs-22.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(repo, "Fixture-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"),
        _audited_pair(repo, "Fixture-21", "nb/py-21.ipynb", "nb/cs-22.ipynb"),
    ])
    rc = main(["--registry", str(reg), "--repo-root", str(repo), "--check"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "[NUMBERING-DRIFT] Fixture-21" in out
    assert "NUMBERING-DRIFT=1" in out


def test_fleet_json_carries_numbering_drift_count(tmp_path, capsys):
    repo = _make_repo(tmp_path, {
        "nb/py-3.ipynb": _MINIMAL_NB,
        "nb/cs-4.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(repo, "Fixture-3", "nb/py-3.ipynb", "nb/cs-4.ipynb"),
    ])
    rc = main(["--registry", str(reg), "--repo-root", str(repo), "--json"])
    out = capsys.readouterr().out
    import json
    data = json.loads(out)
    assert data["numbering_drift"] == 1, data.get("numbering_drift")
    assert rc == 0  # --json alone does not gate ; only --check exits 1


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
