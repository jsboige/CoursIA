"""Tests for the NUMBERING-DRIFT verdict of check_twin_parity.py (EPIC #12933).

EPIC #12933 (« renumerotation paritaire des series paralleles ») posse le
principe « parite des identifiants, liberte des contenus » : deux jumeaux
declares d'une meme paire partagent leur NUMERO DE BASE. The guard catches a
unilateral renumber (one side renamed 10 -> 11, the class of defect #5361)
that content-SHA comparison cannot see -- the paths themselves diverge.

Scope of these tests (mirrors the claim on #12933):
  1. _twin_base_number : base-number extraction, companion suffix `b` ignored;
  2. validate_pair_fields : numbering_exception must be a non-empty string
     (pattern bridge_verdict_reason, #10439);
  3. check_pair : OK / NUMBERING-DRIFT / companion OK / documented exception OK;
  4. _classify_per_pair : numbering drift introduced/resolved per-PR semantics;
  5. fleet-wide --check : exit 1 + tallies when a pair numbering-diverges.
"""
from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_TWIN_PARITY = HERE.parent / "notebook_tools" / "check_twin_parity.py"


def _load(path: Path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


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


def _audited_pair(mod, repo: Path, name: str, py: str, cs: str, **extra) -> dict:
    """Pair whose legacy last_audit records the CURRENT blob SHAs (status OK)."""
    pair = _pair(name, py, cs, **extra)
    pair["last_audit"] = {
        "date": "2026-08-26",
        "by": "test-fixture",
        "python_sha": mod._git_blob_sha(repo, py, "HEAD"),
        "csharp_sha": mod._git_blob_sha(repo, cs, "HEAD"),
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
    mod = _load(CHECK_TWIN_PARITY)
    assert mod._twin_base_number(rel_path) == expected


def test_twin_base_number_companion_suffix_is_not_a_divergence():
    """App-10 vs App-10b : same base number -- the sibling convention."""
    mod = _load(CHECK_TWIN_PARITY)
    assert mod._twin_base_number("Some/App-10-Python.ipynb") == \
           mod._twin_base_number("Some/App-10b-CSharp.ipynb")


# --- 2. validate_pair_fields --------------------------------------------------

def test_validate_numbering_exception_absent_ok():
    mod = _load(CHECK_TWIN_PARITY)
    assert mod.validate_pair_fields(_pair("P", "a-1.py", "a-1.cs")) == []


def test_validate_numbering_exception_string_ok():
    mod = _load(CHECK_TWIN_PARITY)
    errs = mod.validate_pair_fields(
        _pair("P", "a-1.py", "a-2.cs", numbering_exception="justifie le 2026-08-26 (historique)")
    )
    assert errs == []


@pytest.mark.parametrize("bad", [True, False, 1, "", "   "])
def test_validate_numbering_exception_bad_values_fail(bad):
    """Boolean / empty : says THAT we escape, not WHY -- refused (#10439 pattern)."""
    mod = _load(CHECK_TWIN_PARITY)
    errs = mod.validate_pair_fields(_pair("P", "a-1.py", "a-2.cs", numbering_exception=bad))
    assert any("numbering_exception" in e for e in errs), errs


def test_validate_bridge_verdict_regression_guard():
    """The existing INTRINSIC-without-reason rule still holds (untouched by #12933)."""
    mod = _load(CHECK_TWIN_PARITY)
    errs = mod.validate_pair_fields(
        _pair("P", "a-1.py", "a-1.cs", bridge_verdict="INTRINSIC")
    )
    assert any("bridge_verdict_reason" in e for e in errs), errs


# --- 3. check_pair : the verdict itself ---------------------------------------

def test_check_pair_aligned_numbers_ok(tmp_path):
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    r = mod.check_pair(repo, _audited_pair(mod, repo, "P-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"))
    assert r["status"] == "OK", r["details"]


def test_check_pair_divergent_numbers_numbering_drift(tmp_path):
    """The #5361-class defect : one side renamed unilaterally 10 -> 11."""
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = mod.check_pair(repo, _audited_pair(mod, repo, "P-10", "nb/py-10.ipynb", "nb/cs-11.ipynb"))
    assert r["status"] == "NUMBERING-DRIFT", r["details"]
    assert any("python=10" in d and "csharp=11" in d for d in r["details"]), r["details"]
    assert any("numbering_exception" in d for d in r["details"]), r["details"]


def test_check_pair_companion_suffix_ok(tmp_path):
    """App-10 vs App-10b : companion suffix is NOT a numbering divergence."""
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10b.ipynb": _MINIMAL_NB,
    })
    r = mod.check_pair(repo, _audited_pair(mod, repo, "P-10b", "nb/py-10.ipynb", "nb/cs-10b.ipynb"))
    assert r["status"] == "OK", r["details"]


def test_check_pair_documented_exception_stays_ok(tmp_path):
    """numbering_exception with a real reason : OK + detail, never red."""
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = mod.check_pair(repo, _audited_pair(
        mod, repo, "P-doc", "nb/py-10.ipynb", "nb/cs-11.ipynb",
        numbering_exception="publication decallee, numero 11 deja pris (2026-08-26)",
    ))
    assert r["status"] == "OK", r["details"]
    assert any("documentee" in d for d in r["details"]), r["details"]


def test_check_pair_bool_exception_is_not_an_escape(tmp_path):
    """numbering_exception: true (non-string) must NOT silence the verdict --
    check_pair does not run validate_pair_fields, so it guards on its own."""
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-11.ipynb": _MINIMAL_NB,
    })
    r = mod.check_pair(repo, _audited_pair(
        mod, repo, "P-bool", "nb/py-10.ipynb", "nb/cs-11.ipynb",
        numbering_exception=True,
    ))
    assert r["status"] == "NUMBERING-DRIFT", r["details"]


def test_check_pair_missing_wins_over_numbering(tmp_path):
    """A missing twin is the more severe state : MISSING, not NUMBERING-DRIFT."""
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {"nb/py-10.ipynb": _MINIMAL_NB})
    pair = _pair("P-miss", "nb/py-10.ipynb", "nb/cs-11.ipynb")
    r = mod.check_pair(repo, pair)
    assert r["status"] == "MISSING", r["details"]


# --- 4. _classify_per_pair : per-PR semantics ---------------------------------

@pytest.mark.parametrize("base, head, expected", [
    ("OK", "NUMBERING-DRIFT", "DRIFT_INTRODUCED"),   # unilateral rename IN this PR
    ("NUMBERING-DRIFT", "OK", "DRIFT_RESOLVED"),     # realigned, or exception added
    ("NUMBERING-DRIFT", "NUMBERING-DRIFT", "DRIFT_PRE_EXISTING"),
    ("MISSING", "NUMBERING-DRIFT", "DRIFT_INTRODUCED"),  # pair added by the PR, drifted
    # Pre-existing semantics unchanged (regression guard).
    ("OK", "DRIFT", "DRIFT_INTRODUCED"),
    ("DRIFT", "OK", "DRIFT_RESOLVED"),
    ("OK", "OK", "OK"),
])
def test_classify_per_pair(base, head, expected):
    mod = _load(CHECK_TWIN_PARITY)
    assert mod._classify_per_pair(base, head) == expected


# --- 5. Fleet-wide --check gate ------------------------------------------------

def _write_registry(tmp_path: Path, pairs: list[dict]) -> Path:
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
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(mod, repo, "Fixture-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"),
    ])
    rc = mod.main(["--registry", str(reg), "--repo-root", str(repo), "--check"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "NUMBERING-DRIFT=0" in out


def test_fleet_check_red_on_numbering_drift(tmp_path, capsys):
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-10.ipynb": _MINIMAL_NB,
        "nb/cs-10.ipynb": _MINIMAL_NB,
        "nb/py-21.ipynb": _MINIMAL_NB,
        "nb/cs-22.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(mod, repo, "Fixture-10", "nb/py-10.ipynb", "nb/cs-10.ipynb"),
        _audited_pair(mod, repo, "Fixture-21", "nb/py-21.ipynb", "nb/cs-22.ipynb"),
    ])
    rc = mod.main(["--registry", str(reg), "--repo-root", str(repo), "--check"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "[NUMBERING-DRIFT] Fixture-21" in out
    assert "NUMBERING-DRIFT=1" in out


def test_fleet_json_carries_numbering_drift_count(tmp_path, capsys):
    mod = _load(CHECK_TWIN_PARITY)
    repo = _make_repo(tmp_path, {
        "nb/py-3.ipynb": _MINIMAL_NB,
        "nb/cs-4.ipynb": _MINIMAL_NB,
    })
    reg = _write_registry(tmp_path, [
        _audited_pair(mod, repo, "Fixture-3", "nb/py-3.ipynb", "nb/cs-4.ipynb"),
    ])
    rc = mod.main(["--registry", str(reg), "--repo-root", str(repo), "--json"])
    out = capsys.readouterr().out
    import json
    data = json.loads(out)
    assert data["numbering_drift"] == 1, data.get("numbering_drift")
    assert rc == 0  # --json alone does not gate ; only --check exits 1
