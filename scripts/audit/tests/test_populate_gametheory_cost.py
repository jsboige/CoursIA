#!/usr/bin/env python3
"""Tests pour populate_gametheory_cost.py — Issue #8056 (matrice cout/ressource).

Covers the importable pure helpers of the GameTheory cost-metadata provisioner
(the dedicated family populator behind the #8056 GameTheory tranche burn-down,
distinct from the generic `populate_cost_metadata.py` tested in the sibling file).

Scope (hermetic, 0 network / 0 repo-file read):
  - PROFILES / TRANCHES data integrity (references resolve, schema keys present)
  - build_cost : profile-derivation + GameTheory-wide constants + today-stamp
  - populate_notebook : idempotency, dry-run vs apply, LF-only write, error guard
  - main : --audit summary, --tranche validation (exit codes), --apply/--today wiring

``build_cost`` derives per-notebook fields (cpu_min, network, validator, notes)
from PROFILES and pins the GameTheory family constants (api_usd_est=0.0,
gpu_required=False, vram_tier=NONE, free_alternative='self', reproducibility=HIGH,
qcc_tokens_est=0). ``populate_notebook`` is idempotent (never overwrites an
existing cost block) and byte-surgical (LF-only post-write on Windows).

Run: ``python -m pytest scripts/audit/tests/test_populate_gametheory_cost.py -q``
"""
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import populate_gametheory_cost as pgt  # noqa: E402


# ---------------------------------------------------------------------------
# PROFILES / TRANCHES data integrity
# ---------------------------------------------------------------------------

_REQUIRED_PROFILE_KEYS = {"kernel", "validator", "cpu_min", "network", "notes"}
_KNOWN_VALIDATORS = {"papermill", "dotnet-interactive", "lean_build"}
_KNOWN_KERNELS = {"python3", ".net-csharp", "gametheory-wsl"}


def test_profiles_have_required_keys():
    for name, prof in pgt.PROFILES.items():
        missing = _REQUIRED_PROFILE_KEYS - prof.keys()
        assert not missing, f"{name} missing keys: {missing}"


def test_profiles_cpu_min_positive_int():
    for name, prof in pgt.PROFILES.items():
        assert isinstance(prof["cpu_min"], int) and prof["cpu_min"] > 0, name


def test_profiles_network_is_bool():
    for name, prof in pgt.PROFILES.items():
        assert isinstance(prof["network"], bool), name


def test_profiles_validator_in_known_set():
    for name, prof in pgt.PROFILES.items():
        assert prof["validator"] in _KNOWN_VALIDATORS, f"{name}: {prof['validator']}"


def test_profiles_kernel_in_known_set():
    for name, prof in pgt.PROFILES.items():
        assert prof["kernel"] in _KNOWN_KERNELS, f"{name}: {prof['kernel']}"


def test_profiles_notes_nonempty():
    for name, prof in pgt.PROFILES.items():
        assert isinstance(prof["notes"], str) and prof["notes"].strip(), name


def test_tranches_keys_are_one_and_two():
    assert set(pgt.TRANCHES.keys()) == {1, 2}


def test_tranches_all_names_in_profiles():
    for tranche, names in pgt.TRANCHES.items():
        for n in names:
            assert n in pgt.PROFILES, f"tranche {tranche}: {n} not in PROFILES"


def test_tranches_no_duplicate_across_tranches():
    seen = []
    for names in pgt.TRANCHES.values():
        seen.extend(names)
    assert len(seen) == len(set(seen)), "duplicate notebook name across tranches"


# ---------------------------------------------------------------------------
# build_cost
# ---------------------------------------------------------------------------

def test_build_cost_has_all_schema_fields():
    cost = pgt.build_cost("GameTheory-1-Setup", by="x", today="2026-08-03")
    expected_keys = {
        "api_usd_est", "api_provider", "qcc_tokens_est", "cpu_min", "gpu_min",
        "gpu_required", "vram_gb", "vram_tier", "network", "external_account",
        "free_alternative", "reduced_pedagogical", "reproducibility",
        "metadata_written", "validator", "notes",
    }
    assert set(cost.keys()) == expected_keys
    assert len(cost) == 16


def test_build_cost_gametheory_constants():
    """GameTheory family-wide constants (cpu/GPU/VRAM = 0, no API, no account)."""
    cost = pgt.build_cost("GameTheory-2-NormalForm", by="x", today="2026-08-03")
    assert cost["api_usd_est"] == 0.0
    assert cost["api_provider"] == "none"
    assert cost["qcc_tokens_est"] == 0
    assert cost["gpu_min"] == 0
    assert cost["gpu_required"] is False
    assert cost["vram_gb"] == 0
    assert cost["vram_tier"] == "NONE"
    assert cost["external_account"] == "none"
    assert cost["free_alternative"] == "self"
    assert cost["reduced_pedagogical"] is None
    assert cost["reproducibility"] == "HIGH"


def test_build_cost_derives_profile_fields():
    """cpu_min/network/validator/notes are pulled from the notebook's PROFILES entry."""
    cost = pgt.build_cost("GameTheory-1-Setup", by="x", today="2026-08-03")
    prof = pgt.PROFILES["GameTheory-1-Setup"]
    assert cost["cpu_min"] == prof["cpu_min"]
    assert cost["network"] == prof["network"]
    assert cost["validator"] == prof["validator"]
    assert cost["notes"] == prof["notes"]


def test_build_cost_today_stamp_injected():
    assert pgt.build_cost("GameTheory-2-NormalForm", by="x", today="2026-01-09")["metadata_written"] == "2026-01-09"
    assert pgt.build_cost("GameTheory-2-NormalForm", by="x", today="2030-12-31")["metadata_written"] == "2030-12-31"


def test_build_cost_setup_network_true_others_false():
    # Setup needs pip install nashpy/openspiel -> network True; the rest CPU-pure.
    assert pgt.build_cost("GameTheory-1-Setup", by="x", today="t")["network"] is True
    assert pgt.build_cost("GameTheory-2-NormalForm", by="x", today="t")["network"] is False
    assert pgt.build_cost("GameTheory-5-ZeroSum-Minimax", by="x", today="t")["network"] is False


def test_build_cost_unknown_notebook_raises():
    with pytest.raises(KeyError):
        pgt.build_cost("DoesNotExist", by="x", today="t")


# ---------------------------------------------------------------------------
# populate_notebook (file I/O, tmp_path, hermetic)
# ---------------------------------------------------------------------------

def _make_nb(name: str, with_cost: bool = False, cells=None) -> dict:
    nb = {
        "cells": cells or [
            {"cell_type": "markdown", "metadata": {}, "source": [f"# {name}\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    if with_cost:
        nb["metadata"]["cost"] = {"api_usd_est": 9.9}  # pre-existing, must survive
    return nb


def _write_nb(tmp_path: Path, name: str, nb: dict) -> Path:
    p = tmp_path / f"{name}.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    return p


def test_populate_skipped_no_profile(tmp_path):
    p = _write_nb(tmp_path, "GameTheory-999-Unknown", _make_nb("GameTheory-999-Unknown"))
    assert pgt.populate_notebook(p, by="x", today="t", apply=True) == "skipped-no-profile (GameTheory-999-Unknown)"


def test_populate_skipped_has_cost_idempotent(tmp_path):
    # A notebook already carrying metadata.cost is NEVER overwritten.
    p = _write_nb(tmp_path, "GameTheory-1-Setup", _make_nb("GameTheory-1-Setup", with_cost=True))
    assert pgt.populate_notebook(p, by="x", today="t", apply=True) == "skipped-has-cost"
    # The pre-existing cost is preserved untouched.
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["api_usd_est"] == 9.9


def test_populate_dry_run_writes_nothing(tmp_path):
    p = _write_nb(tmp_path, "GameTheory-1-Setup", _make_nb("GameTheory-1-Setup"))
    size_before = p.stat().st_size
    status = pgt.populate_notebook(p, by="x", today="t", apply=False)
    assert status == "populated"
    assert p.stat().st_size == size_before  # dry-run = no byte written
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "cost" not in after["metadata"]


def test_populate_apply_writes_cost_block(tmp_path):
    p = _write_nb(tmp_path, "GameTheory-2-NormalForm", _make_nb("GameTheory-2-NormalForm"))
    status = pgt.populate_notebook(p, by="x", today="2026-08-03", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    cost = after["metadata"]["cost"]
    assert cost["cpu_min"] == pgt.PROFILES["GameTheory-2-NormalForm"]["cpu_min"]
    assert cost["metadata_written"] == "2026-08-03"
    assert cost["api_usd_est"] == 0.0


def test_populate_apply_output_is_lf_only(tmp_path):
    # Windows write_bytes must NOT introduce CRLF (L965/L925-E byte-stability).
    p = _write_nb(tmp_path, "GameTheory-1-Setup", _make_nb("GameTheory-1-Setup"))
    pgt.populate_notebook(p, by="x", today="t", apply=True)
    raw = p.read_bytes()
    assert b"\r\n" not in raw, "CRLF leaked into written notebook"


def test_populate_preserves_existing_cells_and_metadata(tmp_path):
    # The cost block is added; existing cells / kernelspec stay intact.
    cells = [
        {"cell_type": "markdown", "metadata": {}, "source": ["# Title\n"]},
        {"cell_type": "code", "execution_count": 1, "metadata": {},
         "outputs": [], "source": ["import numpy\n"]},
    ]
    p = _write_nb(tmp_path, "GameTheory-1-Setup", _make_nb("GameTheory-1-Setup", cells=cells))
    pgt.populate_notebook(p, by="x", today="t", apply=True)
    after = json.loads(p.read_text(encoding="utf-8"))
    assert len(after["cells"]) == 2
    assert after["cells"][1]["source"] == ["import numpy\n"]
    assert after["metadata"]["kernelspec"]["name"] == "python3"
    assert "cost" in after["metadata"]


def test_populate_unreadable_file_returns_error(tmp_path):
    p = tmp_path / "GameTheory-1-Setup.ipynb"
    p.write_text("{not valid json", encoding="utf-8")  # malformed
    status = pgt.populate_notebook(p, by="x", today="t", apply=True)
    assert status.startswith("error:")


# ---------------------------------------------------------------------------
# main (CLI wiring, hermetic via tmp_path + monkeypatch.chdir)
# ---------------------------------------------------------------------------

def test_main_tranche_invalid_returns_2(capsys):
    assert pgt.main(["--tranche", "99"]) == 2
    err = capsys.readouterr().err
    assert "99" in err


def test_main_tranche_valid_dryrun_returns_0(tmp_path, monkeypatch, capsys):
    # No GameTheory notebooks present -> WARN per missing file, but exit 0.
    monkeypatch.chdir(tmp_path)
    rc = pgt.main(["--tranche", "1"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "DRY-RUN" in out
    assert "tranche=1" in out


def test_main_apply_populates_fake_tranche(tmp_path, monkeypatch, capsys):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "MyIA.AI.Notebooks" / "GameTheory").mkdir(parents=True)
    gt_dir = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
    for name in pgt.TRANCHES[1]:
        (gt_dir / f"{name}.ipynb").write_text(
            json.dumps(_make_nb(name)), encoding="utf-8")
    rc = pgt.main(["--tranche", "1", "--apply", "--today", "2026-08-03"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "APPLY" in out
    assert "populated" in out
    # Verify one notebook got its cost block.
    nb = json.loads((gt_dir / "GameTheory-1-Setup.ipynb").read_text(encoding="utf-8"))
    assert nb["metadata"]["cost"]["metadata_written"] == "2026-08-03"


def test_main_audit_summarizes(tmp_path, monkeypatch, capsys):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "MyIA.AI.Notebooks" / "GameTheory").mkdir(parents=True)
    gt_dir = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
    # one WITH cost, one WITHOUT
    (gt_dir / "WithCost.ipynb").write_text(
        json.dumps(_make_nb("WithCost", with_cost=True)), encoding="utf-8")
    (gt_dir / "NoCost.ipynb").write_text(
        json.dumps(_make_nb("NoCost")), encoding="utf-8")
    rc = pgt.main(["--audit"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "HAS_COST  WithCost.ipynb" in out
    assert "MISSING   NoCost.ipynb" in out
    assert "[AUDIT] 1 WITH cost / 1 WITHOUT cost" in out
