#!/usr/bin/env python3
"""Tests pour populate_semantickernel_cost.py — Issue #8056 (matrice cout/ressource).

Covers the importable pure helpers of the SemanticKernel cost-metadata provisioner
(the dedicated family populator behind the #8056 SemanticKernel tranche burn-down,
distinct from the generic `populate_cost_metadata.py` tested in its own sibling file
and from the GameTheory/QuantConnect family populators tested alongside).

This closes the last parity gap in the audit populate_*_cost.py family: the
GameTheory (`populate_gametheory_cost.py`) and QuantConnect
(`populate_quantconnect_cost.py`) populators each have a hermetic test suite;
the SemanticKernel populator -- the largest residual GenAI sub-series (19
profiled NBs across 2 tranches) -- had none.

Scope (hermetic, 0 network / 0 repo-file read):
  - PROFILES / TRANCHES data integrity (references resolve, schema keys present,
    no orphan profile, no duplicate across tranches)
  - build_cost : profile-derivation + SemanticKernel family constants (vram_tier
    LITE, validator manual) + today-stamp + provenance suffix
  - populate_notebook : idempotency, dry-run vs apply, --force overwrite,
    LF-only byte-surgical write, error guard, cells/metadata preservation
  - main : --audit summary, --tranche validation (exit codes), --apply/--force
    /--today/--by wiring

``build_cost`` derives per-notebook fields (api_usd_est, api_provider, cpu_min,
network, external_account, free_alternative, reproducibility, notes) from
PROFILES, hardcodes validator="manual" (OpenAI API NBs not re-exec'd this cycle,
RECOVERABLE-USER-HAND), pins the family constants (qcc_tokens_est=0, gpu_min=0,
gpu_required=False, vram_gb=0, vram_tier="LITE", reduced_pedagogical=None), stamps
metadata_written=today, and appends a provenance suffix to notes. Unlike the
GameTheory populator (cpu-pure, all api_usd_est=0.0), the SemanticKernel family is
API-heavy: api_usd_est is non-zero for most NBs and the provider varies (openai
default, anthropic for the MCP NB, none for the pandas/skeleton templates).

Run: ``python -m pytest scripts/audit/tests/test_populate_semantickernel_cost.py -q``
"""
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import populate_semantickernel_cost as psk  # noqa: E402


# ---------------------------------------------------------------------------
# PROFILES / TRANCHES data integrity
# ---------------------------------------------------------------------------

# SK profiles carry NO `kernel`/`validator` field (validator is hardcoded
# "manual" in build_cost); the 8 keys below are the actual schema.
_REQUIRED_PROFILE_KEYS = {
    "api_usd_est", "api_provider", "cpu_min", "network",
    "external_account", "free_alternative", "reproducibility", "notes",
}
_KNOWN_PROVIDERS = {"openai", "anthropic", "none"}
_KNOWN_REPRODUCIBILITY = {"LOW", "MED", "HIGH"}


def test_profiles_have_required_keys():
    for name, prof in psk.PROFILES.items():
        missing = _REQUIRED_PROFILE_KEYS - prof.keys()
        assert not missing, f"{name} missing keys: {missing}"


def test_profiles_have_no_extra_keys():
    """Pin the schema so a stray new key is a conscious decision, not drift."""
    for name, prof in psk.PROFILES.items():
        extra = prof.keys() - _REQUIRED_PROFILE_KEYS
        assert not extra, f"{name} unexpected keys: {extra}"


def test_profiles_api_usd_est_non_negative():
    for name, prof in psk.PROFILES.items():
        assert isinstance(prof["api_usd_est"], (int, float)), name
        assert prof["api_usd_est"] >= 0, f"{name}: negative cost"


def test_profiles_cpu_min_non_negative_int():
    # Templates have cpu_min=0 (skeleton), the rest 1-5.
    for name, prof in psk.PROFILES.items():
        assert isinstance(prof["cpu_min"], int) and prof["cpu_min"] >= 0, name


def test_profiles_network_is_bool():
    for name, prof in psk.PROFILES.items():
        assert isinstance(prof["network"], bool), name


def test_profiles_provider_in_known_set():
    for name, prof in psk.PROFILES.items():
        assert prof["api_provider"] in _KNOWN_PROVIDERS, f"{name}: {prof['api_provider']}"


def test_profiles_reproducibility_in_known_set():
    for name, prof in psk.PROFILES.items():
        assert prof["reproducibility"] in _KNOWN_REPRODUCIBILITY, f"{name}: {prof['reproducibility']}"


def test_profiles_notes_nonempty():
    for name, prof in psk.PROFILES.items():
        assert isinstance(prof["notes"], str) and prof["notes"].strip(), name


def test_profiles_external_account_none_when_provider_none():
    """A no-API template (provider="none") has no external account and no network."""
    for name, prof in psk.PROFILES.items():
        if prof["api_provider"] == "none":
            assert prof["external_account"] is None, name
            assert prof["network"] is False, name


def test_tranches_keys_are_one_and_two():
    assert set(psk.TRANCHES.keys()) == {1, 2}


def test_tranches_all_names_in_profiles():
    for tranche, names in psk.TRANCHES.items():
        for n in names:
            assert n in psk.PROFILES, f"tranche {tranche}: {n} not in PROFILES"


def test_tranches_no_duplicate_across_tranches():
    seen = []
    for names in psk.TRANCHES.values():
        seen.extend(names)
    assert len(seen) == len(set(seen)), "duplicate notebook name across tranches"


def test_tranches_cover_all_profiles():
    """No orphan profile: every PROFILES entry is assigned to a tranche."""
    assigned = set()
    for names in psk.TRANCHES.values():
        assigned.update(names)
    assert assigned == set(psk.PROFILES.keys()), (
        f"orphan profiles not in any tranche: {set(psk.PROFILES.keys()) - assigned}")


def test_tranche_1_is_fundamentals_01_to_09():
    """Tranche 1 = the 9 chapter fundamentals NBs (SK-01..09)."""
    for name in psk.TRANCHES[1]:
        assert name[:3] in {f"0{i}-" for i in range(1, 10)}, name
    assert len(psk.TRANCHES[1]) == 9


# ---------------------------------------------------------------------------
# build_cost
# ---------------------------------------------------------------------------

_SCHEMA_KEYS = {
    "api_usd_est", "api_provider", "qcc_tokens_est", "cpu_min", "gpu_min",
    "gpu_required", "vram_gb", "vram_tier", "network", "external_account",
    "free_alternative", "reduced_pedagogical", "reproducibility",
    "metadata_written", "validator", "notes",
}


def test_build_cost_has_all_schema_fields():
    cost = psk.build_cost("01-SemanticKernel-Intro", by="x", today="2026-08-04")
    assert set(cost.keys()) == _SCHEMA_KEYS
    assert len(cost) == 16


def test_build_cost_semantickernel_family_constants():
    """SK family-wide constants (GPU/VRAM = 0, vram_tier LITE, validator manual,
    qcc_tokens_est 0, reduced_pedagogical None). Distinct from GameTheory
    (vram_tier NONE) because SK inference is server-side OpenAI/Azure."""
    cost = psk.build_cost("02-SemanticKernel-Advanced", by="x", today="2026-08-04")
    assert cost["qcc_tokens_est"] == 0
    assert cost["gpu_min"] == 0
    assert cost["gpu_required"] is False
    assert cost["vram_gb"] == 0
    assert cost["vram_tier"] == "LITE"   # NOT "NONE" (GameTheory uses NONE)
    assert cost["reduced_pedagogical"] is None
    assert cost["validator"] == "manual"  # hardcoded, not from PROFILES


def test_build_cost_derives_profile_fields():
    """api_usd_est/api_provider/cpu_min/network/external_account/reproducibility
    are pulled from the notebook's PROFILES entry."""
    cost = psk.build_cost("05-SemanticKernel-VectorStores", by="x", today="t")
    prof = psk.PROFILES["05-SemanticKernel-VectorStores"]
    assert cost["api_usd_est"] == prof["api_usd_est"]
    assert cost["api_provider"] == prof["api_provider"]
    assert cost["cpu_min"] == prof["cpu_min"]
    assert cost["network"] == prof["network"]
    assert cost["external_account"] == prof["external_account"]
    assert cost["free_alternative"] == prof["free_alternative"]
    assert cost["reproducibility"] == prof["reproducibility"]


def test_build_cost_today_stamp_injected():
    assert psk.build_cost("01-SemanticKernel-Intro", by="x", today="2026-01-09")["metadata_written"] == "2026-01-09"
    assert psk.build_cost("01-SemanticKernel-Intro", by="x", today="2030-12-31")["metadata_written"] == "2030-12-31"


def test_build_cost_appends_provenance_suffix():
    """Unlike the GameTheory populator (notes verbatim), SK appends a provenance
    tag carrying the `by` machine:workspace + cycle marker."""
    prof = psk.PROFILES["03-SemanticKernel-Agents"]
    cost = psk.build_cost("03-SemanticKernel-Agents", by="myia-po-2026:CoursIA", today="t")
    assert cost["notes"] == prof["notes"] + " Provenance: myia-po-2026:CoursIA (c.946)."
    # The profile's own notes survive as a prefix.
    assert cost["notes"].startswith(prof["notes"])


def test_build_cost_anthropic_provider_for_mcp_nb():
    """08-SemanticKernel-MCP is the one Anthropic-profiled NB (MCP server example)."""
    cost = psk.build_cost("08-SemanticKernel-MCP", by="x", today="t")
    assert cost["api_provider"] == "anthropic"
    assert cost["external_account"] == "anthropic"


def test_build_cost_none_provider_for_template():
    """Notebook-Generated (pandas/sklearn Iris, no LLM) has provider=none, no network."""
    cost = psk.build_cost("Notebook-Generated", by="x", today="t")
    assert cost["api_provider"] == "none"
    assert cost["network"] is False
    assert cost["external_account"] is None
    assert cost["api_usd_est"] == 0.0
    assert cost["reproducibility"] == "HIGH"


def test_build_cost_unknown_notebook_raises():
    with pytest.raises(KeyError):
        psk.build_cost("DoesNotExist", by="x", today="t")


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
    p = _write_nb(tmp_path, "99-SemanticKernel-Unknown", _make_nb("99-SemanticKernel-Unknown"))
    assert psk.populate_notebook(p, by="x", today="t", apply=True) == "skipped-no-profile (99-SemanticKernel-Unknown)"


def test_populate_skipped_has_cost_idempotent(tmp_path):
    # A notebook already carrying metadata.cost is NEVER overwritten.
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", _make_nb("01-SemanticKernel-Intro", with_cost=True))
    assert psk.populate_notebook(p, by="x", today="t", apply=True) == "skipped-has-cost"
    # The pre-existing cost is preserved untouched.
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["api_usd_est"] == 9.9


def test_populate_force_overwrites_existing_cost(tmp_path):
    """--force bypasses idempotency: a pre-existing cost block is rewritten."""
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", _make_nb("01-SemanticKernel-Intro", with_cost=True))
    status = psk.populate_notebook(p, by="x", today="2026-08-04", apply=True, force=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    # The old sentinel value is gone; the profiled cost replaced it.
    assert after["metadata"]["cost"]["api_usd_est"] != 9.9
    assert after["metadata"]["cost"]["api_usd_est"] == psk.PROFILES["01-SemanticKernel-Intro"]["api_usd_est"]
    assert after["metadata"]["cost"]["metadata_written"] == "2026-08-04"


def test_populate_dry_run_writes_nothing(tmp_path):
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", _make_nb("01-SemanticKernel-Intro"))
    size_before = p.stat().st_size
    status = psk.populate_notebook(p, by="x", today="t", apply=False)
    assert status == "populated"
    assert p.stat().st_size == size_before  # dry-run = no byte written
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "cost" not in after["metadata"]


def test_populate_apply_writes_cost_block(tmp_path):
    p = _write_nb(tmp_path, "02-SemanticKernel-Advanced", _make_nb("02-SemanticKernel-Advanced"))
    status = psk.populate_notebook(p, by="x", today="2026-08-04", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    cost = after["metadata"]["cost"]
    assert cost["cpu_min"] == psk.PROFILES["02-SemanticKernel-Advanced"]["cpu_min"]
    assert cost["metadata_written"] == "2026-08-04"
    assert cost["vram_tier"] == "LITE"
    assert cost["validator"] == "manual"


def test_populate_apply_output_is_lf_only(tmp_path):
    # Windows write_bytes must NOT introduce CRLF (L965/L925-E byte-stability).
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", _make_nb("01-SemanticKernel-Intro"))
    psk.populate_notebook(p, by="x", today="t", apply=True)
    raw = p.read_bytes()
    assert b"\r\n" not in raw, "CRLF leaked into written notebook"


def test_populate_preserves_existing_cells_and_metadata(tmp_path):
    # The cost block is added; existing cells / kernelspec stay intact.
    cells = [
        {"cell_type": "markdown", "metadata": {}, "source": ["# Title\n"]},
        {"cell_type": "code", "execution_count": 1, "metadata": {},
         "outputs": [], "source": ["import semantic_kernel as sk\n"]},
    ]
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", _make_nb("01-SemanticKernel-Intro", cells=cells))
    psk.populate_notebook(p, by="x", today="t", apply=True)
    after = json.loads(p.read_text(encoding="utf-8"))
    assert len(after["cells"]) == 2
    assert after["cells"][1]["source"] == ["import semantic_kernel as sk\n"]
    assert after["metadata"]["kernelspec"]["name"] == "python3"
    assert "cost" in after["metadata"]


def test_populate_unreadable_file_returns_error(tmp_path):
    p = tmp_path / "01-SemanticKernel-Intro.ipynb"
    p.write_text("{not valid json", encoding="utf-8")  # malformed
    status = psk.populate_notebook(p, by="x", today="t", apply=True)
    assert status.startswith("error:")


def test_populate_creates_metadata_if_absent(tmp_path):
    """A notebook with no `metadata` key at all is handled (setdefault)."""
    nb = {"cells": [], "nbformat": 4, "nbformat_minor": 5}  # no metadata
    p = _write_nb(tmp_path, "01-SemanticKernel-Intro", nb)
    status = psk.populate_notebook(p, by="x", today="t", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert "cost" in after["metadata"]


# ---------------------------------------------------------------------------
# main (CLI wiring, hermetic via tmp_path + monkeypatch.chdir)
# ---------------------------------------------------------------------------

def test_main_tranche_invalid_returns_2(capsys):
    assert psk.main(["--tranche", "99"]) == 2
    err = capsys.readouterr().err
    assert "99" in err


def test_main_tranche_valid_dryrun_returns_0(tmp_path, monkeypatch, capsys):
    # No SK notebooks present -> WARN per missing file, but exit 0.
    monkeypatch.chdir(tmp_path)
    rc = psk.main(["--tranche", "1"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "DRY-RUN" in out
    assert "tranche=1" in out


def test_main_apply_populates_tranche_1(tmp_path, monkeypatch, capsys):
    monkeypatch.chdir(tmp_path)
    sk_dir = tmp_path / "MyIA.AI.Notebooks" / "GenAI" / "SemanticKernel"
    sk_dir.mkdir(parents=True)
    for name in psk.TRANCHES[1]:
        (sk_dir / f"{name}.ipynb").write_text(
            json.dumps(_make_nb(name)), encoding="utf-8")
    rc = psk.main(["--tranche", "1", "--apply", "--today", "2026-08-04",
                   "--by", "myia-po-2026:CoursIA"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "APPLY" in out
    assert "populated" in out
    # Verify one notebook got its cost block with the provenance + today stamp.
    nb = json.loads((sk_dir / "01-SemanticKernel-Intro.ipynb").read_text(encoding="utf-8"))
    cost = nb["metadata"]["cost"]
    assert cost["metadata_written"] == "2026-08-04"
    assert "Provenance: myia-po-2026:CoursIA (c.946)." in cost["notes"]


def test_main_force_repopulates_existing(tmp_path, monkeypatch, capsys):
    """--force at the CLI reruns NBs that already carry cost."""
    monkeypatch.chdir(tmp_path)
    sk_dir = tmp_path / "MyIA.AI.Notebooks" / "GenAI" / "SemanticKernel"
    sk_dir.mkdir(parents=True)
    # Pre-populate one NB with a stale cost.
    (sk_dir / "01-SemanticKernel-Intro.ipynb").write_text(
        json.dumps(_make_nb("01-SemanticKernel-Intro", with_cost=True)), encoding="utf-8")
    rc = psk.main(["--tranche", "1", "--apply", "--force", "--today", "2026-08-04"])
    assert rc == 0
    nb = json.loads((sk_dir / "01-SemanticKernel-Intro.ipynb").read_text(encoding="utf-8"))
    # Sentinel 9.9 overwritten with the profiled value.
    assert nb["metadata"]["cost"]["api_usd_est"] != 9.9
    assert nb["metadata"]["cost"]["api_usd_est"] == psk.PROFILES["01-SemanticKernel-Intro"]["api_usd_est"]


def test_main_audit_summarizes(tmp_path, monkeypatch, capsys):
    monkeypatch.chdir(tmp_path)
    sk_dir = tmp_path / "MyIA.AI.Notebooks" / "GenAI" / "SemanticKernel"
    sk_dir.mkdir(parents=True)
    # one WITH cost, one WITHOUT
    (sk_dir / "WithCost.ipynb").write_text(
        json.dumps(_make_nb("WithCost", with_cost=True)), encoding="utf-8")
    (sk_dir / "NoCost.ipynb").write_text(
        json.dumps(_make_nb("NoCost")), encoding="utf-8")
    rc = psk.main(["--audit"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "HAS_COST  WithCost.ipynb" in out
    assert "MISSING   NoCost.ipynb" in out
    assert "[AUDIT] 1 WITH cost / 1 WITHOUT cost" in out


def test_main_audit_excludes_output_notebooks(tmp_path, monkeypatch, capsys):
    """_output.ipynb (papermill artifact) is excluded from the audit glob."""
    monkeypatch.chdir(tmp_path)
    sk_dir = tmp_path / "MyIA.AI.Notebooks" / "GenAI" / "SemanticKernel"
    sk_dir.mkdir(parents=True)
    (sk_dir / "Foo_output.ipynb").write_text(
        json.dumps(_make_nb("Foo_output")), encoding="utf-8")
    rc = psk.main(["--audit"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "Foo_output" not in out
    assert "total 0" in out


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
