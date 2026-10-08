"""Tests pour assert_memory_budget (#19805)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "tests"))

from assert_memory_budget import (  # type: ignore  # noqa: E402
    BudgetSnapshot,
    CompositionFamily,
    assert_memory_budget,
    parse_memory_max_gib,
)


REPO_BUDGET = REPO_ROOT / "docker-configurations" / "runners" / "po2024_budget.json"
REPO_SLICE = REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist" / "coursia-ci.slice"


def test_budget_snapshot_loads():
    """Le snapshot canonique est lisible et structure conforme."""
    snap = BudgetSnapshot.from_json(REPO_BUDGET)
    assert snap.machine == "po-2024"
    assert snap.composition_total_gib == 27.0
    assert "docker" in snap.composition
    assert "waiters" in snap.composition
    assert "lean" in snap.composition
    assert snap.composition["lean"].instances == 2
    assert snap.composition["lean"].cap_gib == 6.0
    assert snap.composition["lean"].total_gib == 12.0


def test_budget_snapshot_total_matches_sum():
    """La somme des familles = composition_total_gib (coherence interne)."""
    snap = BudgetSnapshot.from_json(REPO_BUDGET)
    summed = sum(f.total_gib for f in snap.composition.values())
    assert abs(summed - snap.composition_total_gib) < 0.01


def test_parse_memory_max_gib_slice():
    """Lecture de MemoryMax depuis la slice canonique = 16 GiB."""
    val = parse_memory_max_gib(REPO_SLICE)
    assert val == 16.0


def test_parse_memory_max_gib_handles_units():
    """G, M, T supportes ; infinity ignore."""
    import tempfile

    with tempfile.NamedTemporaryFile(mode="w", suffix=".slice", delete=False) as f:
        f.write("[Slice]\nMemoryMax=8G\n")
        path = Path(f.name)
    try:
        assert parse_memory_max_gib(path) == 8.0
    finally:
        path.unlink()

    with tempfile.NamedTemporaryFile(mode="w", suffix=".slice", delete=False) as f:
        f.write("[Slice]\nMemoryMax=2048M\n")
        path = Path(f.name)
    try:
        assert parse_memory_max_gib(path) == 2.0
    finally:
        path.unlink()

    with tempfile.NamedTemporaryFile(mode="w", suffix=".slice", delete=False) as f:
        f.write("[Slice]\nMemoryMax=infinity\n")
        path = Path(f.name)
    try:
        assert parse_memory_max_gib(path) is None
    finally:
        path.unlink()


def test_assert_incoherent_po2024_snapshot():
    """Le snapshot canonique (27 GiB) depasse le MemoryMax slice (16 GiB) -> INCOHERENT."""
    snap = BudgetSnapshot.from_json(REPO_BUDGET)
    result = assert_memory_budget(snap, vm_total_gib=23.47, slice_memory_max_gib=16.0)
    assert result.verdict == "INCOHERENT"
    assert result.borne_gib == 16.0  # min(16, 23.47-0.5) = 16.0
    assert result.composition_total_gib == 27.0


def test_assert_ok_when_composition_under_budget():
    """Composition 10 GiB < MemoryMax 16 GiB et VM 23.47 GiB -> OK."""
    snap = BudgetSnapshot(
        machine="test",
        composition={
            "small": CompositionFamily(instances=2, cap_gib=2.0, total_gib=4.0),
            "tiny": CompositionFamily(instances=12, cap_gib=0.5, total_gib=6.0),
        },
        composition_total_gib=10.0,
    )
    result = assert_memory_budget(snap, vm_total_gib=23.47, slice_memory_max_gib=16.0)
    assert result.verdict == "OK"


def test_assert_ok_when_no_slice_uses_vm():
    """Sans slice (slice_memory_max_gib=None), on n'utilise que la RAM VM."""
    snap = BudgetSnapshot(
        machine="test",
        composition={
            "small": CompositionFamily(instances=2, cap_gib=2.0, total_gib=4.0),
        },
        composition_total_gib=4.0,
    )
    result = assert_memory_budget(snap, vm_total_gib=23.47, slice_memory_max_gib=None)
    assert result.verdict == "OK"
    assert result.borne_gib == 23.47 - 0.5  # hote reserve


def test_assert_incoherent_when_above_vm_only():
    """Composition > VM-hote mais < slice -> la borne la plus contraignante tranche."""
    snap = BudgetSnapshot(
        machine="test",
        composition={
            "big": CompositionFamily(instances=4, cap_gib=5.0, total_gib=20.0),
        },
        composition_total_gib=20.0,
    )
    # slice 25 GiB, VM 23.47 GiB : borne = min(25, 23.47-0.5) = 22.97 ; 20 < 22.97 -> OK
    result = assert_memory_budget(snap, vm_total_gib=23.47, slice_memory_max_gib=25.0)
    assert result.verdict == "OK"
    # Si la VM est plus petite (16 GiB), borne = 15.5 ; 20 > 15.5 -> INCOHERENT
    result = assert_memory_budget(snap, vm_total_gib=16.0, slice_memory_max_gib=25.0)
    assert result.verdict == "INCOHERENT"


def test_marge_absorbs_overhead():
    """La marge de 0.5 GiB absorbe un leger depassement (<= marge)."""
    snap = BudgetSnapshot(
        machine="test",
        composition={
            "exact": CompositionFamily(instances=8, cap_gib=2.0, total_gib=15.5),
        },
        composition_total_gib=15.5,
    )
    # Borne 16.0, seuil 16.0 - 0.5 = 15.5 ; exactement egal -> OK
    result = assert_memory_budget(snap, vm_total_gib=23.47, slice_memory_max_gib=16.0)
    assert result.verdict == "OK"


def test_snapshot_json_well_formed():
    """Le snapshot JSON a toutes les cles attendues et des types coherents."""
    data = json.loads(REPO_BUDGET.read_text(encoding="utf-8"))
    assert data["machine"] == "po-2024"
    assert "composition" in data
    assert "composition_total_gib" in data
    for name, fam in data["composition"].items():
        assert "instances" in fam
        assert "cap_gib" in fam
        assert "total_gib" in fam
        # Sanity : total_gib = instances * cap_gib (coherence)
        assert abs(fam["total_gib"] - fam["instances"] * fam["cap_gib"]) < 0.01
