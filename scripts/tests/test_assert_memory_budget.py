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
    PO2024_VM_RAM_GIB,
    BudgetSnapshot,
    CompositionFamily,
    assert_memory_budget,
    lookup_slice,
    lookup_vm_ram_gib,
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


# -- Tests pour les 3 fixes revue coordinateur 2026-10-08 (defauts 1, 2, 3) --


def test_lookup_vm_ram_gib_po2024():
    """Defaut 3 : la RAM VM est declaree comme constante par machine-cible.

    Mesurer l'hote de l'organe rend un verdict incoherent (organe sur ai-01
    avec 191.8 GiB dirait 'po-2024 = 191.8 GiB', et l'instrument ne servirait
    plus a rien). La RAM est une propriete de la machine VERIFIEE, pas de
    celle qui execute.
    """
    assert lookup_vm_ram_gib("po-2024") == PO2024_VM_RAM_GIB
    assert PO2024_VM_RAM_GIB == 24.0  # PR #19802


def test_lookup_vm_ram_gib_unknown_returns_none():
    """Machine non referencee -> None, l'organe travaille en mode slice seule."""
    assert lookup_vm_ram_gib("po-2030-unknown") is None
    assert lookup_vm_ram_gib("") is None


def test_lookup_slice_machine_override_wins_on_real_po2024():
    """Defaut 2, sur le depot reel : la surcharge po-2024 prime sur la generique.

    `persist/po-2024/coursia-ci.slice` est materialisee sur `main` depuis
    #19802. Le test precedent affirmait le repli sur la generique en se
    fondant sur l'absence de ce fichier : son postulat a disparu avec le
    deploiement, il n'etait donc plus un test de l'organe mais un test de
    l'etat du depot.
    """
    path = lookup_slice("po-2024")
    assert path == REPO_SLICE.parent / "po-2024" / "coursia-ci.slice"
    assert path.is_file()
    assert parse_memory_max_gib(path) == 16.0


def test_lookup_slice_falls_back_to_generic_for_unknown_machine():
    """Machine sans surcharge : repli sur la generique, sans crasher."""
    path = lookup_slice("po-9999-unknown")
    assert path == REPO_SLICE
    assert path.is_file()


def test_lookup_slice_machine_override_wins(tmp_path):
    """Si une surcharge machine existe, elle prime sur la generique."""
    override = tmp_path / "scripts" / "ci" / "docker" / "linux-runner" / "persist" / "po-2024" / "coursia-ci.slice"
    override.parent.mkdir(parents=True)
    override.write_text("[Slice]\nMemoryMax=20G\n", encoding="utf-8")

    import assert_memory_budget as amb
    original_root = amb.REPO_ROOT
    amb.REPO_ROOT = tmp_path
    try:
        path = lookup_slice("po-2024")
        assert path == override
        assert parse_memory_max_gib(path) == 20.0
    finally:
        amb.REPO_ROOT = original_root


def test_from_supervise_defaults_reads_caps():
    """Defaut 1 : derivation depuis supervise.sh lit les defauts MEMORY/CPUS.

    Le superviseur documente en tete les N par defaut (2 start, 24 waiters,
    2 lean) et expose les caps via variables d'env. La derivation doit
    reproduire l'esprit du deploiement reel sans dependre du snapshot JSON
    maintenu a la main.
    """
    import tempfile

    with tempfile.NamedTemporaryFile(mode="w", suffix=".sh", delete=False) as f:
        f.write('#!/usr/bin/env bash\n')
        f.write('COURSIA_RUNNER_MEMORY="1536m"\n')
        f.write('COURSIA_RUNNER_WAITER_MEMORY="512m"\n')
        f.write('COURSIA_LEAN_RUNNER_MEMORY="6g"\n')
        f.write('echo "defaut 2 start, 24 waiters, 2 lean"\n')
        path = Path(f.name)
    try:
        snap = BudgetSnapshot.from_supervise_defaults(path, "po-2024")
        # 2 x 1.5 + 24 x 0.5 + 2 x 6.0 = 3 + 12 + 12 = 27.0 GiB
        assert snap.composition_total_gib == 27.0
        assert snap.composition["start"].instances == 2
        assert snap.composition["start"].cap_gib == 1.5
        assert snap.composition["waiters"].instances == 24
        assert snap.composition["waiters"].cap_gib == 0.5
        assert snap.composition["lean"].instances == 2
        assert snap.composition["lean"].cap_gib == 6.0
        assert snap.notes  # trace de provenance
    finally:
        path.unlink()


def test_from_supervise_defaults_falls_back_when_missing():
    """Variables absentes -> defauts code en dur (defaut 1 securite)."""
    import tempfile

    with tempfile.NamedTemporaryFile(mode="w", suffix=".sh", delete=False) as f:
        f.write('#!/usr/bin/env bash\n')
        f.write('echo "rien ici"\n')
        path = Path(f.name)
    try:
        snap = BudgetSnapshot.from_supervise_defaults(path, "po-2024")
        # Defauts code en dur : 1536m / 512m / 6g -> 1.5 / 0.5 / 6.0
        assert snap.composition["start"].cap_gib == 1.5
        assert snap.composition["waiters"].cap_gib == 0.5
        assert snap.composition["lean"].cap_gib == 6.0
    finally:
        path.unlink()


# --------------------------------------------------------------------------
# Composition derivee des unites DEPLOYEES (defaut 1, revue coordinateur du
# 2026-10-08). Ces tests portent sur le fichier des unites, pas sur un
# instantane : c'est le point du defaut -- l'organe doit suivre le
# deploiement, donc le postulat du test doit lui aussi etre lu au deploiement.
# --------------------------------------------------------------------------


def test_from_deployed_units_follows_the_dropin_on_real_po2024():
    """L'effectif waiters vient du drop-in deploye, pas d'une constante.

    po-2024 abaisse l'effectif de la jambe waiters par un drop-in, sans
    toucher l'unite partagee avec ai-01. Un organe qui lit une constante
    (24 documentes, 12 dans l'unite generique) annonce 12 ou 24 slots la ou
    la machine en execute 6, et rougit a tort. Le drop-in est re-parse ici :
    l'organe n'est pas cru sur parole.
    """
    import re as _re

    persist = REPO_ROOT / "scripts" / "ci" / "docker" / "linux-runner" / "persist"
    dropin = persist / "po-2024" / "coursia-waiters.service.d" / "10-sizing.conf"
    assert dropin.is_file(), "drop-in po-2024 attendu sur main (#19802)"
    dm = _re.search(
        r"^ExecStart=.*coursia-waiters-start\.sh\s+(\d+)",
        dropin.read_text(encoding="utf-8"),
        _re.MULTILINE,
    )
    assert dm, "ExecStart attendu dans le drop-in"
    expected = int(dm.group(1))

    snap = BudgetSnapshot.from_deployed_units("po-2024")
    assert snap.machine == "po-2024"
    assert set(snap.composition) == {"start", "waiters", "lean"}
    assert snap.composition["waiters"].instances == expected

    # L'unite generique (celle d'ai-01) ne doit PAS gagner quand elle differe :
    # ce serait un dimensionnement pris sur une machine et applique a l'autre.
    gm = _re.search(
        r"^ExecStart=.*coursia-waiters-start\.sh\s+(\d+)",
        (persist / "coursia-waiters.service").read_text(encoding="utf-8"),
        _re.MULTILINE,
    )
    if gm and int(gm.group(1)) != expected:
        assert snap.composition["waiters"].instances != int(gm.group(1))

    summed = sum(f.total_gib for f in snap.composition.values())
    assert abs(summed - snap.composition_total_gib) < 0.01
    assert snap.notes


def test_from_deployed_units_dropin_beats_base_unit(tmp_path):
    """Un drop-in qui redefinit l'ExecStart gagne sur l'unite de base."""
    (tmp_path / "coursia-runner.service").write_text(
        "[Service]\nExecStart=/usr/local/bin/coursia-runner-start.sh start 4\n",
        encoding="utf-8",
    )
    (tmp_path / "coursia-waiters.service").write_text(
        "[Service]\nExecStart=/usr/local/bin/coursia-waiters-start.sh 12\n",
        encoding="utf-8",
    )
    (tmp_path / "coursia-lean.service").write_text(
        "[Service]\nExecStart=/usr/local/bin/coursia-lean-start.sh 2\n",
        encoding="utf-8",
    )
    dropin_dir = tmp_path / "po-2024" / "coursia-waiters.service.d"
    dropin_dir.mkdir(parents=True)
    # Forme systemd reelle : ExecStart= vide (reset) puis la nouvelle ligne.
    (dropin_dir / "10-sizing.conf").write_text(
        "[Service]\nExecStart=\n"
        "ExecStart=/usr/local/bin/coursia-waiters-start.sh 6\n",
        encoding="utf-8",
    )

    snap = BudgetSnapshot.from_deployed_units("po-2024", tmp_path)
    assert snap.composition["start"].instances == 4
    assert snap.composition["waiters"].instances == 6  # le drop-in gagne
    assert snap.composition["lean"].instances == 2
    # Caps non declares -> defauts de la jambe (1536m / 512m / 6g).
    assert snap.composition["start"].total_gib == 6.0
    assert snap.composition["waiters"].total_gib == 3.0
    assert snap.composition["lean"].total_gib == 12.0
    assert snap.composition_total_gib == 21.0


def test_from_deployed_units_reads_cap_from_environment(tmp_path):
    """Le cap unitaire vient de `Environment=` quand l'unite le declare."""
    (tmp_path / "coursia-runner.service").write_text(
        "[Service]\nEnvironment=COURSIA_RUNNER_MEMORY=2g\n"
        "ExecStart=/usr/local/bin/coursia-runner-start.sh start 2\n",
        encoding="utf-8",
    )
    (tmp_path / "coursia-waiters.service").write_text(
        "[Service]\nEnvironment=COURSIA_RUNNER_WAITER_MEMORY=256m\n"
        "ExecStart=/usr/local/bin/coursia-waiters-start.sh 4\n",
        encoding="utf-8",
    )
    (tmp_path / "coursia-lean.service").write_text(
        "[Service]\nExecStart=/usr/local/bin/coursia-lean-start.sh 1\n",
        encoding="utf-8",
    )
    snap = BudgetSnapshot.from_deployed_units("po-2024", tmp_path)
    assert snap.composition["start"].cap_gib == 2.0
    assert snap.composition["waiters"].cap_gib == 0.25
    assert snap.composition["start"].total_gib == 4.0
    assert snap.composition["waiters"].total_gib == 1.0


def test_from_deployed_units_missing_unit_raises(tmp_path):
    """Une jambe absente leve : l'organe ne devine pas un effectif."""
    (tmp_path / "coursia-runner.service").write_text(
        "ExecStart=/usr/local/bin/coursia-runner-start.sh start 4\n",
        encoding="utf-8",
    )
    with pytest.raises(FileNotFoundError):
        BudgetSnapshot.from_deployed_units("po-2024", tmp_path)


def test_from_deployed_units_missing_execstart_raises(tmp_path):
    """Unite presente mais ExecStart illisible : refus, pas d'effectif invente."""
    for unit in ("coursia-runner.service", "coursia-waiters.service", "coursia-lean.service"):
        (tmp_path / unit).write_text("[Service]\nDescription=vide\n", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        BudgetSnapshot.from_deployed_units("po-2024", tmp_path)


def test_cli_default_reads_deployed_units_not_snapshot():
    """Le defaut de la CLI est le deploiement -- pas le JSON recopie a la main.

    Le workflow CI appelle l'organe SANS drapeau. Si le defaut redevenait le
    snapshot, l'organe remesurerait sa propre constante et le rouge fondateur
    reviendrait sans qu'aucun test ne le signale : c'est ce que ce test ferme.
    """
    import subprocess

    proc = subprocess.run(
        [sys.executable, str(REPO_ROOT / "scripts" / "ci" / "assert_memory_budget.py"), "--json"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        cwd=str(REPO_ROOT),
    )
    payload = json.loads(proc.stdout)
    assert "unites deployees" in payload["source"]
    joined = "\n".join(payload["details"])
    for leg in ("start", "waiters", "lean"):
        assert leg in joined
    assert "docker" not in joined  # la famille du snapshot JSON, pas du deploiement
    assert proc.returncode == (1 if payload["verdict"] == "INCOHERENT" else 0)
