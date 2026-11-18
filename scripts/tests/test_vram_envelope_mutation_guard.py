#!/usr/bin/env python3
"""Jeu de mutations permanentes pour l'organe d'enveloppe VRAM (#22756).

La review de la PR #22341 (clusterManager-Myia, 2026-10-24) a prouve par
mutation que l'organe `scripts/audit/check_vram_envelope_rederivable.py` ne
gardait que 2 champs sur 10 : muter `provenance.journal_sha256`,
`provenance.trace_bytes`, `provenance.trace_samples` ou
`provenance.trace_span_s` laissait l'organe en sortie 0. Le commit `0b85e093ef`
a branche ces champs sur la re-derivation. Ce temoin etait reste manuel (il
vivait dans la review) : ce test le rend permanent, joue au CI par le job
`Scripts Tests (CPU)` (workflow `Scripts & Notebook-Tools Tests`, via
`pytest.ini` testpaths `scripts/tests`).

Le tableau ci-dessous reprend les mutations de la review telles quelles, champ
par champ, sur une copie temporaire des donnees committes de
`scripts/results/3d_enveloppe_8go/` (l'organe lui-meme ne connait que des
chemins absolus construits depuis son emplacement ; les constantes `RESULTS`
et `TRACES` sont monkeypatchees vers la copie).

Deux cas de la review ne sont PAS des echecs attendus : `427` (dechargement)
et `4195` (minimum de la phase) sont des valeurs presentes dans la fenetre de
leur phase, et le controle des plateaux est deliberatement d'appartenance --
la docstring de l'organe le dit : il verifie la PRESENCE d'un echantillon et
n'arbitre pas lequel merite le nom de palier. Ces deux lignes servent de
temoins de frontiere : si un durcissement futur change ce contrat, ces tests
rougissent et le changement de contrat devient explicite. Mesure au 2026-10-27
sur la tete `0b85e093ef3` : 11 mutations font echouer leur controle nomme,
les 2 temoins de frontiere restent verts, et les manifestes intacts rendent
27 controles verts (12 pour 3D-01, 15 pour 3D-02), 0 echec.
"""

from __future__ import annotations

import json
import re
import shutil
import sys
from pathlib import Path
from typing import Any, Callable

import pytest

AUDIT_DIR = Path(__file__).resolve().parents[1] / "audit"
sys.path.insert(0, str(AUDIT_DIR))

import check_vram_envelope_rederivable as organ  # noqa: E402

_IDX = re.compile(r"^(\w+)\[(\d+)\]$")


def _apply_mutation(manifest: dict, dotted: str, value: Any) -> Any:
    """Ecrase la valeur pointee par `a.b[i].c` et rend l'ancienne valeur."""
    parts = dotted.split(".")
    cursor: Any = manifest
    for part in parts[:-1]:
        match = _IDX.match(part)
        cursor = cursor[match.group(1)][int(match.group(2))] if match else cursor[part]
    match = _IDX.match(parts[-1])
    target = cursor[match.group(1)][int(match.group(2))] if match else cursor
    key = match.group(1) if match else parts[-1]
    previous = target[key]
    target[key] = value
    return previous


@pytest.fixture()
def staged(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Callable[..., None]:
    """Copie les donnees reelles vers tmp, y applique des mutations, rebranche l'organe."""
    real = organ.RESULTS

    def _stage(mutations: list[tuple[str, str, Any]]) -> None:
        copy = tmp_path / "3d_enveloppe_8go"
        shutil.copytree(real, copy)
        for run, dotted, value in mutations:
            manifest_path = copy / organ.RUNS[run]["manifest"]
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            _apply_mutation(manifest, dotted, value)
            manifest_path.write_text(
                json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8"
            )
        monkeypatch.setattr(organ, "RESULTS", copy)
        monkeypatch.setattr(organ, "TRACES", copy / "traces")

    return _stage


# Les 11 mutations dont l'echec est attendu : (run, champ, valeur mutante,
# nom du controle qui doit rougir). Reprises de la review du 2026-10-24.
NEGATIVE_MUTATIONS: list[tuple[str, str, Any, str]] = [
    ("3d01", "vram.peak_mib", 4312, "peak_mib"),
    ("3d02", "vram.profil_par_phase_mib[0].plateau_mib", 3002, "phase[0].plateau_mib"),
    ("3d02", "provenance.journal_sha256", "deadbeef", "journal_sha256"),
    ("3d02", "provenance.trace_bytes", 999999, "trace_bytes"),
    ("3d02", "provenance.trace_samples", 7, "trace_samples"),
    ("3d02", "provenance.trace_span_s", 1.0, "trace_span_s"),
    ("3d01", "vram.temp_max_c", 99, "temp_max_c"),
    ("3d01", "vram.util_max_pct", 11, "util_max_pct"),
    ("3d02", "vram.peak_pct", 99.9, "peak_pct"),
    ("3d01", "vram.idle_mib", 2912, "idle_mib"),
    ("3d01", "vram.idle_mib", 331, "idle_mib"),
]

# Les 2 temoins de frontiere de la meme review : valeurs presentes dans la
# fenetre de leur phase -- l'organe n'arbitre pas (docstring, famille 4).
BOUNDARY_MUTATIONS: list[tuple[str, str, Any, str]] = [
    ("3d02", "vram.profil_par_phase_mib[2].plateau_mib", 427, "phase[2].plateau_mib"),
    ("3d02", "vram.profil_par_phase_mib[1].plateau_mib", 4195, "phase[1].plateau_mib"),
]


def _failed_checks(run: str) -> list[str]:
    report = organ.check_run(run, organ.RUNS[run])
    return [f["check"] for f in report["checks"] if not f["ok"]]


def test_manifestes_intacts_tous_controles_verts(staged) -> None:
    """Controle positif : sans mutation, les deux runs rendent 0 echec."""
    staged(mutations=[])
    assert _failed_checks("3d01") == []
    assert _failed_checks("3d02") == []


@pytest.mark.parametrize(
    ("run", "dotted", "value", "expected_check"),
    NEGATIVE_MUTATIONS,
    ids=[f"{r}-{c.split('.')[-1]}-{v}" for r, c, v, _ in NEGATIVE_MUTATIONS],
)
def test_mutation_fait_echouer_le_controle(
    staged, run: str, dotted: str, value: Any, expected_check: str
) -> None:
    """Controle negatif : la mutation de la review DOIT rougir son controle."""
    staged(mutations=[(run, dotted, value)])
    failed = _failed_checks(run)
    assert expected_check in failed, (
        f"la mutation {dotted} := {value} devait faire echouer {expected_check}; "
        f"echecs observes : {failed or 'aucun (sortie 0)'}"
    )


@pytest.mark.parametrize(
    ("run", "dotted", "value", "check"),
    BOUNDARY_MUTATIONS,
    ids=[f"{r}-frontiere-{c.split('.')[-1]}" for r, c, v, _ in BOUNDARY_MUTATIONS],
)
def test_frontiere_appartenance_documentee(
    staged, run: str, dotted: str, value: Any, check: str
) -> None:
    """Temoins de frontiere : valeurs presentes dans la fenetre, contrat d'appartenance.

    La docstring de l'organe (famille 4) verifie la PRESENCE d'un echantillon
    dans la fenetre de la phase et n'arbitre pas lequel merite le nom de
    palier : ces deux mutations de la review restent donc vertes. Si ce test
    rougit, le contrat des plateaux a change -- que le changement soit assume
    et la docstring mise a jour dans le meme geste.
    """
    staged(mutations=[(run, dotted, value)])
    failed = _failed_checks(run)
    assert failed == [], (
        f"la mutation {dotted} := {value} est un temoin de frontiere (valeur "
        f"presente dans la fenetre) ; echecs inattendus : {failed}"
    )


def test_mutations_non_vaines(staged, tmp_path: Path) -> None:
    """Aucune valeur mutante ne doit egaler la valeur declaree d'origine.

    Une mutation egale a l'original serait un controle negatif vide : elle ne
    peut pas faire echouer l'organe et ne prouve rien. Ce garde rend le
    tableau auto-verifiable quand les manifestes evoluent.
    """
    staged(mutations=[])
    for run, dotted, value, _ in NEGATIVE_MUTATIONS + BOUNDARY_MUTATIONS:
        manifest = json.loads(
            (tmp_path / "3d_enveloppe_8go" / organ.RUNS[run]["manifest"]).read_text(
                encoding="utf-8"
            )
        )
        previous = _apply_mutation(manifest, dotted, value)
        assert previous != value, (
            f"mutation vide pour {dotted} ({run}) : la valeur declaree vaut deja {value}"
        )
