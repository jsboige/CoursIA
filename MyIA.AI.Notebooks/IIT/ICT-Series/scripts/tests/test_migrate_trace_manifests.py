"""Tests de la migration canonique des manifestes de traces (contrat v1).

Couvre les quatre statuts (MIGRATED / DEJA / SANS_META / SANS_DISCRIMINANT),
la preservation byte-identique des tableaux, la preservation de la
compression d'origine, l'idempotence, et le fait que le contrat revalide
SANS warning apres stamp -- le but meme de la migration (#15476
acceptance #4 : declaration explicite preferred a l'inference).
"""
from __future__ import annotations

import json
import sys
import warnings
from pathlib import Path

import numpy as np

# scripts/ et ict/ vivent deux niveaux au-dessus de ce fichier de test
# (meme cablage que test_ict25_protocol.py).
HERE = Path(__file__).resolve().parent
SCRIPTS = HERE.parent
SERIES = SCRIPTS.parent
for cand in (SCRIPTS, SERIES):
    if str(cand) not in sys.path:
        sys.path.insert(0, str(cand))

from ict.trace_contract import validate_manifest  # noqa: E402
from migrate_trace_manifests import (  # noqa: E402
    DEJA,
    MIGRATED,
    SANS_DISCRIMINANT,
    SANS_META,
    migrate_file,
)


def _write_npz(path: Path, meta: dict, *, compressed: bool = False) -> None:
    saver = np.savez_compressed if compressed else np.savez
    saver(
        path,
        __meta__=np.array(json.dumps(meta)),
        ids=np.array([[3, 1, 2], [0, 5, 4]], dtype=np.int32),
        vals=np.array([[0.5, 0.25, 0.125], [0.75, 0.0, 0.625]], dtype=np.float32),
    )


def _base_meta(**extra: object) -> dict:
    return {"d_sae": 8, "k": 3, "layer": 12, **extra}


def test_migrate_sae_historique_stampe_et_revalide(tmp_path: Path) -> None:
    p = tmp_path / "sae_hist.npz"
    _write_npz(p, _base_meta(sae_repo="Qwen-Scope/W64K", sae_k=50))
    status, inst, _ = migrate_file(p, apply=True)
    assert (status, inst) == (MIGRATED, "sae")

    z = np.load(p, allow_pickle=False)
    meta = json.loads(str(z["__meta__"]))
    assert meta["instrument"] == "sae"
    assert meta["contract_version"]
    # tableaux inchanges, dtype inclus
    assert np.array_equal(z["ids"], np.array([[3, 1, 2], [0, 5, 4]], dtype=np.int32))
    assert z["vals"].dtype == np.float32
    z.close()
    # le contrat revalide SANS warning : plus d'inference retro-compat.
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        valide = validate_manifest(meta, strict=False, expected="sae")
    assert valide["instrument"] == "sae"


def test_migrate_jlens_via_champs_lens(tmp_path: Path) -> None:
    p = tmp_path / "jlens_hist.npz"
    _write_npz(p, _base_meta(lens_repo="jlens-9b", lens_rank=32))
    status, inst, _ = migrate_file(p, apply=True)
    assert (status, inst) == (MIGRATED, "jlens")


def test_migrate_deja_declare_idempotent(tmp_path: Path) -> None:
    p = tmp_path / "deja.npz"
    _write_npz(p, _base_meta(instrument="sae", sae_k=50))
    assert migrate_file(p, apply=True) == (DEJA, "sae", "deja declare")
    assert migrate_file(p, apply=True) == (DEJA, "sae", "deja declare")


def test_migrate_sans_meta_et_sans_discriminant_intacts(tmp_path: Path) -> None:
    # sans __meta__ : non touche, statut SANS_META
    p1 = tmp_path / "no_meta.npz"
    np.savez(p1, ids=np.zeros(2, dtype=np.int32))
    before1 = p1.read_bytes()
    status, _, _ = migrate_file(p1, apply=True)
    assert status == SANS_META
    assert p1.read_bytes() == before1

    # meta sans discriminant : non touche, statut SANS_DISCRIMINANT
    p2 = tmp_path / "no_disc.npz"
    _write_npz(p2, _base_meta())  # ni instrument ni discriminant
    before2 = p2.read_bytes()
    status, inst, _ = migrate_file(p2, apply=True)
    assert (status, inst) == (SANS_DISCRIMINANT, "")
    assert p2.read_bytes() == before2


def test_migrate_preserve_compression_deflate(tmp_path: Path) -> None:
    import zipfile

    p = tmp_path / "comp.npz"
    _write_npz(p, _base_meta(sae_k=50), compressed=True)
    migrate_file(p, apply=True)
    with zipfile.ZipFile(p) as zf:
        kinds = {info.compress_type for info in zf.infolist()}
    assert kinds == {zipfile.ZIP_DEFLATED}


def test_dry_run_necrit_pas(tmp_path: Path) -> None:
    p = tmp_path / "dry.npz"
    _write_npz(p, _base_meta(sae_k=50))
    before = p.read_bytes()
    status, inst, _ = migrate_file(p, apply=False)
    assert (status, inst) == ("TODO", "sae")
    assert p.read_bytes() == before
