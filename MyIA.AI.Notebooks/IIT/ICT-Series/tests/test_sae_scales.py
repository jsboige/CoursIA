"""Contrat CPU du registre des sept backbones SAE Qwen-Scope (#8236)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.sae_scales import (
    QWEN_SCOPE_SCALES,
    coverage_report,
    scan_fidelity_traces,
)

EXPECTED_LAYERS = {
    "Qwen/Qwen3-1.7B-Base": 14,
    "Qwen/Qwen3-8B-Base": 18,
    "Qwen/Qwen3-30B-A3B-Base": 24,
    "Qwen/Qwen3.5-2B-Base": 12,
    "Qwen/Qwen3.5-9B-Base": 16,
    "Qwen/Qwen3.5-27B": 32,
    "Qwen/Qwen3.5-35B-A3B-Base": 20,
}

EXPECTED_VARIANTS = {
    "Qwen/Qwen3-1.7B-Base": ((32768, 50), (32768, 100)),
    "Qwen/Qwen3-8B-Base": ((65536, 50), (65536, 100)),
    "Qwen/Qwen3-30B-A3B-Base": ((32768, 50), (131072, 100)),
    "Qwen/Qwen3.5-2B-Base": ((32768, 50), (32768, 100)),
    "Qwen/Qwen3.5-9B-Base": ((65536, 50), (65536, 100)),
    "Qwen/Qwen3.5-27B": ((81920, 50), (81920, 100)),
    "Qwen/Qwen3.5-35B-A3B-Base": ((32768, 50), (131072, 100)),
}


def _write_trace(directory: Path, filename: str, scale: dict, layer: int) -> Path:
    variant = scale["sae_variants"][0]
    meta = {
        "model": scale["model"],
        "n_layers": scale["n_layers"],
        "layer": layer,
        "d_model": scale["d_model"],
        "d_sae": variant["d_sae"],
        "k": variant["k"],
        "sae_repo": variant["repo"],
    }
    path = directory / filename
    np.savez_compressed(path, meta=np.array(json.dumps(meta)))
    return path


def test_collection_contient_exactement_sept_backbones_et_quatorze_variantes():
    models = [scale["model"] for scale in QWEN_SCOPE_SCALES]
    assert len(models) == len(set(models)) == 7
    assert sum(scale["generation"] == "Qwen3" for scale in QWEN_SCOPE_SCALES) == 3
    assert sum(scale["generation"] == "Qwen3.5" for scale in QWEN_SCOPE_SCALES) == 4
    assert sum(len(scale["sae_variants"]) for scale in QWEN_SCOPE_SCALES) == 14
    assert all({variant["k"] for variant in scale["sae_variants"]} == {50, 100}
               for scale in QWEN_SCOPE_SCALES)
    assert all(scale["available_layers"] == tuple(range(scale["n_layers"]))
               for scale in QWEN_SCOPE_SCALES)


def test_largeurs_et_repositories_correspondent_a_la_collection_verifiee():
    for scale in QWEN_SCOPE_SCALES:
        variants = scale["sae_variants"]
        assert tuple((variant["d_sae"], variant["k"]) for variant in variants) == \
            EXPECTED_VARIANTS[scale["model"]]
        assert all(variant["repo"].startswith("Qwen/SAE-Res-") for variant in variants)
        assert all(variant["repo"].endswith(f"L0_{variant['k']}") for variant in variants)


def test_profondeur_relative_donne_les_sept_couches_attendues(tmp_path):
    report = coverage_report(tmp_path, layer_frac=0.5)
    assert {row["model"]: row["target_layer"] for row in report["rows"]} == EXPECTED_LAYERS


def test_couverture_synthetique_compte_quatre_backbones_sur_sept(tmp_path):
    for index, scale in enumerate(QWEN_SCOPE_SCALES[:2] + QWEN_SCOPE_SCALES[3:5]):
        _write_trace(
            tmp_path,
            f"calib_fidelity_capture_{index}.npz",
            scale,
            EXPECTED_LAYERS[scale["model"]],
        )
    report = coverage_report(tmp_path)
    assert report["n_collected"] == 4
    assert report["n_total"] == 7
    assert report["generation_counts"] == {
        "Qwen3": {"collected": 2, "total": 3},
        "Qwen3.5": {"collected": 2, "total": 4},
    }


def test_mauvaise_profondeur_est_signalee_sans_etre_comptee(tmp_path):
    scale = QWEN_SCOPE_SCALES[0]
    path = _write_trace(tmp_path, "calib_fidelity_wrong_layer.npz", scale, layer=7)
    report = coverage_report(tmp_path)
    row = next(item for item in report["rows"] if item["model"] == scale["model"])
    assert not row["collected"]
    assert row["extra_depths"] == [{"file": path.name, "layer": 7}]


def test_identite_provient_des_metadonnees_pas_du_nom_de_fichier(tmp_path):
    scale = next(item for item in QWEN_SCOPE_SCALES if item["model"].endswith("1.7B-Base"))
    path = _write_trace(
        tmp_path,
        "calib_fidelity_qwen3-17b-base_layer14of28.npz",
        scale,
        layer=14,
    )
    scanned = scan_fidelity_traces(tmp_path)
    assert scanned == [{"file": path.name, **json.loads(str(np.load(path)["meta"]))}]
    assert coverage_report(tmp_path)["n_collected"] == 1


def test_metadonnees_incompatibles_ne_sont_pas_comptees(tmp_path):
    scale = QWEN_SCOPE_SCALES[0]
    path = _write_trace(tmp_path, "calib_fidelity_bad_width.npz", scale, layer=14)
    with np.load(path, allow_pickle=False) as data:
        meta = json.loads(str(data["meta"]))
    meta["d_model"] = 4096
    np.savez_compressed(path, meta=np.array(json.dumps(meta)))
    report = coverage_report(tmp_path)
    row = next(item for item in report["rows"] if item["model"] == scale["model"])
    assert not row["collected"]
    assert row["incompatible_traces"] == [path.name]


def test_traces_committees_forment_un_cliquet_d_au_moins_quatre_backbones():
    traces_dir = Path(__file__).resolve().parent.parent / "traces"
    report = coverage_report(traces_dir)
    assert report["n_collected"] >= 4
    assert not report["unknown_traces"]
    assert {row["model"] for row in report["rows"] if row["collected"]} >= {
        "Qwen/Qwen3-1.7B-Base",
        "Qwen/Qwen3-8B-Base",
        "Qwen/Qwen3.5-2B-Base",
        "Qwen/Qwen3.5-9B-Base",
    }
    extras = {
        row["model"]: {item["layer"] for item in row["extra_depths"]}
        for row in report["rows"] if row["extra_depths"]
    }
    assert extras["Qwen/Qwen3-1.7B-Base"] == {7}
    assert extras["Qwen/Qwen3.5-2B-Base"] == {6}
