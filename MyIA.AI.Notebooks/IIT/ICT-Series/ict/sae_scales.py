"""Registre GPU-free de la collection SAE officielle Qwen-Scope (#8236).

La collection publique comprend sept backbones Qwen3/Qwen3.5, chacun publie
avec deux variantes de sparsité (L0_50 et L0_100). Ce module matérialise ce
contrat sans accès réseau, transpose une profondeur relative via
:func:`ict.sae_traces.resolve_capture_layer`, puis mesure la couverture des
traces de fidélité committées à partir de leurs métadonnées embarquées.

Numpy uniquement : aucun téléchargement de modèle et aucun import torch. Les
trois grandes échelles absentes restent explicitement GPU-gated ; leur absence
n'est jamais transformée en résultat simulé.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .sae_traces import resolve_capture_layer

__all__ = [
    "QWEN_SCOPE_SCALES",
    "coverage_report",
    "format_coverage",
    "scan_fidelity_traces",
]


QWEN_SCOPE_SCALES = (
    {
        "model": "Qwen/Qwen3-1.7B-Base",
        "generation": "Qwen3",
        "architecture": "dense",
        "n_layers": 28,
        "d_model": 2048,
        "available_layers": tuple(range(28)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3-1.7B-Base-W32K-L0_50", "d_sae": 32768, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3-1.7B-Base-W32K-L0_100", "d_sae": 32768, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3-8B-Base",
        "generation": "Qwen3",
        "architecture": "dense",
        "n_layers": 36,
        "d_model": 4096,
        "available_layers": tuple(range(36)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3-8B-Base-W64K-L0_50", "d_sae": 65536, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3-8B-Base-W64K-L0_100", "d_sae": 65536, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3-30B-A3B-Base",
        "generation": "Qwen3",
        "architecture": "moe",
        "n_layers": 48,
        "d_model": 2048,
        "available_layers": tuple(range(48)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3-30B-A3B-Base-W32K-L0_50", "d_sae": 32768, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3-30B-A3B-Base-W128K-L0_100", "d_sae": 131072, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3.5-2B-Base",
        "generation": "Qwen3.5",
        "architecture": "dense",
        "n_layers": 24,
        "d_model": 2048,
        "available_layers": tuple(range(24)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50", "d_sae": 32768, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_100", "d_sae": 32768, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3.5-9B-Base",
        "generation": "Qwen3.5",
        "architecture": "dense",
        "n_layers": 32,
        "d_model": 4096,
        "available_layers": tuple(range(32)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50", "d_sae": 65536, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_100", "d_sae": 65536, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3.5-27B",
        "generation": "Qwen3.5",
        "architecture": "dense",
        "n_layers": 64,
        "d_model": 5120,
        "available_layers": tuple(range(64)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3.5-27B-W80K-L0_50", "d_sae": 81920, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3.5-27B-W80K-L0_100", "d_sae": 81920, "k": 100},
        ),
    },
    {
        "model": "Qwen/Qwen3.5-35B-A3B-Base",
        "generation": "Qwen3.5",
        "architecture": "moe",
        "n_layers": 40,
        "d_model": 2048,
        "available_layers": tuple(range(40)),
        "sae_variants": (
            {"repo": "Qwen/SAE-Res-Qwen3.5-35B-A3B-Base-W32K-L0_50", "d_sae": 32768, "k": 50},
            {"repo": "Qwen/SAE-Res-Qwen3.5-35B-A3B-Base-W128K-L0_100", "d_sae": 131072, "k": 100},
        ),
    },
)

_REQUIRED_META = {"model", "n_layers", "layer", "d_model", "d_sae", "k", "sae_repo"}


def scan_fidelity_traces(traces_dir: str | Path) -> list[dict]:
    """Lit les métadonnées des traces de fidélité sans déduire leur identité du nom.

    Seuls les fichiers ``calib_fidelity_*.npz`` appartiennent à ce protocole.
    Le nom reste informatif : ``meta['model']`` est l'unique source d'identité,
    car les slugs historiques ``1-7b`` et ``17b`` sont ambigus.
    """
    traces = []
    for path in sorted(Path(traces_dir).glob("calib_fidelity_*.npz")):
        with np.load(path, allow_pickle=False) as data:
            if "meta" not in data.files:
                raise ValueError(f"{path.name} : métadonnée 'meta' absente")
            meta = json.loads(str(data["meta"]))
        missing = _REQUIRED_META - set(meta)
        if missing:
            raise ValueError(f"{path.name} : métadonnées incomplètes, manque {sorted(missing)}")
        traces.append({"file": path.name, **meta})
    return traces


def coverage_report(
    traces_dir: str | Path | None = None,
    *,
    layer_frac: float = 0.5,
) -> dict:
    """Compare les traces committées aux sept backbones à profondeur appariée."""
    if traces_dir is None:
        traces_dir = Path(__file__).resolve().parent.parent / "traces"
    traces = scan_fidelity_traces(traces_dir)
    by_model: dict[str, list[dict]] = {}
    for trace in traces:
        by_model.setdefault(trace["model"], []).append(trace)

    rows = []
    known_models = {scale["model"] for scale in QWEN_SCOPE_SCALES}
    for scale in QWEN_SCOPE_SCALES:
        expected = resolve_capture_layer(scale["n_layers"], layer_frac=layer_frac)
        variants_by_repo = {
            variant["repo"]: variant for variant in scale["sae_variants"]
        }
        matches = []
        extra_depths = []
        incompatible = []
        for trace in by_model.get(scale["model"], []):
            variant = variants_by_repo.get(trace["sae_repo"])
            metadata_ok = (
                int(trace["n_layers"]) == scale["n_layers"]
                and int(trace["d_model"]) == scale["d_model"]
                and variant is not None
                and int(trace["d_sae"]) == variant["d_sae"]
                and int(trace["k"]) == variant["k"]
                and int(trace["layer"]) in scale["available_layers"]
            )
            if not metadata_ok:
                incompatible.append(trace["file"])
            elif int(trace["layer"]) == expected["layer"]:
                matches.append(trace["file"])
            else:
                extra_depths.append({"file": trace["file"], "layer": int(trace["layer"])})
        rows.append({
            "model": scale["model"],
            "generation": scale["generation"],
            "architecture": scale["architecture"],
            "n_layers": scale["n_layers"],
            "target_layer": expected["layer"],
            "target_layer_frac": expected["layer_frac"],
            "collected": bool(matches),
            "status": "collectée" if matches else "GPU-gated",
            "matched_traces": matches,
            "extra_depths": extra_depths,
            "incompatible_traces": incompatible,
        })

    generation_counts = {}
    for generation in ("Qwen3", "Qwen3.5"):
        generation_rows = [row for row in rows if row["generation"] == generation]
        generation_counts[generation] = {
            "collected": sum(row["collected"] for row in generation_rows),
            "total": len(generation_rows),
        }
    unknown = [trace["file"] for trace in traces if trace["model"] not in known_models]
    return {
        "layer_frac_requested": layer_frac,
        "n_collected": sum(row["collected"] for row in rows),
        "n_total": len(rows),
        "generation_counts": generation_counts,
        "rows": rows,
        "unknown_traces": unknown,
    }


def format_coverage(report: dict) -> str:
    """Formate un tableau texte compact pour le notebook de calibration."""
    lines = [
        "modèle                         famille  couche  statut",
        "----------------------------------------------------------",
    ]
    for row in report["rows"]:
        model = row["model"].split("/", 1)[-1]
        layer = f"{row['target_layer']}/{row['n_layers']}"
        lines.append(f"{model:30s} {row['generation']:8s} {layer:>7s}  {row['status']}")
        for extra in row["extra_depths"]:
            lines.append(f"  profondeur supplémentaire : couche {extra['layer']} ({extra['file']})")
        for filename in row["incompatible_traces"]:
            lines.append(f"  métadonnées incompatibles : {filename}")
    lines.append("----------------------------------------------------------")
    lines.append(f"Couverture committée : {report['n_collected']}/{report['n_total']} backbones")
    for generation, counts in report["generation_counts"].items():
        lines.append(f"{generation} : {counts['collected']}/{counts['total']}")
    if report["unknown_traces"]:
        lines.append("Traces hors registre : " + ", ".join(report["unknown_traces"]))
    lines.append("Les absences GPU-gated ne sont ni exécutées ni simulées dans ce notebook CPU.")
    return "\n".join(lines)
