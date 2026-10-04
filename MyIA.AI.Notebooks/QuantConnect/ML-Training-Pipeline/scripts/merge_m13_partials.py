"""Merge the per-coin partial M13 cluster runs into the full artifact + manifest.

The cluster grid (7 coins x 3 horizons x 4 seeds = 84 combos) is split across
detached processes to use idle cores: the serial run measured ~215 s per combo
at 97% single-core, so 19 of 20 logical cores sat idle for ~90 min.

The split is by COIN, which is safe by construction: `_aggregate_cell` folds a
cell over its seeds for one (coin, horizon), so no aggregation boundary is ever
crossed between processes -- each partial owns whole cells end to end. This
merger therefore only concatenates, and never re-aggregates.

Outputs, matching the family's (M4/M15/M17) shape:
  * the full artifact (large, off-repo per results-artifact-policy #15890),
  * the compact in-repo manifest with verdicts, per-cell alignment diagnostics
    and per-coin SHA-256 anchors of the full rows.

Usage:
    python merge_m13_partials.py [--results-dir results/m13_ms_har]
                                 [--full-out PATH] [--manifest-out PATH]
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from m13_ms_har import HORIZONS, SEEDS, _write_cluster_manifest

SCRIPTS_DIR = Path(__file__).resolve().parent
DEFAULT_RESULTS_DIR = SCRIPTS_DIR / "results" / "m13_ms_har"
PARTIALS = ["p_btc.json", "p_eth.json", "p_remote.json"]

# The 7-asset cluster universe, in the family's canonical order.
CLUSTER_COINS = ["BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"]


def _load_partial(path: Path) -> dict:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def merge(results_dir: Path) -> dict:
    """Concatenate the partials and return the merged artifact dict.

    Raises if a partial is missing, if a coin is covered twice (a split that
    silently overlapped would double-count its seeds in the aggregate), or if
    the merged grid is not the expected 7 coins x 3 horizons x 4 seeds.
    """
    combos: list[dict] = []
    aggregates: list[dict] = []
    elapsed_total = 0.0
    per_coin_seen: dict[str, int] = {}

    for name in PARTIALS:
        path = results_dir / name
        if not path.exists():
            raise FileNotFoundError(f"missing partial {path} -- the split run did not finish")
        payload = _load_partial(path)
        combos.extend(payload["combos"])
        aggregates.extend(payload["aggregates"])
        elapsed_total = max(elapsed_total, float(payload.get("elapsed_s") or 0.0))
        for row in payload["combos"]:
            per_coin_seen[row["coin"]] = per_coin_seen.get(row["coin"], 0) + 1

    dupes = {c: n for c, n in per_coin_seen.items() if n != len(HORIZONS) * len(SEEDS)}
    if dupes:
        raise ValueError(
            f"coin(s) with an unexpected combo count (expected "
            f"{len(HORIZONS) * len(SEEDS)} = {len(HORIZONS)} horizons x {len(SEEDS)} seeds): {dupes}"
        )
    missing = [c for c in CLUSTER_COINS if c not in per_coin_seen]
    if missing:
        raise ValueError(f"cluster coin(s) absent from the merged rows: {missing}")

    # Stable order so the artifact and the per-coin anchors are reproducible.
    combos.sort(key=lambda r: (CLUSTER_COINS.index(r["coin"]), r["horizon"], r["seed"]))
    aggregates.sort(key=lambda r: (CLUSTER_COINS.index(r["coin"]), r["horizon"]))

    return {
        "note": (
            "Merged cluster revalidation run (#18190 port, Epic #1454). Split by "
            "coin across detached processes; the coin split never crosses an "
            "aggregation boundary (cells are per coin x horizon)."
        ),
        "protocol": (
            "paired-origin: DM legs join walk-forwards on common origin dates and "
            "refuse on shared-target mismatch, never positional truncation"
        ),
        "loss_fn": "mse",
        "dm_centered_errors": True,
        "classic_har_debiased": True,
        "coins": CLUSTER_COINS,
        "horizons": HORIZONS,
        "seeds": SEEDS,
        "n_combos": len(combos),
        "elapsed_s": elapsed_total,
        "combos": combos,
        "aggregates": aggregates,
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results-dir", type=Path, default=DEFAULT_RESULTS_DIR,
                   help="directory holding the p_*.json partials")
    p.add_argument("--full-out", type=Path, default=None,
                   help="merged full artifact path (default: <results-dir>/m13_ms_har_cluster_full.json)")
    p.add_argument("--manifest-out", type=Path, default=None,
                   help=("compact in-repo manifest path "
                         "(default: <scripts>/results/m13_ms_har_cluster_aligned.json)"))
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    args = _parse_args(argv)
    results_dir: Path = args.results_dir
    full_out: Path = args.full_out or results_dir / "m13_ms_har_cluster_full.json"
    manifest_out: Path = args.manifest_out or (SCRIPTS_DIR / "results" / "m13_ms_har_cluster_aligned.json")

    merged = merge(results_dir)

    full_out.parent.mkdir(parents=True, exist_ok=True)
    with open(full_out, "w", encoding="utf-8") as f:
        json.dump(merged, f, indent=2, default=str)
    print(f"Merged artifact: {full_out} ({full_out.stat().st_size} bytes, "
          f"{len(merged['combos'])} combos, {len(merged['aggregates'])} aggregates)")

    _write_cluster_manifest(
        manifest_out,
        merged["combos"],
        merged["aggregates"],
        full_out,
        HORIZONS,
        SEEDS,
        merged["elapsed_s"],
    )
    print(f"Cluster manifest written to {manifest_out}")


if __name__ == "__main__":
    main()
