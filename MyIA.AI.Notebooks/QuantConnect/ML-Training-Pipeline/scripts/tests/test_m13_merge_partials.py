"""Tests for the per-coin partial merge of the M13 cluster run.

The cluster grid is split across detached processes by COIN. That split is safe
only because `_aggregate_cell` folds one (coin, horizon) cell over its seeds --
no aggregation boundary is crossed between processes. These tests pin the two
ways a split can silently corrupt the artifact:

  * a coin covered by TWO partials (an overlapping split would double-count its
    seeds, and the four-state aggregate would then read "8/8" where the grid
    holds "4/4" -- a unanimity that never happened);
  * a coin covered by NONE (the manifest would advertise 7 assets while the
    aggregate table silently held 6).

Both must raise, never merge into a plausible-looking artifact.
"""

from __future__ import annotations

import json

import pytest

from merge_m13_partials import CLUSTER_COINS, PARTIALS, merge
from m13_ms_har import HORIZONS, SEEDS

PARTIAL_TO_COINS = {
    "p_btc.json": ["BTC-USD"],
    "p_eth.json": ["ETH-USD"],
    "p_remote.json": ["SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD"],
}


def _combo(coin: str, horizon: int, seed: int) -> dict:
    return {"coin": coin, "horizon": horizon, "seed": seed, "dm_verdict": "INCONCLUSIVE"}


def _aggregate(coin: str, horizon: int) -> dict:
    return {"coin": coin, "horizon": horizon, "seed": "aggregate", "aggregate_verdict": "INCONCLUSIVE"}


def _write_partial(results_dir, name: str, coins: list[str]) -> None:
    combos = [_combo(c, h, s) for c in coins for h in HORIZONS for s in SEEDS]
    aggregates = [_aggregate(c, h) for c in coins for h in HORIZONS]
    (results_dir / name).write_text(
        json.dumps({"combos": combos, "aggregates": aggregates, "elapsed_s": 1.0}),
        encoding="utf-8",
    )


def _write_all(results_dir) -> None:
    for name, coins in PARTIAL_TO_COINS.items():
        _write_partial(results_dir, name, coins)


def test_merge_covers_the_whole_cluster_grid(tmp_path) -> None:
    _write_all(tmp_path)

    merged = merge(tmp_path)

    assert merged["n_combos"] == len(CLUSTER_COINS) * len(HORIZONS) * len(SEEDS) == 84
    assert len(merged["aggregates"]) == len(CLUSTER_COINS) * len(HORIZONS) == 21
    assert merged["coins"] == CLUSTER_COINS


def test_merge_orders_rows_by_cluster_coin_then_horizon_then_seed(tmp_path) -> None:
    """Row order must be reproducible: the manifest anchors per-coin SHA-256 over these rows."""
    _write_all(tmp_path)

    merged = merge(tmp_path)

    keys = [(r["coin"], r["horizon"], r["seed"]) for r in merged["combos"]]
    assert keys == sorted(keys, key=lambda k: (CLUSTER_COINS.index(k[0]), k[1], k[2]))
    agg_keys = [(r["coin"], r["horizon"]) for r in merged["aggregates"]]
    assert agg_keys == sorted(agg_keys, key=lambda k: (CLUSTER_COINS.index(k[0]), k[1]))


def test_merge_refuses_a_missing_partial(tmp_path) -> None:
    _write_all(tmp_path)
    (tmp_path / PARTIALS[1]).unlink()

    with pytest.raises(FileNotFoundError, match="did not finish"):
        merge(tmp_path)


def test_merge_refuses_a_coin_covered_twice(tmp_path) -> None:
    """An overlapping split double-counts seeds -- the aggregate would read a false unanimity.

    BTC is already owned by p_btc.json; re-listing it in p_remote.json makes the
    grid hold 24 BTC rows where it holds 12, and the four-state aggregate would
    then fold "8/8" seeds into a unanimity that never happened. Every cluster
    coin is still present, so this can only trip the overlap guard.
    """
    _write_all(tmp_path)
    _write_partial(tmp_path, PARTIALS[2], CLUSTER_COINS)

    with pytest.raises(ValueError, match="unexpected combo count"):
        merge(tmp_path)


def test_merge_refuses_a_cluster_coin_covered_by_none(tmp_path) -> None:
    _write_all(tmp_path)
    _write_partial(tmp_path, PARTIALS[2], ["SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD"])  # DOT lost

    with pytest.raises(ValueError, match="absent from the merged rows"):
        merge(tmp_path)
