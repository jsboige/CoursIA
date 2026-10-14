"""M18 cluster aggregation tests — collapse rule, sign test, fail-closed guards (#1454)."""

from __future__ import annotations

import json

import pytest

from m18_tsfm_cluster import (
    BASELINES,
    CLUSTER_COINS,
    VIEW_HORIZONS,
    aggregate,
    coin_sign_test,
    collapse_asset,
    per_coin_anchors,
)


def _row(coin, horizon, baseline, verdict, edge=10.0, p=0.001, identical=True):
    return {
        "coin": coin, "horizon": horizon, "baseline": baseline,
        "verdict": verdict, "edge_pct_mean": edge, "dm_p_median": p,
        "seeds_bit_identical": identical, "n_seeds": 4,
    }


def _full_summary(verdict_fn):
    return [
        _row(coin, h, b, verdict_fn(coin, h, b))
        for coin in CLUSTER_COINS
        for h in (1, 5, 10, 22)
        for b in BASELINES
    ]


# --- horizon collapse (M16 rule) -------------------------------------------

def test_collapse_strict_majority_beats() -> None:
    rows = [
        _row("BTC-USD", 1, "log_har", "BEATS"),
        _row("BTC-USD", 5, "log_har", "BEATS"),
        _row("BTC-USD", 10, "log_har", "INCONCLUSIVE"),
    ]
    assert collapse_asset(rows) == "BEATS"


def test_collapse_strict_majority_wins_over_single_no_beats() -> None:
    # M16 canonical precedence (har_asymmetric.py): strict BEATS majority is
    # checked first — 2/3 BEATS outweighs one NO BEATS horizon.
    rows = [
        _row("BTC-USD", 1, "log_har", "BEATS"),
        _row("BTC-USD", 5, "log_har", "NO BEATS"),
        _row("BTC-USD", 10, "log_har", "BEATS"),
    ]
    assert collapse_asset(rows) == "BEATS"


def test_collapse_no_majority_with_loss_is_no_beats() -> None:
    rows = [
        _row("BTC-USD", 1, "log_har", "BEATS"),
        _row("BTC-USD", 5, "log_har", "NO BEATS"),
        _row("BTC-USD", 10, "log_har", "INCONCLUSIVE"),
    ]
    assert collapse_asset(rows) == "NO BEATS"


def test_collapse_inconclusive_when_no_majority_no_loss() -> None:
    rows = [
        _row("BTC-USD", 1, "log_har", "BEATS"),
        _row("BTC-USD", 5, "log_har", "INCONCLUSIVE"),
        _row("BTC-USD", 10, "log_har", "INCONCLUSIVE"),
    ]
    assert collapse_asset(rows) == "INCONCLUSIVE"


# --- coin-level sign test ---------------------------------------------------

def test_sign_test_all_beats_rejects_null() -> None:
    verdicts = [{"coin": c, "verdict": "BEATS"} for c in CLUSTER_COINS]
    st = coin_sign_test(verdicts)
    assert st["n_beats"] == 7
    assert st["p_value"] == pytest.approx(0.0078125)
    assert st["verdict"] == "BEATS"


def test_sign_test_one_beat_is_no_beats_cluster() -> None:
    verdicts = [{"coin": c, "verdict": "BEATS" if c == "BTC-USD" else "INCONCLUSIVE"}
                for c in CLUSTER_COINS]
    st = coin_sign_test(verdicts)
    assert st["n_beats"] == 1
    assert st["p_value"] == pytest.approx(0.9921875)
    assert st["verdict"] == "NO BEATS"


def test_sign_test_majority_but_not_significant_is_inconclusive() -> None:
    verdicts = [{"coin": c, "verdict": "BEATS" if c in ("BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD")
                 else "INCONCLUSIVE"} for c in CLUSTER_COINS]
    st = coin_sign_test(verdicts)
    assert st["n_beats"] == 4  # majority of 7 but p >= 0.05
    assert st["p_value"] >= 0.05
    assert st["verdict"] == "INCONCLUSIVE"


# --- fail-closed guards -----------------------------------------------------

def test_aggregate_missing_row_fails_closed() -> None:
    summary = _full_summary(lambda c, h, b: "BEATS")
    summary.pop(0)  # drop one (coin, horizon, baseline) row
    with pytest.raises(SystemExit, match="missing summary rows"):
        aggregate({"summary": summary})


def test_aggregate_seed_divergence_fails_closed() -> None:
    summary = _full_summary(lambda c, h, b: "BEATS")
    summary[3]["seeds_bit_identical"] = False
    with pytest.raises(SystemExit, match="bit-identical"):
        aggregate({"summary": summary})


def test_aggregate_all_beats_view_shapes() -> None:
    summary = _full_summary(lambda c, h, b: "BEATS")
    views = aggregate({"summary": summary})
    for view in VIEW_HORIZONS:
        for baseline in BASELINES:
            st = views[view][baseline]["sign_test"]
            assert st["verdict"] == "BEATS"
            assert len(st["coin_verdicts"]) == 7


# --- per-coin anchors -------------------------------------------------------

def test_anchors_deterministic_and_sensitive() -> None:
    summary = _full_summary(lambda c, h, b: "BEATS")
    a1 = per_coin_anchors(summary)
    a2 = per_coin_anchors(json.loads(json.dumps(summary)))
    assert a1 == a2  # canonical: key order must not matter
    summary[0]["edge_pct_mean"] = 99.0
    a3 = per_coin_anchors(summary)
    changed = {k for k in a1 if a1[k] != a3[k]}
    assert changed == {summary[0]["coin"]}
