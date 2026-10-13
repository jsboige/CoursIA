"""M18 TimesFM cluster aggregation — per-asset collapse + sign-test (#1454).

Consumes the full benchmark manifest produced by ``m18_tsfm_benchmark.py``
(seven assets, horizons {1, 5, 10, 22}) and derives the cluster verdict of
the #1454 revalidation family (M16/M12/M17/M4/M15):

1. fail-closed completeness — every (coin, horizon, baseline) summary row
   must be present, and every row must be seed-bit-identical (deterministic
   inference: seeds are controls, never observations — n_seeds_effective=1);
2. per-asset horizon collapse per baseline — BEATS on strict majority of
   horizons BEATS, NO BEATS as soon as one horizon is NO BEATS, otherwise
   INCONCLUSIVE (the M16 rule);
3. coin-level sign test — binomial exact, one-sided ``greater`` (M16/M12);
4. two views: ``cluster`` on {1, 5, 10} (comparable to M4/M15/M16/M17) and
   ``protocol`` on {1, 5, 22} (continuity of the #14768 claim).

Alignment honesty: unlike M4/M15, both DM legs are produced inside a single
walk-forward by the same harness, so there is no cross-harness origin join to
measure — the manifest records this explicitly instead of remaining silent.

Usage:
    python m18_tsfm_cluster.py --full-json <m18_tsfm_cluster_full.json> \
        --out-json scripts/results/m18_tsfm_cluster_aligned.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path

from scipy.stats import binomtest

RESULTS_DIR = Path(__file__).resolve().parent / "results"

CLUSTER_COINS = (
    "BTC-USD", "ETH-USD", "SOL-USD", "LTC-USD", "XRP-USD", "ADA-USD", "DOT-USD",
)
BASELINES = ("persistence", "ewma", "log_har", "har_rv")
VIEW_HORIZONS = {
    "cluster": (1, 5, 10),   # #1454 revalidation family convention
    "protocol": (1, 5, 22),  # #14768 original protocol continuity
}
ALPHA = 0.05


def _require(cond: bool, message: str) -> None:
    if not cond:
        raise SystemExit(f"[m18-cluster] FAIL-CLOSED: {message}")


def collapse_asset(rows: list[dict]) -> str:
    """M16 horizon-collapse rule for one (coin, baseline) slice."""
    n = len(rows)
    n_beats = sum(r["verdict"] == "BEATS" for r in rows)
    n_no = sum(r["verdict"] == "NO BEATS" for r in rows)
    if n_beats > n / 2:
        return "BEATS"
    if n_no >= 1:
        return "NO BEATS"
    return "INCONCLUSIVE"


def coin_sign_test(coin_verdicts: list[dict], alpha: float = ALPHA) -> dict:
    """Coin-level binomial exact sign test, one-sided greater (M16/M12)."""
    n_coins = len(coin_verdicts)
    n_beats = sum(v["verdict"] == "BEATS" for v in coin_verdicts)
    p_value = float(binomtest(n_beats, n_coins, p=0.5, alternative="greater").pvalue)
    if p_value < alpha:
        verdict = "BEATS"
    elif n_beats > n_coins / 2:
        verdict = "INCONCLUSIVE"
    else:
        verdict = "NO BEATS"
    return {
        "verdict": verdict,
        "alpha": alpha,
        "n_effective": n_coins,
        "n_beats": n_beats,
        "p_null": 0.5,
        "alternative": "greater",
        "p_value": p_value,
        "horizon_collapse": "BEATS when strict majority of horizons BEATS",
        "coin_verdicts": coin_verdicts,
    }


def aggregate(full: dict) -> dict:
    """Build every view/baseline aggregation from the benchmark manifest."""
    summary = full["summary"]
    by_key = {(r["coin"], r["horizon"], r["baseline"]): r for r in summary}

    expected = [
        (coin, h, b)
        for coin in CLUSTER_COINS
        for h in VIEW_HORIZONS["cluster"] + VIEW_HORIZONS["protocol"]
        for b in BASELINES
    ]
    missing = [k for k in expected if k not in by_key]
    _require(not missing, f"missing summary rows: {missing[:8]}")

    non_deterministic = [
        f"{r['coin']}/h={r['horizon']}/{r['baseline']}"
        for r in summary
        if not r.get("seeds_bit_identical", False)
    ]
    _require(
        not non_deterministic,
        "cluster verdict requires bit-identical seeds (deterministic "
        "inference, M17/M18 OLS precedent): " + ", ".join(non_deterministic[:8]),
    )

    views: dict[str, dict[str, dict]] = {}
    for view, horizons in VIEW_HORIZONS.items():
        per_baseline: dict[str, dict] = {}
        for baseline in BASELINES:
            coin_verdicts = []
            for coin in CLUSTER_COINS:
                rows = [by_key[(coin, h, baseline)] for h in horizons]
                coin_verdicts.append({
                    "coin": coin,
                    "verdict": collapse_asset(rows),
                    "horizons": {
                        str(h): {
                            "verdict": by_key[(coin, h, baseline)]["verdict"],
                            "edge_pct_mean": by_key[(coin, h, baseline)]["edge_pct_mean"],
                            "dm_p_median": by_key[(coin, h, baseline)]["dm_p_median"],
                        }
                        for h in horizons
                    },
                })
            per_baseline[baseline] = {
                "sign_test": coin_sign_test(coin_verdicts),
            }
        views[view] = per_baseline
    return views


def per_coin_anchors(summary: list[dict]) -> dict[str, str]:
    """SHA-256 of the canonical per-coin summary slice (M4 manifest parity)."""
    anchors: dict[str, str] = {}
    for coin in CLUSTER_COINS:
        rows = sorted(
            (r for r in summary if r["coin"] == coin),
            key=lambda r: (r["baseline"], r["horizon"]),
        )
        canon = json.dumps(rows, sort_keys=True).encode("utf-8")
        anchors[coin] = hashlib.sha256(canon).hexdigest()
    return anchors


def build_manifest(full: dict, full_json_path: Path) -> dict:
    views = aggregate(full)
    return {
        "module": "M18",
        "epic": 1454,
        "protocol": (
            "cluster revalidation of the zero-shot TimesFM 2.5 lead (#14768 "
            "protocol, PR #14778): seven-asset panel, per-asset horizon "
            "collapse (M16 rule) + coin-level binomial exact sign test, two "
            "views — cluster {1,5,10} (#1454 family) and protocol {1,5,22} "
            "(#14768 continuity). DM legs share one in-harness walk-forward: "
            "no cross-harness origin join exists to measure (unlike M4/M15); "
            "per-config n_oos and fold provenance live in the full artifact."
        ),
        "config": {
            "coins": list(CLUSTER_COINS),
            "view_horizons": {k: list(v) for k, v in VIEW_HORIZONS.items()},
            "seeds": sorted({c["seed"] for c in full["configs"]}),
            "n_seeds_effective": 1,
            "n_splits": full["n_splits"],
            "calibration_size": full["calibration_size"],
            "refit_every": full["refit_every"],
            "context_len": full["context_len"],
            "debias": full["debias"],
            "checkpoint_revision": full["checkpoint_revision"],
            "n_tsfm_series_served": full["n_tsfm_series_served"],
        },
        "seed_discipline": (
            "TimesFM 2.5 inference is deterministic: seeds {0,7,42,99} are "
            "bit-identical controls (seeds_bit_identical=true on every row), "
            "never independent observations"
        ),
        "alignment": (
            "single-harness legs: baselines and TimesFM forecasts are scored "
            "on the same fold indices by construction — no cross-harness "
            "origin join to measure (recorded instead of assumed)"
        ),
        "artifact": {
            "path": str(full_json_path),
            "bytes": full_json_path.stat().st_size,
            "sha256": hashlib.sha256(full_json_path.read_bytes()).hexdigest(),
        },
        "per_coin_sha256": per_coin_anchors(full["summary"]),
        "aggregated": views,
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="M18 TimesFM cluster aggregation (#1454 revalidation family)")
    parser.add_argument("--full-json", type=Path, required=True,
                        help="manifest written by m18_tsfm_benchmark.py (7 assets)")
    parser.add_argument("--out-json", type=Path,
                        default=RESULTS_DIR / "m18_tsfm_cluster_aligned.json")
    args = parser.parse_args()

    full = json.loads(args.full_json.read_text(encoding="utf-8"))
    manifest = build_manifest(full, args.full_json)

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(manifest, indent=1), encoding="utf-8")
    print(f"[m18-cluster] wrote {args.out_json}")

    for view, per_baseline in manifest["aggregated"].items():
        for baseline, blob in per_baseline.items():
            st = blob["sign_test"]
            print(f"  view={view} vs {baseline}: {st['verdict']} "
                  f"({st['n_beats']}/{st['n_effective']} coins BEATS, "
                  f"p={st['p_value']:.6f})")
            for cv in st["coin_verdicts"]:
                print(f"    {cv['coin']}: {cv['verdict']}")


if __name__ == "__main__":
    sys.exit(main())
