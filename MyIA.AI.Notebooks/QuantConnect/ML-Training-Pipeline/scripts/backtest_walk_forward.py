"""Stage 4: Walk-forward backtesting with portfolio simulation.

Consumes predictions from Stage 1-3 models (RF/XGBoost, LSTM, Transformer)
and evaluates them with production metrics: Sharpe, MaxDD, CAGR, HitRate.
Includes transaction costs (5bps equity, 10bps crypto) and multi-seed
validation (>=4 seeds, edge >= 2*std rule).

Usage:
    python backtest_walk_forward.py --predictions results/xgb_preds.npz \
        --asset-type spy --seeds 0,1,7,42 --n-folds 5

    python backtest_walk_forward.py --predictions results/lstm_preds.npz \
        --asset-type crypto --output results/stage4_lstm.json

    python backtest_walk_forward.py --multi-asset \
        --predictions SPY=results/spy_preds.npz BTC=results/btc_preds.npz \
        --asset-type spy,spy,crypto --seeds 0,1,7,42
"""

from __future__ import annotations

import argparse
import json
import logging
import sys
import time
from pathlib import Path

import numpy as np

from wf_framework.backtest import (
    WalkForwardBacktest,
    WalkForwardResult,
    default_classification_metrics,
    save_results,
)
from wf_framework.metrics import (
    PortfolioMetrics,
    aggregate_fold_metrics,
    compute_portfolio_metrics,
)
from wf_framework.portfolio import (
    COST_PRESETS,
    PortfolioResult,
    simulate_fold,
    simulate_walk_forward,
)
from wf_framework.stats import multi_asset_eval, multi_seed_eval

log = logging.getLogger(__name__)

SCRIPT_DIR = Path(__file__).resolve().parent


def load_predictions(path: str) -> dict:
    """Load predictions from .npz file.

    Expected keys: y_true, y_pred, optionally prices, returns.
    If seed-specific: y_true_seed{i}, y_pred_seed{i}.
    """
    data = np.load(path, allow_pickle=True)
    result = dict(data)
    log.info(f"Loaded {len(result)} arrays from {path}")
    return result


def load_predictions_multi_seed(
    path: str,
    seeds: list[int],
) -> dict[int, dict]:
    """Load multi-seed predictions from .npz file.

    Tries seed-specific keys first (y_true_seed0, y_pred_seed0),
    falls back to single (y_true, y_pred) duplicated for all seeds.
    """
    data = np.load(path, allow_pickle=True)

    results = {}
    for seed in seeds:
        y_true_key = f"y_true_seed{seed}"
        y_pred_key = f"y_pred_seed{seed}"

        if y_true_key in data and y_pred_key in data:
            results[seed] = {
                "y_true": data[y_true_key],
                "y_pred": data[y_pred_key],
            }
        elif "y_true" in data and "y_pred" in data:
            if seed == seeds[0] or seed not in results:
                results[seed] = {
                    "y_true": data["y_true"],
                    "y_pred": data["y_pred"],
                }
        else:
            log.warning(f"No predictions found for seed={seed} in {path}")

    if "prices" in data:
        for seed in results:
            results[seed]["prices"] = data["prices"]
    if "returns" in data:
        for seed in results:
            results[seed]["returns"] = data["returns"]

    return results


def run_portfolio_backtest(
    y_true: np.ndarray,
    y_pred: np.ndarray,
    prices: np.ndarray | None = None,
    returns: np.ndarray | None = None,
    cost_model: str = "spy",
    n_folds: int = 5,
    gap: int = 0,
) -> dict:
    """Run walk-forward portfolio backtest on a single seed's predictions.

    Splits predictions into walk-forward folds, simulates portfolio for each,
    and aggregates production metrics across folds.
    """
    n = len(y_true)
    fold_size = n // n_folds
    if fold_size < 2:
        log.warning(f"Too few samples ({n}) for {n_folds} folds")
        fold_size = max(n, 1)
        n_folds = 1

    fold_results = []
    all_gross = []
    all_net = []

    for i in range(n_folds):
        start = i * fold_size
        end = start + fold_size if i < n_folds - 1 else n

        if end - start < 2:
            continue

        y_t = y_true[start:end]
        y_p = y_pred[start:end]

        p = prices[start:end] if prices is not None else None
        r = returns[start:end] if returns is not None else None

        result = simulate_fold(
            y_t, y_p,
            prices=p, returns=r,
            cost_model=cost_model,
        )
        fold_results.append(result)
        all_gross.append(result.gross_returns)
        all_net.append(result.net_returns)

    if not fold_results:
        return {"error": "no valid folds"}

    # Concatenate across folds
    gross_returns = np.concatenate(all_gross)
    net_returns = np.concatenate(all_net)

    # Build equity curve from net returns
    equity = np.zeros(len(net_returns) + 1)
    equity[0] = 100_000.0
    for t in range(len(net_returns)):
        equity[t + 1] = equity[t] * (1 + net_returns[t])

    metrics = compute_portfolio_metrics(
        net_returns=net_returns,
        equity_curve=equity,
        gross_returns=gross_returns,
    )

    # Per-fold metrics
    fold_metrics = []
    for fr in fold_results:
        fm = compute_portfolio_metrics(
            net_returns=fr.net_returns,
            equity_curve=fr.equity_curve,
            gross_returns=fr.gross_returns,
        )
        fold_metrics.append(fm)

    aggregated = aggregate_fold_metrics(fold_metrics)

    # Classification accuracy
    dir_acc = float(np.mean(y_true == y_pred))

    return {
        "portfolio_metrics": metrics.to_dict(),
        "fold_aggregation": aggregated,
        "dir_acc": round(dir_acc, 4),
        "n_folds": len(fold_results),
        "total_n_trades": sum(fr.n_trades for fr in fold_results),
        "fold_details": [fr.to_dict() for fr in fold_results],
    }


def run_single_asset(
    pred_path: str,
    seeds: list[int],
    asset_type: str = "spy",
    n_folds: int = 5,
    gap: int = 0,
) -> dict:
    """Run multi-seed walk-forward backtest for a single asset."""
    log.info(f"Loading predictions from {pred_path}")
    seed_preds = load_predictions_multi_seed(pred_path, seeds)

    if not seed_preds:
        return {"error": f"no predictions loaded from {pred_path}"}

    results = {}
    for seed, data in seed_preds.items():
        log.info(f"  Seed {seed}: {len(data['y_true'])} samples")
        results[str(seed)] = run_portfolio_backtest(
            y_true=data["y_true"],
            y_pred=data["y_pred"],
            prices=data.get("prices"),
            returns=data.get("returns"),
            cost_model=asset_type,
            n_folds=n_folds,
            gap=gap,
        )

    # Multi-seed statistical evaluation on Sharpe
    seed_sharpes = []
    seed_metrics_list = []
    for seed_str, res in results.items():
        if "portfolio_metrics" in res:
            seed_sharpes.append({
                "sharpe": res["portfolio_metrics"]["sharpe"],
                "dir_acc": res["dir_acc"],
            })
            seed_metrics_list.append(res["portfolio_metrics"])

    stat_result = None
    if len(seed_sharpes) >= 4:
        stat_result = multi_seed_eval(
            seed_sharpes,
            baseline_value=0.0,
            metric="sharpe",
            alpha=0.05,
        ).to_dict()

    return {
        "asset_type": asset_type,
        "seeds": seeds,
        "n_folds": n_folds,
        "per_seed": results,
        "multi_seed_stats": stat_result,
    }


def run_multi_asset(
    asset_specs: list[tuple[str, str]],
    seeds: list[int],
    asset_types: list[str] | None = None,
    n_folds: int = 5,
    gap: int = 0,
) -> dict:
    """Run walk-forward backtest across multiple assets with Bonferroni correction.

    Parameters
    ----------
    asset_specs : list of (symbol, pred_path) tuples.
    seeds : list of random seeds.
    asset_types : list of asset type strings per asset.
    n_folds : walk-forward folds.
    gap : gap between train/test.
    """
    per_asset = {}
    asset_sharpes = {}

    for i, (symbol, pred_path) in enumerate(asset_specs):
        atype = asset_types[i] if asset_types and i < len(asset_types) else "spy"
        log.info(f"Multi-asset: {symbol} ({atype})")

        result = run_single_asset(
            pred_path=pred_path,
            seeds=seeds,
            asset_type=atype,
            n_folds=n_folds,
            gap=gap,
        )
        per_asset[symbol] = result

        # Collect per-seed Sharpe for multi-asset eval
        if "per_seed" in result:
            seed_sharpes = []
            for seed_str, seed_res in result["per_seed"].items():
                if "portfolio_metrics" in seed_res:
                    seed_sharpes.append({
                        "sharpe": seed_res["portfolio_metrics"]["sharpe"],
                        "dir_acc": seed_res["dir_acc"],
                    })
            if seed_sharpes:
                asset_sharpes[symbol] = seed_sharpes

    bonf_result = None
    if len(asset_sharpes) >= 2:
        bonf_result = multi_asset_eval(
            asset_sharpes,
            baseline_value=0.0,
            metric="sharpe",
            alpha=0.05,
        ).to_dict()

    return {
        "n_assets": len(asset_specs),
        "seeds": seeds,
        "per_asset": per_asset,
        "bonferroni": bonf_result,
    }


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Stage 4: Walk-forward portfolio backtesting",
    )
    parser.add_argument(
        "--predictions", type=str,
        help="Path to .npz predictions file (y_true, y_pred arrays)",
    )
    parser.add_argument(
        "--multi-asset", action="store_true",
        help="Multi-asset mode. Use --predictions SYM=path.npz SYM2=path2.npz",
    )
    parser.add_argument(
        "--asset-type", type=str, default="spy",
        help="Asset type for cost model: spy, crypto, default. "
             "For multi-asset: comma-separated (spy,crypto,spy)",
    )
    parser.add_argument(
        "--seeds", type=str, default="0,1,7,42",
        help="Comma-separated random seeds (default: 0,1,7,42)",
    )
    parser.add_argument(
        "--n-folds", type=int, default=5,
        help="Number of walk-forward folds (default: 5)",
    )
    parser.add_argument(
        "--gap", type=int, default=0,
        help="Gap between train/test periods (default: 0)",
    )
    parser.add_argument(
        "--output", "-o", type=str, default=None,
        help="Output JSON path (default: auto-generated)",
    )
    parser.add_argument(
        "--verbose", "-v", action="store_true",
        help="Enable verbose logging",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s: %(message)s",
    )

    seeds = [int(s.strip()) for s in args.seeds.split(",")]
    if len(seeds) < 4:
        log.warning(f"Only {len(seeds)} seeds provided. Project rule requires >= 4.")

    t0 = time.time()

    if args.multi_asset:
        # Parse "SYM=path" pairs from remaining args or --predictions
        if not args.predictions:
            log.error("--multi-asset requires --predictions with SYM=path pairs")
            return 1

        # Parse asset specs
        specs = []
        asset_types = None
        for part in args.predictions.split():
            if "=" in part:
                sym, path = part.split("=", 1)
                specs.append((sym.strip(), path.strip()))

        if args.asset_type and "," in args.asset_type:
            asset_types = [a.strip() for a in args.asset_type.split(",")]
        elif args.asset_type:
            asset_types = [args.asset_type] * len(specs)

        result = run_multi_asset(
            asset_specs=specs,
            seeds=seeds,
            asset_types=asset_types,
            n_folds=args.n_folds,
            gap=args.gap,
        )
    elif args.predictions:
        result = run_single_asset(
            pred_path=args.predictions,
            seeds=seeds,
            asset_type=args.asset_type,
            n_folds=args.n_folds,
            gap=args.gap,
        )
    else:
        log.error("Provide --predictions or --multi-asset with prediction paths")
        return 1

    elapsed = time.time() - t0
    result["elapsed_s"] = round(elapsed, 2)

    # Output
    output_path = args.output
    if output_path is None:
        stem = Path(args.predictions).stem if args.predictions else "stage4"
        output_path = str(SCRIPT_DIR / "results" / f"{stem}_walkforward.json")

    out = Path(output_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, default=str), encoding="utf-8")
    log.info(f"Results saved to {out}")

    # Print summary
    print(f"\n{'='*60}")
    print(f"Stage 4 Walk-Forward Results ({elapsed:.1f}s)")
    print(f"{'='*60}")

    if "per_seed" in result:
        for seed_str, seed_res in result["per_seed"].items():
            if "portfolio_metrics" in seed_res:
                pm = seed_res["portfolio_metrics"]
                print(f"  Seed {seed_str}: Sharpe={pm['sharpe']:.3f} "
                      f"MaxDD={pm['max_drawdown']:.2%} "
                      f"CAGR={pm['cagr']:.2%} "
                      f"HitRate={pm['hit_rate']:.2%} "
                      f"Trades={seed_res['total_n_trades']}")
        if result.get("multi_seed_stats"):
            ms = result["multi_seed_stats"]
            print(f"  Multi-seed: mean_Sharpe={ms['mean']:.3f} "
                  f"std={ms['std']:.3f} "
                  f"passes_rule={ms['passes_rule']}")

    if "bonferroni" in result and result["bonferroni"]:
        b = result["bonferroni"]
        print(f"  Bonferroni: {b['n_significant_bonferroni']}/{b['n_assets']} "
              f"assets significant (alpha_bonf={b['alpha_bonferroni']:.4f})")

    print(f"{'='*60}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
