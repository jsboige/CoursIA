"""
Run Stage -1 panier baselines POST-FIX for all 26 symbols (RF + XGBoost).

Uses walk-forward validation with train-only normalization (POST-FIX methodology).
Outputs checkpoints with metadata for each symbol/model combination.

Usage:
    python run_panier_baselines.py
    python run_panier_baselines.py --dry-run
    python run_panier_baselines.py --symbols SPY GLD TLT
    python run_panier_baselines.py --model rf
"""

import argparse
import json
import sys
import time
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
PANIER_DIR = SCRIPTS_DIR.parent.parent / "datasets" / "panier"
CHECKPOINTS_DIR = SCRIPTS_DIR.parent / "checkpoints"

sys.path.insert(0, str(SCRIPTS_DIR))

from panier_loader import PANIER_GROUPS, get_panier_symbols


def run_single_baseline(
    symbol: str,
    model_type: str,
    dry_run: bool = False,
) -> dict:
    """Run a single baseline training for a symbol."""
    import subprocess

    cmd = [
        sys.executable,
        str(SCRIPTS_DIR / "train_classification.py"),
        "--data-dir", str(PANIER_DIR),
        "--symbol", symbol,
        "--model", model_type,
        "--walk-forward",
        "--n-splits", "5",
        "--gap", "5",
        "--advanced",
        "--n-estimators", "200",
        "--max-depth", "8",
        "--lookback", "20",
        "--checkpoint-dir", str(CHECKPOINTS_DIR / "panier_baselines" / symbol.replace("-", "_") / model_type),
    ]

    if dry_run:
        return {"symbol": symbol, "model": model_type, "status": "DRY_RUN"}

    start = time.time()
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=600,
        cwd=str(SCRIPTS_DIR),
    )
    elapsed = time.time() - start

    return {
        "symbol": symbol,
        "model": model_type,
        "returncode": result.returncode,
        "elapsed": round(elapsed, 1),
        "success": result.returncode == 0,
        "stdout_last": result.stdout.strip().split("\n")[-3:] if result.stdout else [],
        "stderr_last": result.stderr.strip().split("\n")[-3:] if result.stderr else [],
    }


def collect_results() -> list[dict]:
    """Scan checkpoint directories and collect all baseline results."""
    results = []
    baselines_dir = CHECKPOINTS_DIR / "panier_baselines"
    if not baselines_dir.exists():
        return results

    for symbol_dir in sorted(baselines_dir.iterdir()):
        if not symbol_dir.is_dir():
            continue
        for model_dir in sorted(symbol_dir.iterdir()):
            if not model_dir.is_dir():
                continue
            for ckpt_dir in sorted(model_dir.iterdir()):
                if not ckpt_dir.is_dir():
                    continue
                meta_file = ckpt_dir / "metadata.json"
                if not meta_file.exists():
                    continue
                try:
                    meta = json.loads(meta_file.read_text(encoding="utf-8"))
                except json.JSONDecodeError:
                    continue

                metrics = meta.get("metrics", {})
                hp = meta.get("hyperparams", {})
                results.append({
                    "symbol": hp.get("symbol", symbol_dir.name),
                    "model": model_dir.name,
                    "group": _get_group(hp.get("symbol", symbol_dir.name)),
                    "oos_diracc": metrics.get("oos_direction_accuracy"),
                    "majority_acc": metrics.get("majority_class_acc"),
                    "majority_freq": metrics.get("majority_class_freq"),
                    "vs_majority": metrics.get("vs_majority_class"),
                    "n_folds": metrics.get("n_wf_folds"),
                    "timestamp": meta.get("timestamp", ckpt_dir.name),
                    "checkpoint": str(ckpt_dir.relative_to(CHECKPOINTS_DIR)),
                })
    return results


def _get_group(symbol: str) -> str:
    """Get asset class group for a symbol."""
    for group_name, symbols in PANIER_GROUPS.items():
        if symbol in symbols:
            return group_name
    return "unknown"


def print_summary(results: list[dict]):
    """Print POST-FIX verdict summary."""
    print("\n" + "=" * 80)
    print("PANIER BASELINES POST-FIX SUMMARY")
    print("=" * 80)

    by_group = {}
    for r in results:
        grp = r["group"]
        by_group.setdefault(grp, []).append(r)

    total = len(results)
    beats = sum(1 for r in results if r.get("vs_majority", 0) > 0)
    fails = total - beats

    for grp in sorted(by_group.keys()):
        print(f"\n  [{grp}]")
        for r in sorted(by_group[grp], key=lambda x: x["symbol"]):
            vs = r.get("vs_majority", 0)
            verdict = "BEATS" if vs > 0 else "FAIL"
            diracc = r.get("oos_diracc", 0)
            maj = r.get("majority_acc", 0)
            print(f"    {r['symbol']:8s} {r['model']:3s}  DirAcc={diracc:.4f}  Maj={maj:.4f}  vs_Maj={vs:+.4f}  [{verdict}]")

    print(f"\n{'='*80}")
    print(f"TOTAL: {total} experiments | BEATS: {beats} | FAILS: {fails}")
    print(f"{'='*80}")


def main():
    parser = argparse.ArgumentParser(description="Run panier baselines POST-FIX")
    parser.add_argument("--dry-run", action="store_true", help="Validate pipeline only")
    parser.add_argument("--symbols", nargs="+", help="Specific symbols to run")
    parser.add_argument("--model", choices=["rf", "xgb", "both"], default="both", help="Model type")
    parser.add_argument("--summary-only", action="store_true", help="Just print existing results")
    args = parser.parse_args()

    if args.summary_only:
        results = collect_results()
        print_summary(results)
        return

    symbols = args.symbols or get_panier_symbols()
    models = ["rf", "xgb"] if args.model == "both" else [args.model]
    total_runs = len(symbols) * len(models)

    print(f"Panier baselines: {len(symbols)} symbols x {len(models)} models = {total_runs} runs")
    print(f"POST-FIX: seed=42, walk-forward 5-fold, gap=5, advanced features")
    print()

    completed = 0
    failed = 0
    for symbol in symbols:
        for model_type in models:
            completed += 1
            print(f"[{completed}/{total_runs}] {symbol} ({model_type})...", end=" ", flush=True)

            result = run_single_baseline(symbol, model_type, dry_run=args.dry_run)

            if result["success"]:
                print(f"OK ({result['elapsed']}s)")
            else:
                failed += 1
                print(f"FAIL")
                if result.get("stderr_last"):
                    for line in result["stderr_last"]:
                        print(f"    {line}")

    print(f"\nCompleted: {completed - failed}/{total_runs} successful")

    if not args.dry_run:
        results = collect_results()
        print_summary(results)

        summary_path = CHECKPOINTS_DIR / "panier_baselines_summary.json"
        summary_path.parent.mkdir(parents=True, exist_ok=True)
        summary_path.write_text(json.dumps(results, indent=2), encoding="utf-8")
        print(f"\nSummary saved: {summary_path}")


if __name__ == "__main__":
    main()
