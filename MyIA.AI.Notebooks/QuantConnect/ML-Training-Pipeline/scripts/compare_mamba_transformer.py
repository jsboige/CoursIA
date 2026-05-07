"""Mamba vs Transformer comparison for SPY hourly forecasting.

Stage 5 research script: runs both models via their CLIs (subprocess),
then parses their metadata.json outputs for a side-by-side comparison.

Each model has its own data pipeline (Mamba = multi-step pred_len,
Transformer = single-step), so we run them independently and compare
metrics at the output level.

Usage:
    python compare_mamba_transformer.py --dry-run
    python compare_mamba_transformer.py --data-dir ../datasets/yfinance --symbol SPY
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent


def run_model_cli(
    script_name: str,
    extra_args: list[str],
    output_dir: Path,
    timeout: int = 600,
) -> dict:
    """Run a training script via subprocess and return parsed metadata.

    Parameters
    ----------
    script_name : str
        Script filename (e.g., "train_mamba.py").
    extra_args : list[str]
        Additional CLI arguments.
    output_dir : Path
        Directory where the script saves checkpoints.
    timeout : int
        Subprocess timeout in seconds.

    Returns
    -------
    dict with "metrics", "elapsed_s", "returncode".
    """
    cmd = [sys.executable, str(SCRIPTS_DIR / script_name)] + extra_args
    print(f"\n  Running: {' '.join(cmd[:4])}...")

    t0 = time.time()
    proc = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=timeout,
        cwd=str(SCRIPTS_DIR),
    )
    elapsed = time.time() - t0

    if proc.returncode != 0:
        print(f"  ERROR ({script_name}): exit code {proc.returncode}")
        print(f"  stderr: {proc.stderr[-500:]}" if proc.stderr else "  (no stderr)")
        return {"error": proc.stderr[-1000:] if proc.stderr else "unknown", "elapsed_s": elapsed, "returncode": proc.returncode}

    # Find the latest metadata.json in output_dir
    metadata_files = sorted(output_dir.rglob("metadata.json"), key=lambda p: p.stat().st_mtime)
    if not metadata_files:
        print(f"  WARNING: No metadata.json found in {output_dir}")
        return {"error": "no metadata.json", "elapsed_s": elapsed, "returncode": 0}

    metadata = json.loads(metadata_files[-1].read_text(encoding="utf-8"))
    return {
        "metrics": metadata.get("metrics", {}),
        "hyperparams": metadata.get("hyperparams", {}),
        "elapsed_s": round(elapsed, 1),
        "returncode": 0,
    }


def print_comparison(results: dict) -> None:
    """Print side-by-side comparison table."""
    m = results.get("mamba", {})
    t = results.get("transformer", {})

    m_metrics = m.get("metrics", {})
    t_metrics = t.get("metrics", {})

    m_err = "error" in m
    t_err = "error" in t

    print(f"\n{'='*70}")
    print(f"{'Mamba vs Transformer Comparison':^70}")
    print(f"{'='*70}")
    print(f"{'Metric':<35} {'Mamba':>15} {'Transformer':>15}")
    print(f"{'-'*70}")

    rows = []

    if m_err:
        rows.append(("Status", "ERROR", "OK" if not t_err else "ERROR"))
    if t_err:
        rows.append(("Status", "OK" if not m_err else "ERROR", "ERROR"))

    rows.append(("Training time (s)",
                  f"{m.get('elapsed_s', 0):.1f}",
                  f"{t.get('elapsed_s', 0):.1f}"))

    rows.append(("Total params",
                  f"{m_metrics.get('total_params', 0):,}",
                  f"{t_metrics.get('total_params', 0):,}"))

    # MSE
    m_mse = m_metrics.get("mse")
    t_mse = t_metrics.get("mse")
    if m_mse is not None and t_mse is not None:
        rows.append(("MSE", f"{m_mse:.6f}", f"{t_mse:.6f}"))

    # MAE
    m_mae = m_metrics.get("mae")
    t_mae = t_metrics.get("mae")
    if m_mae is not None and t_mae is not None:
        rows.append(("MAE", f"{m_mae:.6f}", f"{t_mae:.6f}"))

    # Direction accuracy
    m_da = m_metrics.get("direction_accuracy_step1", m_metrics.get("direction_accuracy"))
    t_da = t_metrics.get("direction_accuracy", t_metrics.get("oos_direction_accuracy"))
    if m_da is not None and t_da is not None:
        rows.append(("DirAcc", f"{m_da:.4f}", f"{t_da:.4f}"))

    # Majority baseline comparison
    m_bl = m_metrics.get("majority_class_baseline", m_metrics.get("majority_class_acc"))
    t_bl = t_metrics.get("majority_class_acc", t_metrics.get("majority_class_baseline", {}).get("majority_class_accuracy"))
    if m_bl is not None:
        if isinstance(m_bl, dict):
            rows.append(("Majority baseline", f"{m_bl.get('majority_class_accuracy', 0):.4f}", "-"))
        else:
            rows.append(("Majority baseline", f"{m_bl:.4f}", f"{t_bl:.4f}" if t_bl is not None else "-"))
    if t_bl is not None and not isinstance(t_bl, dict):
        if m_bl is None or isinstance(m_bl, dict):
            rows.append(("Majority baseline", "-", f"{t_bl:.4f}"))

    # Edge over majority
    m_edge = m_metrics.get("edge_over_majority", m_metrics.get("vs_majority_class"))
    t_edge = t_metrics.get("vs_majority_class")
    if m_edge is not None:
        rows.append(("Edge over majority", f"{m_edge:+.4f}", "-"))
    if t_edge is not None:
        rows.append(("Edge over majority", "-", f"{t_edge:+.4f}") if m_edge is None else None)
    rows = [r for r in rows if r is not None]

    for label, m_val, t_val in rows:
        print(f"{label:<35} {str(m_val):>15} {str(t_val):>15}")

    print(f"{'='*70}\n")

    # Verdict (only if both succeeded)
    if not m_err and not t_err:
        m_mse_val = m_metrics.get("mse", float("inf"))
        t_mse_val = t_metrics.get("mse", float("inf"))
        winner = "Mamba" if m_mse_val < t_mse_val else "Transformer"
        speedup = t.get("elapsed_s", 1) / max(m.get("elapsed_s", 0.1), 0.1)
        print(f"MSE winner: {winner}")
        print(f"Training speed: Mamba is {speedup:.1f}x {'faster' if speedup > 1 else 'slower'}")


def main():
    parser = argparse.ArgumentParser(description="Mamba vs Transformer comparison")
    parser.add_argument("--data-dir", default=str(
        Path(__file__).resolve().parent.parent / "datasets" / "yfinance"))
    parser.add_argument("--symbol", default="SPY")
    parser.add_argument("--epochs", type=int, default=50)
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--output", type=str, default=None,
                        help="Save comparison JSON to this path")
    parser.add_argument("--timeout", type=int, default=600,
                        help="Per-model subprocess timeout (seconds)")
    args = parser.parse_args()

    base_args = [
        "--data-dir", args.data_dir,
        "--symbol", args.symbol,
        "--epochs", str(args.epochs if not args.dry_run else 2),
        "--batch-size", str(args.batch_size),
    ]
    if args.dry_run:
        base_args.append("--dry-run")

    results = {}

    with tempfile.TemporaryDirectory(prefix="mamba_vs_tf_") as tmpdir:
        tmp = Path(tmpdir)

        # --- Mamba ---
        print("=" * 50)
        print("Phase 1/2: Training Mamba SSM")
        print("=" * 50)
        mamba_output = tmp / "mamba"
        mamba_args = base_args + [
            "--seed", str(args.seed),
            "--output-dir", str(mamba_output),
        ]
        results["mamba"] = run_model_cli(
            "train_mamba.py", mamba_args, mamba_output, timeout=args.timeout,
        )

        # --- Transformer ---
        print("=" * 50)
        print("Phase 2/2: Training Transformer")
        print("=" * 50)
        tf_output = tmp / "transformer"
        tf_args = base_args + ["--checkpoint-dir", str(tf_output)]
        results["transformer"] = run_model_cli(
            "train_transformer.py", tf_args, tf_output, timeout=args.timeout,
        )

    print_comparison(results)

    if args.output:
        Path(args.output).write_text(
            json.dumps(results, indent=2, default=str), encoding="utf-8",
        )
        print(f"Saved to {args.output}")


if __name__ == "__main__":
    main()
