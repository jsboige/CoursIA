"""
DM Test Retroactif -- Cycle 28 Track A
Re-classify all raw BEATS claims across M3/M3b/M4/M5/M9 using strict p-value thresholds.

Methodology:
- Per-combo: DM p-value < 0.05 => BEATS_p005, < 0.10 => BEATS_p010, else INCONCLUSIVE
- Cross-seed sign-test: binomial test on N_beats/N_seeds
- Aggregation by model and overall

Usage:
    python scripts/dm_test_retroactif.py
"""

import json
import os
import sys
from pathlib import Path
from collections import defaultdict
from scipy import stats

BASE = Path(__file__).resolve().parent
RESULTS = BASE / "results"
OUTPUTS = BASE.parent / "outputs"


def load_json(path):
    with open(path) as f:
        return json.load(f)


def extract_m3_classic():
    """M3 HAR classic vs GARCH/naive baselines."""
    data = load_json(RESULTS / "m3_har_extended.json")
    rows = []
    for r in data["rows"]:
        rows.append({
            "model": "M3_HAR_classic",
            "coin": r["coin"],
            "horizon": r["horizon"],
            "seed": "pooled",
            "dm_stat": r["dm_stat"],
            "dm_pvalue": r["dm_pvalue"],
            "mse_model": r["har_mse_logrv"],
            "mse_baseline": r.get("garch_rolling_mse_logrv", r.get("naive_30d_mse_logrv")),
            "n_predictions": r["n_predictions"],
            "baseline_type": "GARCH_rolling",
        })
    return rows


def extract_m3b_asymmetric():
    """M3b HAR asymmetric vs HAR classic."""
    data = load_json(RESULTS / "m3_har_asymmetric.json")
    rows = []
    for r in data["rows"]:
        if r.get("seed") == "aggregate":
            continue
        rows.append({
            "model": "M3b_HAR_asymmetric",
            "coin": r["coin"],
            "horizon": r["horizon"],
            "seed": r["seed"],
            "dm_stat": r["dm_stat"],
            "dm_pvalue": r["dm_pvalue"],
            "mse_model": r["asym_mse_logrv"],
            "mse_baseline": r["classic_mse_logrv"],
            "n_predictions": r["n_predictions"],
            "baseline_type": "HAR_classic",
        })
    return rows


def extract_m4_dlinear():
    """M4 DLinear vs HAR classic."""
    data = load_json(RESULTS / "m4_dlinear_vol_full.json")
    rows = []
    for r in data["rows"]:
        rows.append({
            "model": "M4_DLinear",
            "coin": r["coin"],
            "horizon": r["horizon"],
            "seed": r["seed"],
            "dm_stat": r["dm_stat"],
            "dm_pvalue": r["dm_pvalue"],
            "mse_model": r["dlinear_mse_logrv"],
            "mse_baseline": r["har_mse_logrv"],
            "n_predictions": r["n_predictions"],
            "baseline_type": "HAR_classic",
        })
    return rows


def extract_m5_hmm():
    """M5 HMM regime-switching vs HAR classic."""
    data = load_json(RESULTS / "m5_hmm_regime.json")
    rows = []
    for r in data["results"]:
        if r.get("seed") == "aggregate":
            continue
        rows.append({
            "model": "M5_HMM_regime",
            "coin": r["coin"],
            "horizon": r["horizon"],
            "seed": r["seed"],
            "dm_stat": r["dm_statistic"],
            "dm_pvalue": r["dm_p_value"],
            "mse_model": r["regime_mse"],
            "mse_baseline": r["classic_mse"],
            "n_predictions": r["n_preds"],
            "baseline_type": "HAR_classic",
        })
    return rows


def extract_m9_tft():
    """M9 TFT vs majority-class baseline (direction accuracy edge)."""
    tft_dirs = sorted(OUTPUTS.glob("tft_m9_*/results.json"))
    rows = []
    for d in tft_dirs:
        data = load_json(d)
        config_name = d.parent.name  # e.g. tft_m9_btc_h1
        # Skip non-standard dirs (e.g. tft_m9_test)
        if config_name == "tft_m9_test" or "tft_m9_run" in config_name:
            continue
        # Extract coin and horizon from hyperparams if available
        hp = data.get("hyperparams", {})
        symbols = hp.get("symbols", [])
        coin = symbols[0] if symbols else "BTC-USD"
        horizon = hp.get("pred_len", 1)

        for run in data["per_run"]:
            edge = run["edge_over_majority"]
            n_test = run["n_test"]
            majority_acc = run["majority_class_baseline"]["majority_class_accuracy"]

            # For direction accuracy, we compute a binomial test
            # H0: p = majority_acc (model is random)
            # H1: p > majority_acc (model beats baseline)
            dir_acc = run["direction_accuracy_step1"]
            n_correct = int(dir_acc * n_test)
            binom_pvalue = stats.binomtest(n_correct, n_test, majority_acc, alternative="greater").pvalue

            rows.append({
                "model": "M9_TFT",
                "coin": coin,
                "horizon": horizon,
                "seed": run["seed"],
                "fold": run["fold_idx"],
                "dm_stat": edge,
                "dm_pvalue": binom_pvalue,
                "mse_model": run["mse"],
                "mse_baseline": None,
                "n_predictions": n_test,
                "baseline_type": "majority_class",
                "edge": edge,
                "dir_acc": dir_acc,
            })
    return rows


def classify_combo(rows_for_combo):
    """Classify a single (model, coin, horizon) combo across seeds/folds."""
    # Separate rows by direction: model beats baseline vs baseline beats model
    beats_pvalues = []
    beaten_pvalues = []
    for r in rows_for_combo:
        if r["dm_pvalue"] is None:
            continue
        model = r["model"]
        dm_stat = r["dm_stat"]
        # For MSE-based tests: dm_stat < 0 means model has lower MSE (beats)
        # For M9: edge > 0 means model beats majority
        if model == "M9_TFT":
            is_beat = r.get("edge", 0) > 0
        else:
            is_beat = dm_stat < 0

        if is_beat:
            beats_pvalues.append(r["dm_pvalue"])
        else:
            beaten_pvalues.append(r["dm_pvalue"])

    all_pvalues = [r["dm_pvalue"] for r in rows_for_combo if r["dm_pvalue"] is not None]
    if not all_pvalues:
        return "INCONCLUSIVE", None, len(rows_for_combo)

    mean_p = sum(all_pvalues) / len(all_pvalues)

    # Check if model predominantly BEATEN by baseline
    n_beaten = len(beaten_pvalues)
    n_beats = len(beats_pvalues)
    n_total = n_beats + n_beaten

    # If more seeds show BEATEN than BEATS, classify as BEATEN
    if n_beaten > n_beats:
        beaten_mean_p = sum(beaten_pvalues) / len(beaten_pvalues) if beaten_pvalues else 1.0
        if beaten_mean_p < 0.05:
            return "BEATEN_p005", mean_p, len(rows_for_combo)
        elif beaten_mean_p < 0.10:
            return "BEATEN_p010", mean_p, len(rows_for_combo)
        else:
            return "INCONCLUSIVE", mean_p, len(rows_for_combo)

    # Model predominantly beats baseline
    beats_mean_p = sum(beats_pvalues) / len(beats_pvalues) if beats_pvalues else 1.0
    if beats_mean_p < 0.05:
        verdict = "BEATS_p005"
    elif beats_mean_p < 0.10:
        verdict = "BEATS_p010"
    else:
        verdict = "INCONCLUSIVE"

    return verdict, mean_p, len(rows_for_combo)


def sign_test_across_seeds(rows_for_combo):
    """Binomial sign-test: count how many seeds beat baseline."""
    # For DM-style tests: negative dm_stat => model beats baseline
    # For M9: positive edge => model beats baseline
    n_beats = 0
    n_total = 0
    for r in rows_for_combo:
        model = r["model"]
        dm_stat = r["dm_stat"]
        if model == "M9_TFT":
            beats = r.get("edge", 0) > 0
        else:
            beats = dm_stat < 0 and r["dm_pvalue"] < 0.05
        if beats:
            n_beats += 1
        n_total += 1

    if n_total == 0:
        return None, n_beats, n_total

    # Binomial test: H0: p=0.5 (random), H1: p>0.5 (model wins more than chance)
    binom_p = stats.binomtest(n_beats, n_total, 0.5, alternative="greater").pvalue
    return binom_p, n_beats, n_total


def main():
    print("=" * 80)
    print("DM TEST RETROACTIF -- Cycle 28 Track A")
    print("Re-classification: BEATS p<0.05 / BEATS p<0.10 / INCONCLUSIVE")
    print("=" * 80)

    all_rows = []
    all_rows.extend(extract_m3_classic())
    all_rows.extend(extract_m3b_asymmetric())
    all_rows.extend(extract_m4_dlinear())
    all_rows.extend(extract_m5_hmm())
    all_rows.extend(extract_m9_tft())

    print(f"\nTotal raw rows loaded: {len(all_rows)}")

    # Group by (model, coin, horizon)
    combos = defaultdict(list)
    for r in all_rows:
        key = (r["model"], r["coin"], r["horizon"])
        combos[key].append(r)

    print(f"Unique combos: {len(combos)}")

    # Re-classify each combo
    results = []
    model_summary = defaultdict(lambda: {
        "p005": 0, "p010": 0, "beaten_p005": 0, "beaten_p010": 0, "inconclusive": 0, "total": 0
    })

    for (model, coin, horizon), rows in sorted(combos.items()):
        verdict, mean_p, n_runs = classify_combo(rows)
        sign_p, n_beats, n_seeds = sign_test_across_seeds(rows)

        mse_model = [r["mse_model"] for r in rows if r["mse_model"] is not None]
        mse_baseline = [r["mse_baseline"] for r in rows if r["mse_baseline"] is not None]
        mean_mse_model = sum(mse_model) / len(mse_model) if mse_model else None
        mean_mse_baseline = sum(mse_baseline) / len(mse_baseline) if mse_baseline else None
        mse_reduction_pct = (
            (1 - mean_mse_model / mean_mse_baseline) * 100
            if mean_mse_model and mean_mse_baseline and mean_mse_baseline > 0
            else None
        )

        result = {
            "model": model,
            "coin": coin,
            "horizon": horizon,
            "n_runs": n_runs,
            "n_beats_seeds": n_beats,
            "n_total_seeds": n_seeds,
            "mean_dm_pvalue": round(mean_p, 6) if mean_p is not None else None,
            "sign_test_pvalue": round(sign_p, 6) if sign_p is not None else None,
            "mean_mse_model": round(mean_mse_model, 6) if mean_mse_model else None,
            "mean_mse_baseline": round(mean_mse_baseline, 6) if mean_mse_baseline else None,
            "mse_reduction_pct": round(mse_reduction_pct, 2) if mse_reduction_pct is not None else None,
            "verdict_strict": verdict,
        }
        results.append(result)

        model_summary[model]["total"] += 1
        if verdict == "BEATS_p005":
            model_summary[model]["p005"] += 1
        elif verdict == "BEATS_p010":
            model_summary[model]["p010"] += 1
        elif verdict == "BEATEN_p005":
            model_summary[model]["beaten_p005"] += 1
        elif verdict == "BEATEN_p010":
            model_summary[model]["beaten_p010"] += 1
        else:
            model_summary[model]["inconclusive"] += 1

    # Print per-combo table
    print(f"\n{'Model':<20} {'Coin':<8} {'h':<4} {'Runs':<5} {'Beats':<7} {'Mean p':<12} {'Sign p':<12} {'MSE red%':<10} {'Verdict'}")
    print("-" * 110)
    for r in results:
        sign_p_str = f"{r['sign_test_pvalue']:.4f}" if r["sign_test_pvalue"] is not None else "N/A"
        mean_p_str = f"{r['mean_dm_pvalue']:.6f}" if r["mean_dm_pvalue"] is not None else "N/A"
        mse_str = f"{r['mse_reduction_pct']:.1f}" if r["mse_reduction_pct"] is not None else "N/A"
        print(f"{r['model']:<20} {r['coin']:<8} {r['horizon']:<4} {r['n_runs']:<5} "
              f"{r['n_beats_seeds']}/{r['n_total_seeds']:<5} {mean_p_str:<12} {sign_p_str:<12} "
              f"{mse_str:<10} {r['verdict_strict']}")

    # Print model summary
    print("\n" + "=" * 80)
    print("MODEL SUMMARY")
    print("=" * 80)
    total_p005 = 0
    total_p010 = 0
    total_beaten_p005 = 0
    total_beaten_p010 = 0
    total_inc = 0
    total_all = 0
    for model in ["M3_HAR_classic", "M3b_HAR_asymmetric", "M4_DLinear", "M5_HMM_regime", "M9_TFT"]:
        s = model_summary.get(model, {"p005": 0, "p010": 0, "beaten_p005": 0, "beaten_p010": 0, "inconclusive": 0, "total": 0})
        total_p005 += s["p005"]
        total_p010 += s["p010"]
        total_beaten_p005 += s["beaten_p005"]
        total_beaten_p010 += s["beaten_p010"]
        total_inc += s["inconclusive"]
        total_all += s["total"]
        print(f"  {model:<22} {s['total']} combos: "
              f"BEATS p<0.05: {s['p005']}, BEATS p<0.10: {s['p010']}, "
              f"BEATEN p<0.05: {s['beaten_p005']}, BEATEN p<0.10: {s['beaten_p010']}, "
              f"INCONCLUSIVE: {s['inconclusive']}")

    print(f"\n  {'TOTAL':<22} {total_all} combos: "
          f"BEATS p<0.05: {total_p005}, BEATS p<0.10: {total_p010}, "
          f"BEATEN p<0.05: {total_beaten_p005}, BEATEN p<0.10: {total_beaten_p010}, "
          f"INCONCLUSIVE: {total_inc}")

    # Edge population sign-test (across ALL combos)
    n_beats_total = sum(1 for r in results if r["verdict_strict"] in ("BEATS_p005", "BEATS_p010"))
    n_beaten_total = sum(1 for r in results if r["verdict_strict"] in ("BEATEN_p005", "BEATEN_p010"))
    n_total_combos = len(results)
    pop_sign_p = stats.binomtest(n_beats_total, n_total_combos, 0.5, alternative="greater").pvalue
    print(f"\n  Population sign-test: {n_beats_total}/{n_total_combos} combos beat, p={pop_sign_p:.4f}")

    # Save JSON output
    output_path = RESULTS.parent / "results" / "dm_retroactif" / "dm_retroactif_results.json"
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output = {
        "experiment": "DM_RETROACTIF_Cycle28_TrackA",
        "methodology": "Diebold-Mariano MSE-diff for M3/M3b/M4/M5, binomial dir-acc for M9. "
                       "Re-classification: BEATS p<0.05, BEATS p<0.10, INCONCLUSIVE. "
                       "Sign-test = binomial across seeds per combo.",
        "per_combo": results,
        "model_summary": {k: v for k, v in model_summary.items()},
        "population_sign_test": {
            "n_beats": n_beats_total,
            "n_total": n_total_combos,
            "p_value": round(pop_sign_p, 6),
        },
    }
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nResults saved to: {output_path}")

    # Generate markdown table for docs
    md_path = RESULTS.parent.parent / "docs" / "DM_RETROACTIF.md"
    md_lines = [
        "# DM Test Retroactif -- Cycle 28 Track A",
        "",
        "**Status:** COMPLETE",
        "",
        "## Methodology",
        "",
        "- Diebold-Mariano test on MSE loss differential (M3/M3b/M4/M5 vs HAR classic baseline)",
        "- M9 TFT: binomial test on direction accuracy vs majority-class baseline",
        "- Re-classification thresholds: BEATS p<0.05 (strict), BEATS p<0.10 (marginal), INCONCLUSIVE",
        "- Cross-seed sign-test: binomial H0:p=0.5 on per-seed BEATS counts",
        "",
        "## Per-combo results",
        "",
        "| Model | Coin | h | Runs | Beats | Mean p | Sign-test p | MSE red% | Verdict |",
        "|-------|------|---|------|-------|--------|-------------|----------|---------|",
    ]
    for r in results:
        sign_p_str = f"{r['sign_test_pvalue']:.4f}" if r["sign_test_pvalue"] is not None else "N/A"
        mean_p_str = f"{r['mean_dm_pvalue']:.6f}" if r["mean_dm_pvalue"] is not None else "N/A"
        mse_str = f"{r['mse_reduction_pct']:.1f}%" if r["mse_reduction_pct"] is not None else "N/A"
        md_lines.append(
            f"| {r['model']} | {r['coin']} | {r['horizon']} | {r['n_runs']} | "
            f"{r['n_beats_seeds']}/{r['n_total_seeds']} | {mean_p_str} | {sign_p_str} | "
            f"{mse_str} | **{r['verdict_strict']}** |"
        )

    md_lines.extend([
        "",
        "## Model summary",
        "",
        "| Model | Combos | BEATS p<0.05 | BEATS p<0.10 | BEATEN p<0.05 | BEATEN p<0.10 | INCONCLUSIVE |",
        "|-------|--------|-------------|-------------|---------------|--------------|-------------|",
    ])
    for model in ["M3_HAR_classic", "M3b_HAR_asymmetric", "M4_DLinear", "M5_HMM_regime", "M9_TFT"]:
        s = model_summary.get(model, {"p005": 0, "p010": 0, "beaten_p005": 0, "beaten_p010": 0, "inconclusive": 0, "total": 0})
        md_lines.append(f"| {model} | {s['total']} | {s['p005']} | {s['p010']} | {s['beaten_p005']} | {s['beaten_p010']} | {s['inconclusive']} |")

    md_lines.extend([
        f"| **TOTAL** | **{total_all}** | **{total_p005}** | **{total_p010}** | **{total_beaten_p005}** | **{total_beaten_p010}** | **{total_inc}** |",
        "",
        f"**Population sign-test:** {n_beats_total}/{n_total_combos} combos beat, "
        f"{n_beaten_total}/{n_total_combos} beaten, p={pop_sign_p:.4f}",
        "",
        "## Key findings",
        "",
    ])

    # Auto-generate key findings
    finding_num = 1
    if total_p005 > 0:
        best_models = [m for m, s in model_summary.items() if s["p005"] > 0]
        md_lines.append(f"{finding_num}. **Models with strict BEATS (p<0.05):** {', '.join(best_models)}")
        finding_num += 1
    if total_beaten_p005 > 0:
        beaten_models = [m for m, s in model_summary.items() if s["beaten_p005"] > 0]
        md_lines.append(f"{finding_num}. **Models significantly BEATEN by baseline (p<0.05):** {', '.join(beaten_models)}")
        finding_num += 1
    if total_p010 > 0:
        marginal = [m for m, s in model_summary.items() if s["p010"] > 0 and s["p005"] == 0]
        if marginal:
            md_lines.append(f"{finding_num}. **Models with marginal BEATS (p<0.10 only):** {', '.join(marginal)}")
            finding_num += 1
    no_signal = [m for m, s in model_summary.items() if s["p005"] == 0 and s["p010"] == 0 and s["beaten_p005"] == 0 and s["beaten_p010"] == 0]
    if no_signal:
        md_lines.append(f"{finding_num}. **Models with NO significant signal (INCONCLUSIVE across all combos):** {', '.join(no_signal)}")

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("\n".join(md_lines))
    print(f"Markdown saved to: {md_path}")


if __name__ == "__main__":
    main()
