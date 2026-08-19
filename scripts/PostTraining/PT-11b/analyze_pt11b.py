"""Final analysis of PT-11b multi-seed results.

Reads pt11b_multiseed_output/pt11b_per_seed_metrics.jsonl (one line per seed),
computes edge_sigma + DM pooled + DM per-seed (linear), prints verdict.
"""

import json
import sys
from pathlib import Path

import numpy as np

# Repo root: scripts/PostTraining/PT-11b/analyze_pt11b.py -> <root>/scripts/PostTraining/PT-11b
WORK_DIR = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(WORK_DIR / "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts"))
from dm_test import diebold_mariano_test


def main():
    metrics_path = WORK_DIR / "pt11b_multiseed_output" / "pt11b_per_seed_metrics.jsonl"
    if not metrics_path.exists():
        print(f"ERROR: {metrics_path} not found")
        sys.exit(1)

    per_seed_metrics = []
    with open(metrics_path) as f:
        for line in f:
            if line.strip():
                per_seed_metrics.append(json.loads(line))

    print("=" * 70)
    print(f" PT-11b MULTI-SEED FINAL ANALYSIS ({len(per_seed_metrics)} seeds) ")
    print("=" * 70)

    if len(per_seed_metrics) < 2:
        print(f"\nERROR: Need >= 2 seeds for cross-seed edge_sigma, got {len(per_seed_metrics)}")
        print("Cannot compute inter-seed std (would be 0 with 1 seed -> inf edge).")
        return 1

    # 1. Edge cross-seed
    seed_mean_rewards = []
    for m in per_seed_metrics:
        if m["reward_curve"]:
            mean_r = np.mean([v for _, v in m["reward_curve"]])
            seed_mean_rewards.append((m["seed"], mean_r))
    seeds_arr = np.array([s for s, _ in seed_mean_rewards])
    means_arr = np.array([r for _, r in seed_mean_rewards])
    overall_mean = np.mean(means_arr)
    inter_seed_std = np.std(means_arr, ddof=1)
    edge_sigma = overall_mean / inter_seed_std if inter_seed_std > 1e-10 else float("inf")
    print(f"\nEdge cross-seed : mean={overall_mean:.4f}, std={inter_seed_std:.4f}, edge={edge_sigma:.2f} sigma")
    for s, r in seed_mean_rewards:
        print(f"  seed {s}: mean reward = {r:.4f}")

    # 2. DM pooled
    min_len = min(len(m["reward_curve"]) for m in per_seed_metrics if m["reward_curve"])
    print(f"\nDM setup : {len(per_seed_metrics)} seeds, {min_len} steps/seed, total obs={min_len * len(per_seed_metrics)}")
    errors_model = np.concatenate([
        np.array([v for _, v in m["reward_curve"][:min_len]])
        for m in per_seed_metrics if m["reward_curve"]
    ])
    errors_baseline = np.zeros_like(errors_model)
    dm_pooled = diebold_mariano_test(errors_model, errors_baseline, loss_fn="linear")
    print(f"\nDM pooled (n={len(errors_model)}, linear) :")
    print(f"  dm_stat = {dm_pooled.dm_statistic:.4f}")
    print(f"  p_value = {dm_pooled.p_value:.6f}")
    print(f"  mean_loss_diff = {dm_pooled.mean_loss_diff:.4f}")

    # 3. DM per-seed
    dm_per_seed = []
    for m in per_seed_metrics:
        if not m["reward_curve"]:
            continue
        em = np.array([v for _, v in m["reward_curve"][:min_len]])
        eb = np.zeros_like(em)
        r = diebold_mariano_test(em, eb, loss_fn="linear")
        dm_per_seed.append((m["seed"], r))
    if dm_per_seed:
        dm_p_median = float(np.median([r.p_value for _, r in dm_per_seed]))
        dm_diff_median = float(np.median([r.mean_loss_diff for _, r in dm_per_seed]))
        print(f"\nDM per-seed (median p, n_seeds={len(dm_per_seed)}) :")
        for s, r in dm_per_seed:
            print(f"  seed {s}: dm_stat={r.dm_statistic:.4f}, p={r.p_value:.6f}, loss_diff={r.mean_loss_diff:.4f}")
        print(f"  dm_p_median = {dm_p_median:.6f}")
        print(f"  dm_diff_median = {dm_diff_median:.4f}  (per-seed mean reward gap vs zero baseline)")
    else:
        dm_p_median = 1.0
        dm_diff_median = 0.0

    # 4. Verdict combine (regle C)
    edge_ok = edge_sigma >= 2.0
    # Directional DM leg (#11419 method lesson): p < 0.05 alone says the two
    # series DIFFER, not which side wins. mean_loss_diff here is the per-seed
    # mean reward gap vs the zero baseline (positive = model better), so the
    # DM leg carries significance AND direction on the same quantity.
    dm_ok = (dm_p_median < 0.05) and (dm_diff_median > 0)
    if edge_ok and dm_ok:
        verdict = "BEATS"
    elif (not edge_ok) and (not dm_ok):
        verdict = "NO BEATS"
    else:
        verdict = "INCONCLUSIVE"

    print("\n" + "=" * 70)
    print(f" VERDICT PT-11b FINAL ({len(per_seed_metrics)} seeds) ")
    print("=" * 70)
    print(f"Seeds : {len(per_seed_metrics)}")
    print(f"Steps/seed : {min_len}")
    print(f"edge_sigma : {edge_sigma:.2f}  (>= 2.0 required)")
    print(f"dm_p_median : {dm_p_median:.6f}  (< 0.05 required)")
    print(f"dm_diff_median : {dm_diff_median:.4f}  (> 0 required, same quantity as the DM)")
    print(f"dm_pooled_p : {dm_pooled.p_value:.6f}")
    print(f"Verdict : {verdict}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    sys.exit(main())