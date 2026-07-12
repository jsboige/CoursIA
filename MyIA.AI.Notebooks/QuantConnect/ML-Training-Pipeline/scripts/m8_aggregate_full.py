"""Aggregate M8 SOTA sweep results: 4 models x 2 coins x 3 horizons x 4 seeds = 96 runs.

Outputs per-combo statistics (mean/std across 4 seeds) for:
  - MSE, MAE, DirAcc (step 1)
  - Edge over majority class baseline

Verdict per combo (vs majority baseline):
  - BEATS  : mean(edge) >= 2*std(edge) AND mean(edge) > 0
  - NO BEATS : mean(edge) <= -2*std(edge)
  - INCONCLUSIVE : otherwise

NOTE: The driver docstring mentions HAR baseline. HAR comparison TODO once
HAR_RV reference numbers are committed. For now, compares to majority class.
"""
from __future__ import annotations
import json
import statistics
from pathlib import Path

ROOT = Path(r"d:/CoursIA/MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m8_sota_overnight")
MODELS = ["tft", "mamba", "itransformer", "patchtst"]
COINS = ["BTC_USD", "ETH_USD"]
HORIZONS = [1, 5, 10]


def load_combo(model: str, coin: str, h: int) -> list[dict]:
    """Load all metrics.json (or metadata.json) for one combo across all seeds."""
    base = ROOT / f"{model}_{coin}_h{h}"
    if not base.is_dir():
        return []
    seeds_data = []
    for seed_dir in sorted(base.glob("seed_*")):
        metas = sorted(seed_dir.glob("*/metadata.json"))
        if metas:
            metas = [metas[-1]]  # most recent timestamp
        else:
            metas = sorted(seed_dir.glob("metadata.json"))
        for m in metas:
            try:
                seeds_data.append(json.loads(m.read_text(encoding="utf-8")))
            except Exception as e:
                print(f"  WARN: failed to load {m}: {e}")
    # tft uses multi-seed in single subprocess: search base/<ts>/metadata.json
    if not seeds_data:
        for m in sorted(base.glob("*/metadata.json")):
            try:
                seeds_data.append(json.loads(m.read_text(encoding="utf-8")))
            except Exception as e:
                print(f"  WARN: failed to load {m}: {e}")
    return seeds_data


def stats(vals: list[float]) -> tuple[float, float]:
    if not vals:
        return float("nan"), float("nan")
    if len(vals) == 1:
        return vals[0], 0.0
    return statistics.mean(vals), statistics.stdev(vals)


def verdict(edge_mean: float, edge_std: float) -> str:
    if edge_std == 0:
        return "SINGLE_SEED" if edge_mean != 0 else "NO_DATA"
    if edge_mean >= 2 * edge_std and edge_mean > 0:
        return "BEATS"
    if edge_mean <= -2 * edge_std:
        return "NO BEATS"
    return "INCONCLUSIVE"


def main():
    out_md = ["# M8 SOTA Sweep Verdict (vs Majority Class Baseline)", ""]
    out_md.append("**Setup:** 4 models x 2 coins x 3 horizons x 4 seeds = 96 runs, "
                  "seq_len=60, epochs=250, GPU2 (RTX 4090, PCIe x4)")
    out_md.append("")
    out_md.append("**Verdict criterion:** edge_over_majority cross-seed >= 2*std (BEATS) "
                  "or <= -2*std (NO BEATS), otherwise INCONCLUSIVE.")
    out_md.append("")
    out_md.append("**HAR baseline comparison TODO** — driver intended HAR_mse but "
                  "per-seed metadata only has majority_class baseline.")
    out_md.append("")
    out_md.append("| Model | Coin | h | n_seeds | MSE mean+/-std | DirAcc mean+/-std | Edge mean+/-std | Verdict |")
    out_md.append("|-------|------|---|---------|----------------|-------------------|-----------------|---------|")

    counts = {"BEATS": 0, "NO BEATS": 0, "INCONCLUSIVE": 0, "SINGLE_SEED": 0, "NO_DATA": 0}
    for model in MODELS:
        for coin in COINS:
            for h in HORIZONS:
                seeds_data = load_combo(model, coin, h)
                if not seeds_data:
                    out_md.append(f"| {model} | {coin} | {h} | 0 | NO_DATA | NO_DATA | NO_DATA | NO_DATA |")
                    counts["NO_DATA"] += 1
                    continue
                mse_vals = [d["metrics"]["mse"] for d in seeds_data]
                dir_vals = [d["metrics"]["direction_accuracy_step1"] for d in seeds_data]
                edge_vals = [d["metrics"]["edge_over_majority"] for d in seeds_data]
                mse_m, mse_s = stats(mse_vals)
                dir_m, dir_s = stats(dir_vals)
                edge_m, edge_s = stats(edge_vals)
                v = verdict(edge_m, edge_s)
                counts[v] += 1
                out_md.append(
                    f"| {model} | {coin} | {h} | {len(seeds_data)} | "
                    f"{mse_m:.6f}+/-{mse_s:.6f} | {dir_m:.4f}+/-{dir_s:.4f} | "
                    f"{edge_m:+.4f}+/-{edge_s:.4f} | **{v}** |"
                )

    out_md.append("")
    out_md.append("## Summary")
    for k, v in counts.items():
        out_md.append(f"- {k}: {v}")
    out_md.append("")
    out_md.append("## Cross-model BEATS pattern")
    out_md.append("(How many BEATS verdicts each model has across 6 combos)")
    out_md.append("")
    for model in MODELS:
        beats = no_beats = inc = 0
        for coin in COINS:
            for h in HORIZONS:
                seeds_data = load_combo(model, coin, h)
                if not seeds_data:
                    continue
                edge_vals = [d["metrics"]["edge_over_majority"] for d in seeds_data]
                edge_m, edge_s = stats(edge_vals)
                v = verdict(edge_m, edge_s)
                if v == "BEATS": beats += 1
                elif v == "NO BEATS": no_beats += 1
                elif v == "INCONCLUSIVE": inc += 1
        out_md.append(f"- **{model}**: {beats} BEATS / {inc} INCONCLUSIVE / {no_beats} NO BEATS")

    md = "\n".join(out_md) + "\n"
    out_path = ROOT / "_verdict_full.md"
    out_path.write_text(md, encoding="utf-8")
    print(md)
    print(f"\nWritten: {out_path}")


if __name__ == "__main__":
    main()
