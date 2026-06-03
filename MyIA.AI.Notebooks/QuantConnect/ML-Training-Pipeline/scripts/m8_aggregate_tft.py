"""Aggregate M8 TFT results (the 6 successful combos) into a verdict."""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(r"d:/CoursIA/MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m8_sota_overnight")
out = []
for d in sorted(ROOT.glob("tft_*")):
    if not d.is_dir():
        continue
    metas = sorted(d.glob("*/metadata.json"))
    if not metas:
        continue
    m = json.loads(metas[0].read_text(encoding="utf-8"))
    h = m["hyperparams"]
    met = m["metrics"]
    out.append({
        "name": d.name,
        "symbols": h["symbols"],
        "pred_len": h["pred_len"],
        "seeds": h["seeds"],
        "mse": met["mse"],
        "mae": met["mae"],
        "dir_acc_step1": met["direction_accuracy_step1"],
        "majority_baseline": met["majority_class_baseline"]["majority_class_accuracy"],
        "edge_over_majority": met["edge_over_majority"],
    })

print(json.dumps(out, indent=2))

# Verdict per combo: edge >= 0 = beats baseline, edge < 0 = fails
print("\n=== TFT vs Majority Baseline (DirAcc) ===")
for r in out:
    verdict = "BEATS" if r["edge_over_majority"] >= 0.005 else ("NO BEATS" if r["edge_over_majority"] <= -0.005 else "INCONCLUSIVE")
    print(f"  {r['name']:30s} edge={r['edge_over_majority']:+.4f}  ({verdict})")
