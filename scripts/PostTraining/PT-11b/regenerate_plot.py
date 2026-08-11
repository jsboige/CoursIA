"""Regenerate pt11b_reward_curves.png with all 4 seeds.

The seed=42 plot only had 1 seed. Now we have 4 seeds, so re-render.
"""

import json
import matplotlib
matplotlib.use("Agg")  # non-interactive backend, no blocking
import matplotlib.pyplot as plt
from pathlib import Path

# Repo root: scripts/PostTraining/PT-11b/regenerate_plot.py -> <root>/scripts/PostTraining/PT-11b
REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_DIR = REPO_ROOT / "pt11b_multiseed_output"
JSONL_PATH = OUTPUT_DIR / "pt11b_per_seed_metrics.jsonl"
PNG_PATH = REPO_ROOT / "MyIA.AI.Notebooks" / "GenAI" / "PostTraining" / "pt11b_reward_curves.png"

per_seed_metrics = []
with open(JSONL_PATH) as f:
    for line in f:
        if line.strip():
            per_seed_metrics.append(json.loads(line))

print(f"Loaded {len(per_seed_metrics)} seeds")
plt.figure(figsize=(10, 6))
colors = ["#2B5C8C", "#C44E52", "#55A868", "#8172B3"]
for i, m in enumerate(per_seed_metrics):
    curve = m["reward_curve"]
    if not curve:
        continue
    steps, vals = zip(*curve)
    plt.plot(steps, vals, marker="o", linewidth=1.5, alpha=0.85,
             color=colors[i % len(colors)], label=f"seed {m['seed']}", markersize=3)

plt.xlabel("Step")
plt.ylabel("Reward (outcome verifier)")
plt.title(f"PT-11b RLVR — Qwen3.5-0.8B x {len(per_seed_metrics)} seeds (100 steps each)")
plt.grid(True, alpha=0.3)
plt.legend(loc="lower right")
plt.savefig(PNG_PATH, dpi=100, bbox_inches="tight")
print(f"Figure saved: {PNG_PATH}")
plt.close()
print("Done.")