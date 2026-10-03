"""PT-18 eval: per-decision losses for the paired Diebold-Mariano test.

Reloads each run's checkpoint (model.safetensors written by pt18_train.py),
runs the SAME eval_items.pt in the SAME deterministic order, and writes
predictions.jsonl next to metrics.json: one line per decision with the MSE
loss of the reported distribution. The idx is the eval-item index, so losses
are pairable across arms seed-by-seed (same items, same order).

Usage: python pt18_eval.py <arm> <seed>   (or --all for every complete run)
Writes D:/dev/pt18_runs/<arm>_seed<seed>/predictions.jsonl
"""
import argparse
import json
import os

import numpy as np
import torch
from huggingface_hub import snapshot_download
from laya.agent import _fix_tokenizer_config
from laya.common import build_model
from safetensors.torch import load_file
from transformers import AutoTokenizer

MODEL_ID = "convaiinnovations/laya-multilingual"
REVISION = "e4e9ddf21a7b1903b7acffd8814ad4307bf63a67"
RUNS_DIR = "D:/dev/pt18_runs"


def eval_run(arm, seed, device):
    from pt18_train import collate_train_batch, collect_logits  # same collate, same order

    out_dir = os.path.join(RUNS_DIR, f"{arm}_seed{seed}")
    metrics_path = os.path.join(out_dir, "metrics.json")
    if not os.path.exists(metrics_path):
        print(f"skip {arm}_seed{seed}: no metrics.json")
        return False

    model_dir = snapshot_download(MODEL_ID, revision=REVISION)
    _fix_tokenizer_config(model_dir)
    with open(os.path.join(model_dir, "rl_agent_config.json")) as f:
        cfg = json.load(f)
    tok = AutoTokenizer.from_pretrained(os.path.join(model_dir, "tokenizer"))
    model = build_model(cfg, encoder_dir=os.path.join(model_dir, "encoder"))
    sd = load_file(os.path.join(out_dir, "model.safetensors"))
    model.load_state_dict({k: v.float() for k, v in sd.items()}, strict=True)
    model.to(device)
    model.eval()

    # Same temperatures as the run (post-calibration) so the loss measured here
    # is the loss of the shipped model, not of an uncalibrated variant.
    with open(metrics_path) as f:
        temps = json.load(f)["temperatures"]

    eval_items = torch.load(os.path.join(RUNS_DIR, "eval_items.pt"), weights_only=False)
    pairs = collect_logits(model, eval_items, tok, device)

    lines = []
    for idx, (qt, z, target, label) in enumerate(pairs):
        T = temps[qt] if qt < len(temps) else 1.0
        zz = z / T
        q = np.exp(zz - zz.max())
        q = q / q.sum()
        loss_mse = float(np.sum((q - target) ** 2))
        lines.append({
            "idx": idx, "qtype": int(qt), "label": int(label),
            "loss_mse": loss_mse,
            "conf": float(q[label]),
            "correct": int(np.argmax(q) == label),
        })
    out_path = os.path.join(out_dir, "predictions.jsonl")
    with open(out_path, "w", encoding="utf-8") as f:
        for line in lines:
            f.write(json.dumps(line) + "\n")
    print(f"wrote {out_path} ({len(lines)} decisions)")
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("arm", nargs="?", choices=["ce", "rl", "rl_ce"])
    ap.add_argument("seed", type=int, nargs="?")
    ap.add_argument("--all", action="store_true")
    args = ap.parse_args()

    if not torch.cuda.is_available():
        raise SystemExit("GPU required (rule F: no CPU fallback)")
    device = torch.device("cuda", 0)

    if args.all:
        done = 0
        for arm in ["ce", "rl", "rl_ce"]:
            for seed in [0, 1, 7, 42]:
                if eval_run(arm, seed, device):
                    done += 1
        print(f"evaluated {done} runs")
    else:
        if args.arm is None or args.seed is None:
            raise SystemExit("give <arm> <seed> or --all")
        eval_run(args.arm, args.seed, device)


if __name__ == "__main__":
    main()
