"""PT-18 stage 2 prep: build train/eval items for laya-multilingual on typed-decisions.

Faithful adaptation of upstream notebook cell 6 (laya_finetune_typed_decisions_2xT4_kaggle),
switched to the multilingual checkpoint and extended with an eval-items build from the test split.
"""
import json
import os

import torch
from datasets import load_dataset
from huggingface_hub import snapshot_download
from laya.agent import _fix_tokenizer_config
from laya.common import QTYPES, build_sequence, render_options
from transformers import AutoTokenizer

MODEL_ID = "convaiinnovations/laya-multilingual"
REVISION = "e4e9ddf21a7b1903b7acffd8814ad4307bf63a67"  # pinned by laya/revisions.py
OUT_DIR = "D:/dev/pt18_runs"

model_dir = snapshot_download(MODEL_ID, revision=REVISION)
_fix_tokenizer_config(model_dir)

tok = AutoTokenizer.from_pretrained(os.path.join(model_dir, "tokenizer"))
with open(os.path.join(model_dir, "rl_agent_config.json")) as f:
    cfg = json.load(f)
print("cfg keys:", sorted(cfg.keys()))
print("max_len", cfg.get("max_len"), "head_max_len", cfg.get("head_max_len"))


def build_training_item(state, q, gold_q):
    t = q["type"]
    crit = q.get("criteria", {})
    if t == "choice":
        keys = list(crit.keys())
        target = [gold_q["probabilities"].get(k, 0.0) for k in keys]
    elif t == "noul":
        target = [gold_q["probabilities"].get("false", 0.5), gold_q["probabilities"].get("true", 0.5)]
    elif t == "score":
        n_levels = len(crit) if isinstance(crit, list) else 4
        target = [gold_q["probabilities"].get(str(i), 0.0) for i in range(n_levels)]
    else:
        return None

    s = sum(target)
    target = [v / s for v in target] if s > 0 else [1.0 / len(target)] * len(target)
    label = target.index(max(target))
    k = len(render_options({"t": t, "crit": crit}))

    seq, markers = build_sequence(tok, state, {"t": t, "ins": q["instructions"], "crit": crit}, cfg["max_len"], cfg["head_max_len"])
    if len(markers) != k:
        return None
    return {"ids": seq, "markers": markers, "qtype": QTYPES[t], "target": target, "label": label}


def build_split(split_name):
    ds = load_dataset("LocalLLaMA/typed-decisions", "all", split=split_name)
    items, skipped = [], 0
    for row in ds:
        state = json.loads(row["state"])
        questions = json.loads(row["questions"])
        gold = json.loads(row["gold"])
        for qid, q in questions.items():
            if qid in gold:
                it = build_training_item(state, q, gold[qid])
                if it:
                    items.append(it)
                else:
                    skipped += 1
    return items, skipped, len(ds)


os.makedirs(OUT_DIR, exist_ok=True)
train_items, sk_tr, n_tr = build_split("train")
eval_items, sk_ev, n_ev = build_split("test")

from collections import Counter

for name, items in [("train", train_items), ("eval", eval_items)]:
    qt = Counter(i["qtype"] for i in items)
    seq_lens = [len(i["ids"]) for i in items]
    print(f"{name}: {len(items)} items from {n_ev if name=='eval' else n_tr} cases, skipped {sk_ev if name=='eval' else sk_tr}")
    print(f"  qtypes: {dict(qt)}")
    print(f"  seq len: mean {sum(seq_lens)/len(seq_lens):.0f} max {max(seq_lens)}")

torch.save(train_items, os.path.join(OUT_DIR, "train_items.pt"))
torch.save(eval_items, os.path.join(OUT_DIR, "eval_items.pt"))
print("saved to", OUT_DIR)
