"""PT-18 metrics recompute -- re-derive the per-run aggregates from the checkpoints.

Why this exists (repair of the #19037 review by myia-po-2025:CoursIA-2):

`metrics_from_logits` (pt18_train.py) fed `conf = q[label]` -- the probability the
model assigns to the TRUE class -- to two consumers:

  * `laya.common.ece_score(conf, correct)`, whose contract (read in the library)
    bins a *reported* confidence against the outcome. The true-class mass is an
    oracle quantity: it is not available at inference on an error.
  * the ranking of the coverage-accuracy curve (`np.argsort(-all_conf)`), where
    ranking by `q[label]` puts the errors last *by construction* -- the curve read
    1.000 accuracy at 50% coverage.

Both now use the top-1 confidence `max(q)`, which is what a deployed selector
actually has. The committed aggregate `pt18_per_run_metrics.jsonl` predates the
fix, so it is regenerated here from the SAME checkpoints, the SAME `eval_items.pt`
and the SAME functions the training script used: no retraining, no new split, no
new item order.

`acc`, `nll` and `brier` do not read `conf`: this script compares each regenerated
value against the committed one and REPORTS any drift in them, so a silent change
in an unaffected metric is visible rather than assumed away.

Usage:
  python pt18_metrics_recompute.py                  # all runs, writes the jsonl
  python pt18_metrics_recompute.py --out PATH       # alternate output
  python pt18_metrics_recompute.py --arms ce rl     # subset (diagnosis)

Writes <out> (default: ./pt18_per_run_metrics.jsonl), carrying over the committed
metadata keys unchanged, and prints an old-vs-new table for the affected fields.
"""
import argparse
import json
import os
import sys

import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

RUNS_DIR = "D:/dev/pt18_runs"
ARMS = ["ce", "rl", "rl_ce"]
SEEDS = [0, 1, 7, 42]
PHASE_KEYS = ("before_T1", "after_T1", "after_Tfitted")
# Schema of the committed aggregate: the pooled dict without its sample count,
# so the regenerated file diffs on values only, never on shape.
POOLED_KEYS = ["acc", "nll", "brier", "ece", "coverage_accuracy"]
DEFAULT_OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pt18_per_run_metrics.jsonl")


def pooled_slice(metrics):
    return {k: metrics["pooled"][k] for k in POOLED_KEYS}


def build_base(device):
    """The pre-training model: build_model + the base weights of the snapshot.

    Mirrors pt18_train.py (model construction) -- that is the state `before_T1`
    measures, so it is reproduced from the same artefacts, not retyped.
    """
    from huggingface_hub import snapshot_download
    from laya.agent import _fix_tokenizer_config
    from laya.common import build_model
    from safetensors.torch import load_file
    from transformers import AutoTokenizer

    from pt18_train import MODEL_ID, REVISION

    model_dir = snapshot_download(MODEL_ID, revision=REVISION)
    _fix_tokenizer_config(model_dir)
    with open(os.path.join(model_dir, "rl_agent_config.json")) as f:
        cfg = json.load(f)
    cfg["gradient_checkpointing"] = True
    cfg["max_tokens_per_batch"] = 4096
    cfg["max_len"] = 1024
    cfg["head_max_len"] = 256
    tok = AutoTokenizer.from_pretrained(os.path.join(model_dir, "tokenizer"))
    model = build_model(cfg, encoder_dir=os.path.join(model_dir, "encoder"))
    model.load_state_dict(load_file(os.path.join(model_dir, "model.safetensors")), strict=True)
    model.to(device)
    return model, tok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--arms", nargs="*", default=ARMS, choices=ARMS)
    args = ap.parse_args()

    if not torch.cuda.is_available():
        raise SystemExit("GPU required (rule F: no CPU fallback)")

    from pt18_train import collect_logits, metrics_from_logits

    device = torch.device("cuda", 0)

    # The committed file is both the schema reference and the A/B control: its
    # metadata keys are carried over untouched and its values are compared.
    old = {}
    order = []
    if os.path.exists(args.out):
        for line in open(args.out, encoding="utf-8"):
            line = line.strip()
            if line:
                m = json.loads(line)
                old[(m["arm"], m["seed"])] = m
                order.append((m["arm"], m["seed"]))
    for arm in args.arms:
        for seed in SEEDS:
            if (arm, seed) not in order:
                order.append((arm, seed))
    meta_keys = [k for k in old[order[0]] if k not in PHASE_KEYS and k not in ("arm", "seed")] if old else []

    eval_items = torch.load(os.path.join(RUNS_DIR, "eval_items.pt"), weights_only=False)
    print(f"eval_items: {len(eval_items)} decisions | meta carried over: {meta_keys}", flush=True)

    # before_T1 depends on the base model and eval_items only: one measurement
    # serves every line (the committed file carries one distinct value for 12).
    before = None
    for m in old.values():
        if m.get("before_T1"):
            before = m["before_T1"]
            break
    if before is None:
        model, tok = build_base(device)
        before = pooled_slice(metrics_from_logits(collect_logits(model, eval_items, tok, device)))
        print(f"before_T1 (modele de base): {json.dumps(before)}", flush=True)
        del model
        torch.cuda.empty_cache()

    rows = []
    for arm, seed in order:
        if arm not in args.arms:
            continue
        model, tok = build_base(device)
        from safetensors.torch import load_file

        run_dir = os.path.join(RUNS_DIR, f"{arm}_seed{seed}")
        with open(os.path.join(run_dir, "metrics.json")) as f:
            temps = json.load(f)["temperatures"]
        model.load_state_dict(
            {k: v.float() for k, v in load_file(os.path.join(run_dir, "model.safetensors")).items()},
            strict=True,
        )
        model.to(device)
        # One collection serves both temperatures: metrics_from_logits is pure.
        pairs = collect_logits(model, eval_items, tok, device)
        t1 = pooled_slice(metrics_from_logits(pairs))
        tt = pooled_slice(metrics_from_logits(pairs, temps=temps))

        row = {"arm": arm, "seed": seed}
        for k in meta_keys:
            row[k] = old[(arm, seed)][k]
        row["before_T1"] = before
        row["after_T1"] = t1
        row["after_Tfitted"] = tt
        rows.append(row)

        o = old.get((arm, seed))
        if o:
            drift = [
                f"{ph}.{k}: {o[ph][k]} -> {row[ph][k]}"
                for ph in PHASE_KEYS
                if o.get(ph)
                for k in ("acc", "nll", "brier")
                if abs(o[ph][k] - row[ph][k]) > 1e-9
            ]
            print(
                f"{arm}_seed{seed}: ece T=1 {o['after_T1']['ece']:.4f} -> {t1['ece']:.4f} | "
                f"cov@0.5 T=1 {o['after_T1']['coverage_accuracy']['cov0.5']:.3f} -> "
                f"{t1['coverage_accuracy']['cov0.5']:.3f} | "
                f"cov@0.5 T=fitted {o['after_Tfitted']['coverage_accuracy']['cov0.5']:.3f} -> "
                f"{tt['coverage_accuracy']['cov0.5']:.3f} | drift acc/nll/brier: {drift or 'aucun'}",
                flush=True,
            )
        del model
        torch.cuda.empty_cache()

    if len(rows) < len(order):
        raise SystemExit(f"incomplete: {len(rows)} run(s) computed for {len(order)} -- refusing to write a partial file")
    with open(args.out, "w", encoding="utf-8") as f:
        for row in rows:
            f.write(json.dumps(row) + "\n")
    print(f"wrote {args.out} ({len(rows)} runs)", flush=True)


if __name__ == "__main__":
    main()
