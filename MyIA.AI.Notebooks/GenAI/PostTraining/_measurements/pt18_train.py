"""PT-18 stage 2: 3-arm ablation fine-tuning of laya-multilingual on typed-decisions.

Faithful mono-GPU adaptation of the upstream 2xT4 DDP notebook (train_ddp.py cell 8).
Arms differ only in the loss composition (upstream lines 169-173):
  ce     -> loss = loss_ce
  rl     -> loss = loss_rl
  rl_ce  -> loss = loss_rl + 1.0 * loss_ce   (the published recipe)

Usage: python pt18_train.py <arm> <seed> [--epochs N] [--max-items N] [--max-steps N] [--tag S]
Writes D:/dev/pt18_runs/<arm>_seed<seed><tag>/{model.safetensors, metrics.json, train_log.txt}
"""
import argparse
import json
import os
import random
import time

import numpy as np
import torch
from huggingface_hub import snapshot_download
from laya.agent import _fix_tokenizer_config
from laya.common import QTYPES, build_model, ece_score, proper_reward
from safetensors.torch import load_file, save_file
from transformers import AutoTokenizer

MODEL_ID = "convaiinnovations/laya-multilingual"
REVISION = "e4e9ddf21a7b1903b7acffd8814ad4307bf63a67"
RUNS_DIR = "D:/dev/pt18_runs"


def collate_train_batch(items, pad_id):
    n, L = len(items), max(len(it["ids"]) for it in items)
    kmax = max(len(it["markers"]) for it in items)
    ids = torch.full((n, L), pad_id, dtype=torch.long)
    att = torch.zeros((n, L), dtype=torch.long)
    mpos = torch.zeros((n, kmax), dtype=torch.long)
    mmask = torch.zeros((n, kmax), dtype=torch.bool)
    target = torch.zeros((n, kmax), dtype=torch.float32)
    for i, it in enumerate(items):
        ids[i, : len(it["ids"])] = torch.tensor(it["ids"])
        att[i, : len(it["ids"])] = 1
        k = len(it["markers"])
        mpos[i, :k] = torch.tensor(it["markers"])
        mmask[i, :k] = True
        target[i, : len(it["target"])] = torch.tensor(it["target"], dtype=torch.float32)
    return {
        "input_ids": ids,
        "attention_mask": att,
        "marker_pos": mpos,
        "marker_mask": mmask,
        "target": target,
        "qtype": torch.tensor([it["qtype"] for it in items]),
        "label": torch.tensor([it["label"] for it in items]),
    }


def fit_one_temp(sel):
    if len(sel) < 10:
        return 1.0
    kmax = max(len(z) for z, _ in sel)
    Z = torch.full((len(sel), kmax), -1e4)
    T = torch.zeros((len(sel), kmax))
    for i, (z, t) in enumerate(sel):
        Z[i, : len(z)] = torch.tensor(z)
        T[i, : len(t)] = torch.tensor(t, dtype=torch.float32)
    log_t = torch.zeros(1, requires_grad=True)
    opt = torch.optim.LBFGS([log_t], lr=0.1, max_iter=100)

    def closure():
        opt.zero_grad()
        loss = -(T * torch.log_softmax(Z / log_t.exp(), -1)).sum(-1).mean()
        loss.backward()
        return loss

    opt.step(closure)
    return float(torch.clamp(log_t.exp(), 0.1, 10.0).item())


@torch.no_grad()
def collect_logits(model, items, tok, device):
    """Return per-item (qtype, logits[:k], target, label) on CPU."""
    out = []
    model.eval()
    for c_idx in range(0, len(items), 16):
        chunk = items[c_idx : c_idx + 16]
        b = collate_train_batch(chunk, tok.pad_token_id)
        with torch.autocast("cuda", dtype=torch.float16):
            logits, _ = model(
                b["input_ids"].to(device),
                b["attention_mask"].to(device),
                b["marker_pos"].to(device),
                b["marker_mask"].to(device),
                b["qtype"].to(device),
            )
        l_np = logits.float().cpu().numpy()
        for r, it in enumerate(chunk):
            k = len(it["markers"])
            out.append((it["qtype"], l_np[r, :k], np.array(it["target"], dtype=np.float64), it["label"]))
    return out


def metrics_from_logits(pairs, temps=(1.0, 1.0, 1.0)):
    """acc, NLL, Brier, ECE (per qtype + pooled) at given temperatures."""
    res = {}
    per_qt_conf, per_qt_correct = {0: [], 1: [], 2: []}, {0: [], 1: [], 2: []}
    for qt, z, target, label in pairs:
        T = temps[qt] if qt < len(temps) else 1.0
        q = np.exp((z / T) - np.max(z / T))
        q = q / q.sum()
        conf = float(q[label])
        correct = int(np.argmax(q) == label)
        per_qt_conf[qt].append(conf)
        per_qt_correct[qt].append(correct)
        res.setdefault(qt, {"nll": [], "brier": [], "acc": []})
        res[qt]["nll"].append(-float(np.sum(target * np.log(np.clip(q, 1e-12, None)))))
        res[qt]["brier"].append(float(np.sum((q - target) ** 2)))
        res[qt]["acc"].append(correct)
    out = {}
    for qt in sorted(res):
        conf = np.array(per_qt_conf[qt])
        corr = np.array(per_qt_correct[qt], dtype=bool)
        out[f"qt{qt}"] = {
            "n": len(conf),
            "acc": float(corr.mean()),
            "nll": float(np.mean(res[qt]["nll"])),
            "brier": float(np.mean(res[qt]["brier"])),
            "ece": float(ece_score(conf, corr)),
        }
    all_conf = np.concatenate([np.array(per_qt_conf[qt]) for qt in sorted(res)])
    all_corr = np.concatenate([np.array(per_qt_correct[qt], dtype=bool) for qt in sorted(res)])
    all_nll = [v for qt in sorted(res) for v in res[qt]["nll"]]
    all_br = [v for qt in sorted(res) for v in res[qt]["brier"]]
    out["pooled"] = {
        "n": len(all_conf),
        "acc": float(all_corr.mean()),
        "nll": float(np.mean(all_nll)),
        "brier": float(np.mean(all_br)),
        "ece": float(ece_score(all_conf, all_corr)),
    }
    # Coverage-accuracy curve on pooled top-1 confidence
    order = np.argsort(-all_conf)
    sorted_corr = all_corr[order]
    curve = {}
    for cov in [0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 0.99]:
        m = max(1, int(round(cov * len(sorted_corr))))
        curve[f"cov{cov}"] = float(sorted_corr[:m].mean())
    out["pooled"]["coverage_accuracy"] = curve
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("arm", choices=["ce", "rl", "rl_ce"])
    ap.add_argument("seed", type=int)
    ap.add_argument("--epochs", type=int, default=4)
    ap.add_argument("--max-items", type=int, default=0)
    ap.add_argument("--max-steps", type=int, default=0, help="smoke cap on optimizer steps")
    ap.add_argument("--tag", default="")
    args = ap.parse_args()

    assert torch.cuda.is_available(), "GPU required (rule F: no CPU fallback for this arm)"
    device = torch.device("cuda", 0)
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    random.seed(args.seed)

    out_dir = os.path.join(RUNS_DIR, f"{args.arm}_seed{args.seed}{args.tag}")
    os.makedirs(out_dir, exist_ok=True)
    log_f = open(os.path.join(out_dir, "train_log.txt"), "w", encoding="utf-8")

    def log(msg):
        print(msg)
        log_f.write(msg + "\n")
        log_f.flush()

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
    model.encoder.gradient_checkpointing_enable(gradient_checkpointing_kwargs={"use_reentrant": False})
    model.head_checkpointing = True
    model.to(device)
    model.train()

    all_items = torch.load(os.path.join(RUNS_DIR, "train_items.pt"), weights_only=False)
    eval_items = torch.load(os.path.join(RUNS_DIR, "eval_items.pt"), weights_only=False)

    # Calibration holdout identical to upstream (seed 20260922, rank-independent)
    CALIB_MAX = 400
    order = list(range(len(all_items)))
    random.Random(20260922).shuffle(order)
    n_calib = min(CALIB_MAX, len(all_items) // 10)
    calib_items = [all_items[i] for i in sorted(order[:n_calib])]
    train_items = [all_items[i] for i in sorted(order[n_calib:])]
    if args.max_items and args.max_items < len(train_items):
        random.Random(args.seed).shuffle(train_items)
        train_items = sorted(train_items[: args.max_items])

    EPOCHS = args.epochs
    MICRO_BATCH = 8
    GRAD_ACCUM = 4
    GROUP_SIZE = 4
    LR_ENCODER = 2.5e-5
    LR_HEAD = 1.0e-4
    SIGMA_START = 0.4
    SIGMA_END = 0.1

    enc_params = [p for n, p in model.named_parameters() if "encoder." in n]
    head_params = [p for n, p in model.named_parameters() if "encoder." not in n]
    optimizer = torch.optim.AdamW(
        [{"params": enc_params, "lr": LR_ENCODER}, {"params": head_params, "lr": LR_HEAD}],
        weight_decay=0.01,
    )
    total_updates = max(1, (len(train_items) // (MICRO_BATCH * GRAD_ACCUM)) * EPOCHS)
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=total_updates, eta_min=1e-6)
    scaler = torch.amp.GradScaler("cuda", enabled=True)

    log(f"arm={args.arm} seed={args.seed} items={len(train_items)} calib={len(calib_items)} epochs={EPOCHS} updates={total_updates}")

    # Pre-training metrics (T=1)
    t0 = time.time()
    before = metrics_from_logits(collect_logits(model, eval_items, tok, device))
    log(f"metrics BEFORE (T=1): {json.dumps(before['pooled'])}")

    t0 = time.time()
    step_count = 0
    for epoch in range(EPOCHS):
        # Item order is seed-INDEPENDENT (as upstream 42+epoch): arms and seeds see
        # the same batches; the seed only drives the exploration noise eps.
        random.seed(1000 + epoch)
        random.shuffle(train_items)
        optimizer.zero_grad(set_to_none=True)
        accum_step = 0
        epoch_loss, n_batches = 0.0, 0
        progress = epoch / max(1, EPOCHS - 1)
        sigma = SIGMA_START + (SIGMA_END - SIGMA_START) * progress

        for b_idx in range(0, len(train_items), MICRO_BATCH):
            chunk = train_items[b_idx : b_idx + MICRO_BATCH]
            if not chunk:
                continue
            batch = collate_train_batch(chunk, tok.pad_token_id)
            with torch.autocast("cuda", dtype=torch.float16):
                logits, act = model(
                    batch["input_ids"].to(device),
                    batch["attention_mask"].to(device),
                    batch["marker_pos"].to(device),
                    batch["marker_mask"].to(device),
                    batch["qtype"].to(device),
                )
            logits = logits.float()
            mask = batch["marker_mask"].to(device)
            k = mask.sum(-1, keepdim=True).float()
            target = batch["target"].to(device)

            eps = torch.randn((GROUP_SIZE,) + logits.shape, device=device) * sigma * mask
            eps = (eps - eps.sum(-1, keepdim=True) / k) * mask
            z = logits.detach().unsqueeze(0) + eps
            q = torch.softmax(z.masked_fill(~mask, -1e4), -1)

            with torch.no_grad():
                r = proper_reward(q, target.unsqueeze(0), batch["qtype"].to(device), mask, w_sph=0.75, w_rps=1.0)
                adv = r - r.mean(0, keepdim=True)
                adv = adv / (adv.std() + 1e-6)

            logp = -(((z - logits.unsqueeze(0)) ** 2) * mask).sum(-1) / (2 * sigma ** 2)
            loss_rl = -(adv * logp).mean()
            loss_ce = -(target * torch.log_softmax(logits.masked_fill(~mask, -1e4), -1)).sum(-1).mean()
            if args.arm == "ce":
                loss = loss_ce / GRAD_ACCUM
            elif args.arm == "rl":
                loss = loss_rl / GRAD_ACCUM
            else:
                loss = (loss_rl + 1.0 * loss_ce) / GRAD_ACCUM

            scaler.scale(loss).backward()
            accum_step += 1
            if accum_step % GRAD_ACCUM == 0 or (b_idx + MICRO_BATCH) >= len(train_items):
                scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                scaler.step(optimizer)
                scaler.update()
                scheduler.step()
                optimizer.zero_grad(set_to_none=True)
                step_count += 1

            epoch_loss += loss.item() * GRAD_ACCUM
            n_batches += 1
            if n_batches % 50 == 0:
                log(f"  epoch {epoch+1}/{EPOCHS} step {n_batches} loss {loss.item()*GRAD_ACCUM:.4f} reward {r.mean().item():.3f} lr {scheduler.get_last_lr()[0]:.2e} sigma {sigma:.2f}")

            if args.max_steps and step_count >= args.max_steps:
                log(f"SMOKE CAP reached ({step_count} optimizer steps)")
                break
        log(f"=== epoch {epoch+1}/{EPOCHS} done in {time.time()-t0:.1f}s avg_loss {epoch_loss/max(1,n_batches):.4f} ===")
        if args.max_steps and step_count >= args.max_steps:
            break

    train_time = time.time() - t0

    # Post-training temperature calibration on the held-out calib slice (upstream protocol)
    calib_pairs = collect_logits(model, calib_items, tok, device)
    fitted_temps = [1.2, 1.2, 1.2]
    for qt in range(3):
        sel = [(z, t) for q_type, z, t, _ in calib_pairs if q_type == qt]
        if sel:
            fitted_temps[qt] = fit_one_temp(sel)
    log(f"fitted temperatures (choice, score, noul): {[round(t,3) for t in fitted_temps]}")

    after_t1 = metrics_from_logits(collect_logits(model, eval_items, tok, device))
    after_tt = metrics_from_logits(collect_logits(model, eval_items, tok, device), temps=fitted_temps)
    log(f"metrics AFTER (T=1): {json.dumps(after_t1['pooled'])}")
    log(f"metrics AFTER (T=fitted): {json.dumps(after_tt['pooled'])}")

    sd = {k: v.half().contiguous().cpu() for k, v in model.state_dict().items()}
    save_file(sd, os.path.join(out_dir, "model.safetensors"))
    metrics = {
        "arm": args.arm,
        "seed": args.seed,
        "epochs": EPOCHS,
        "n_train": len(train_items),
        "n_eval": len(eval_items),
        "sigma_start": SIGMA_START,
        "sigma_end": SIGMA_END,
        "group_size": GROUP_SIZE,
        "train_time_s": round(train_time, 1),
        "optimizer_steps": step_count,
        "temperatures": fitted_temps,
        "before_T1": before,
        "after_T1": after_t1,
        "after_Tfitted": after_tt,
    }
    with open(os.path.join(out_dir, "metrics.json"), "w") as f:
        json.dump(metrics, f, indent=2)
    log(f"saved {out_dir}/metrics.json")


if __name__ == "__main__":
    main()
