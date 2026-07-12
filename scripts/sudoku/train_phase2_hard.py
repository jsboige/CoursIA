"""
Sudoku RRN Phase 2 — training on hard puzzles (issue #605).

Phase 1 trained on easy puzzles (nakashi104/sudoku-1million, 30-36 givens) and
does not generalise to hard puzzles (sudoku-extreme, 17-36 givens): zero-shot
grid accuracy collapses from 100% (easy) to ~5% (hard). Phase 2 trains on the
hard distribution so the RRN learns the deeper reasoning hard puzzles require.

Key design choices:
  * Canonical encoding (channels 0-8 = digits 1-9, channel 9 = is-given) matching
    scripts/sudoku/core/dataset.py and the Phase 1 checkpoints. The legacy
    sudoku_rrn.py / curriculum_train.py encoding (channel 0 = empty) is NOT
    compatible with the trained checkpoints and is avoided here.
  * Optional warm-start from a Phase 1 checkpoint (finetune) or fresh init.
  * Deep-supervision auxiliary loss over reasoning steps (Palm et al. 2018).
  * RTX 4090 scale: large batch, more reasoning steps, mixed precision.
  * Empty-cell-masked loss and grid accuracy (givens are trivially copied).

Usage:
    python scripts/sudoku/train_phase2_hard.py \
        --train sudoku_models/data_cache/sudoku_extreme_train.npz \
        --test  sudoku_models/data_cache/sudoku_extreme_test.npz \
        --pretrained sudoku_models/checkpoints/finetuned_h256_s16_strat_v2_best.pt \
        --hidden 256 --steps 32 --epochs 30 --batch 256 --seed 42 \
        --save-name phase2_h256_s32_seed42
"""

import os
import sys
import time
import json
import argparse
import numpy as np

import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader

sys.path.insert(0, os.path.dirname(__file__))
from sudoku_rrn import SudokuRRN, build_sudoku_edge_index, make_batch_edge_index

MODELS_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')


# ── Dataset (canonical encoding) ──────────────────────────────────────────────

class HardSudokuDataset(Dataset):
    """Encoding: channels 0-8 = digit 1-9 one-hot, channel 9 = is-given."""

    def __init__(self, puzzles, solutions):
        self.puzzles = puzzles.astype(np.int8)
        self.solutions = solutions.astype(np.int8)

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        p = self.puzzles[idx].astype(np.int64)
        s = self.solutions[idx].astype(np.int64)
        x = np.zeros((81, 10), dtype=np.float32)
        for d in range(1, 10):
            x[:, d - 1] = (p == d)
        x[:, 9] = (p > 0)
        y = (s - 1).astype(np.int64)
        is_given = (p > 0).astype(np.float32)
        return x, y, is_given


def load_npz(path):
    d = np.load(path)
    p = d['puzzles'].astype(np.int64).reshape(-1, 81)
    s = d['solutions'].astype(np.int64).reshape(-1, 81)
    return p, s


# ── Train / eval ──────────────────────────────────────────────────────────────

def train_epoch(model, loader, optimizer, scheduler, edge_index_base, device,
                scaler, aux_weight, grad_accum):
    model.train()
    criterion = nn.CrossEntropyLoss(reduction='none')
    total_loss = 0.0
    total_correct = 0
    total_empty = 0
    n_batches = 0
    optimizer.zero_grad()

    for step_idx, (x, y, is_given) in enumerate(loader):
        x = x.to(device, non_blocking=True)
        y = y.to(device, non_blocking=True)
        is_given = is_given.to(device, non_blocking=True)
        B = x.size(0)

        x_flat = x.reshape(B * 81, 10)
        y_flat = y.reshape(B * 81)
        empty_mask = (is_given.reshape(B * 81) == 0).float()
        edge_index = make_batch_edge_index(edge_index_base, B).to(device)

        with torch.amp.autocast('cuda', enabled=device.type == 'cuda'):
            final_logits, all_logits = model(x_flat, edge_index)
            loss_main = (criterion(final_logits, y_flat) * empty_mask).sum() / empty_mask.sum().clamp(min=1)
            aux = 0.0
            if aux_weight > 0:
                for i, lg in enumerate(all_logits[:-1]):
                    w = aux_weight * (i + 1) / len(all_logits)
                    aux = aux + w * (criterion(lg, y_flat) * empty_mask).sum() / empty_mask.sum().clamp(min=1)
            loss = (loss_main + aux) / grad_accum

        if device.type == 'cuda':
            scaler.scale(loss).backward()
            if (step_idx + 1) % grad_accum == 0:
                scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                scaler.step(optimizer)
                scaler.update()
                optimizer.zero_grad()
                scheduler.step()
        else:
            loss.backward()
            if (step_idx + 1) % grad_accum == 0:
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                optimizer.step()
                optimizer.zero_grad()
                scheduler.step()

        with torch.no_grad():
            preds = final_logits.argmax(dim=-1)
            total_correct += ((preds == y_flat).float() * empty_mask).sum().item()
            total_empty += empty_mask.sum().item()
        total_loss += loss.item() * grad_accum
        n_batches += 1

    return total_loss / max(n_batches, 1), total_correct / max(total_empty, 1)


@torch.no_grad()
def evaluate(model, loader, edge_index_base, device):
    model.eval()
    criterion = nn.CrossEntropyLoss(reduction='none')
    total_loss = 0.0
    correct_empty = 0
    total_empty = 0
    correct_grids = 0
    total_grids = 0
    n_batches = 0

    for x, y, is_given in loader:
        x = x.to(device)
        y = y.to(device)
        is_given = is_given.to(device)
        B = x.size(0)

        x_flat = x.reshape(B * 81, 10)
        y_flat = y.reshape(B * 81)
        empty_mask = (is_given.reshape(B * 81) == 0).float()
        edge_index = make_batch_edge_index(edge_index_base, B).to(device)

        logits, _ = model(x_flat, edge_index)
        total_loss += ((criterion(logits, y_flat) * empty_mask).sum() / empty_mask.sum().clamp(min=1)).item()
        n_batches += 1

        preds = logits.argmax(dim=-1)
        correct_empty += ((preds == y_flat).float() * empty_mask).sum().item()
        total_empty += empty_mask.sum().item()

        preds_grid = preds.reshape(B, 81)
        y_grid = y.reshape(B, 81)
        given_grid = is_given.bool()
        grid_ok = ((preds_grid == y_grid) | given_grid).all(dim=1)
        correct_grids += grid_ok.sum().item()
        total_grids += B

    return {
        'loss': total_loss / max(n_batches, 1),
        'empty_cell_acc': correct_empty / max(total_empty, 1),
        'grid_acc': correct_grids / max(total_grids, 1),
        'correct_grids': correct_grids,
        'total_grids': total_grids,
    }


def main():
    parser = argparse.ArgumentParser(description='Sudoku RRN Phase 2 hard training')
    parser.add_argument('--train', required=True)
    parser.add_argument('--test', required=True)
    parser.add_argument('--pretrained', type=str, default=None,
                        help='Warm-start from a Phase 1 checkpoint (optional)')
    parser.add_argument('--hidden', type=int, default=256)
    parser.add_argument('--steps', type=int, default=32)
    parser.add_argument('--epochs', type=int, default=30)
    parser.add_argument('--batch', type=int, default=256)
    parser.add_argument('--grad-accum', type=int, default=1)
    parser.add_argument('--lr', type=float, default=2e-4)
    parser.add_argument('--aux-weight', type=float, default=0.3)
    parser.add_argument('--dropout', type=float, default=0.1)
    parser.add_argument('--patience', type=int, default=8)
    parser.add_argument('--max-train', type=int, default=None)
    parser.add_argument('--val-frac', type=float, default=0.05)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--save-name', type=str, default='phase2_h256_s32')
    parser.add_argument('--num-workers', type=int, default=4)
    args = parser.parse_args()

    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"Device: {device}")
    if device.type == 'cuda':
        print(f"GPU: {torch.cuda.get_device_name()} "
              f"({torch.cuda.get_device_properties().total_memory/1e9:.1f} GB)")

    torch.manual_seed(args.seed)
    np.random.seed(args.seed)
    torch.backends.cudnn.benchmark = True

    edge_index_base = build_sudoku_edge_index()

    # Data
    train_p, train_s = load_npz(args.train)
    if args.max_train and args.max_train < len(train_p):
        idx = np.random.RandomState(args.seed).choice(len(train_p), args.max_train, replace=False)
        train_p, train_s = train_p[idx], train_s[idx]
    perm = np.random.RandomState(args.seed).permutation(len(train_p))
    train_p, train_s = train_p[perm], train_s[perm]
    n_val = int(len(train_p) * args.val_frac)
    val_p, val_s = train_p[:n_val], train_s[:n_val]
    tr_p, tr_s = train_p[n_val:], train_s[n_val:]
    test_p, test_s = load_npz(args.test)

    g = (tr_p > 0).sum(1)
    print(f"Train: {len(tr_p):,} | Val: {len(val_p):,} | Test: {len(test_p):,}")
    print(f"Train givens: min={g.min()} max={g.max()} mean={g.mean():.1f}")

    train_loader = DataLoader(HardSudokuDataset(tr_p, tr_s), batch_size=args.batch,
                              shuffle=True, num_workers=args.num_workers, pin_memory=True,
                              persistent_workers=args.num_workers > 0, drop_last=True)
    val_loader = DataLoader(HardSudokuDataset(val_p, val_s), batch_size=args.batch * 2,
                            shuffle=False, num_workers=2, pin_memory=True)
    test_loader = DataLoader(HardSudokuDataset(test_p, test_s), batch_size=args.batch * 2,
                             shuffle=False, num_workers=2, pin_memory=True)

    # Model
    model = SudokuRRN(hidden_dim=args.hidden, msg_dim=args.hidden,
                      n_steps=args.steps, dropout=args.dropout).to(device)
    if args.pretrained and os.path.exists(args.pretrained):
        ck = torch.load(args.pretrained, map_location=device, weights_only=False)
        sd = ck['model_state_dict'] if 'model_state_dict' in ck else ck
        # Only load if architecture matches (hidden dim); n_steps can differ (shared weights).
        if sd['input_embed.0.weight'].shape[0] == args.hidden:
            model.load_state_dict(sd, strict=True)
            print(f"Warm-started from {os.path.basename(args.pretrained)} "
                  f"(n_steps {ck.get('config', {}).get('n_steps', '?')} -> {args.steps})")
        else:
            print(f"Pretrained hidden dim mismatch; training from scratch.")
    print(f"Model: h={args.hidden} steps={args.steps} params={model.count_params():,}")

    optimizer = optim.AdamW(model.parameters(), lr=args.lr, weight_decay=1e-4)
    scaler = torch.amp.GradScaler('cuda', enabled=(device.type == 'cuda'))
    steps_per_epoch = max(len(train_loader) // args.grad_accum, 1)
    total_steps = args.epochs * steps_per_epoch
    scheduler = optim.lr_scheduler.OneCycleLR(optimizer, max_lr=args.lr,
                                              total_steps=total_steps, pct_start=0.1,
                                              anneal_strategy='cos')

    save_dir = os.path.join(MODELS_DIR, args.save_name)
    os.makedirs(save_dir, exist_ok=True)
    log_path = os.path.join(save_dir, 'training.log')

    config = vars(args).copy()
    config['params'] = model.count_params()
    results = {'config': config, 'epochs': []}

    print(f"\nPre-training val (warm-start check):")
    pre = evaluate(model, val_loader, edge_index_base, device)
    print(f"  val grid_acc={pre['grid_acc']:.4f} empty_cell_acc={pre['empty_cell_acc']:.4f}")

    best_grid = -1.0
    patience_counter = 0
    t0 = time.time()

    for epoch in range(args.epochs):
        te = time.time()
        tr_loss, tr_acc = train_epoch(model, train_loader, optimizer, scheduler,
                                      edge_index_base, device, scaler,
                                      args.aux_weight, args.grad_accum)
        vm = evaluate(model, val_loader, edge_index_base, device)
        lr_now = optimizer.param_groups[0]['lr']
        line = (f"Epoch {epoch+1:3d}/{args.epochs} | tr_loss={tr_loss:.4f} tr_acc={tr_acc:.4f} | "
                f"val_loss={vm['loss']:.4f} val_cell={vm['empty_cell_acc']:.4f} "
                f"val_grid={vm['grid_acc']:.4f} | lr={lr_now:.2e} | {time.time()-te:.0f}s")
        print(line)
        with open(log_path, 'a') as f:
            f.write(line + '\n')
        results['epochs'].append({'epoch': epoch + 1, 'train_loss': tr_loss,
                                  'train_acc': tr_acc, **vm, 'lr': lr_now})

        if vm['grid_acc'] > best_grid:
            best_grid = vm['grid_acc']
            patience_counter = 0
            torch.save({'epoch': epoch, 'model_state_dict': model.state_dict(),
                        'val_grid_acc': vm['grid_acc'], 'val_cell_acc': vm['empty_cell_acc'],
                        'config': config}, os.path.join(save_dir, 'best_model.pt'))
            print(f"  -> Best saved (val_grid_acc={vm['grid_acc']:.4f})")
        else:
            patience_counter += 1
            if patience_counter >= args.patience:
                print(f"  Early stopping at epoch {epoch+1}.")
                break

    total_time = time.time() - t0
    print(f"\nTraining done in {total_time/60:.1f} min. Best val grid_acc={best_grid:.4f}")

    best = torch.load(os.path.join(save_dir, 'best_model.pt'), map_location=device, weights_only=False)
    model.load_state_dict(best['model_state_dict'])
    test_m = evaluate(model, test_loader, edge_index_base, device)
    print(f"\nTest (hard) zero-shot: grid_acc={test_m['grid_acc']:.4f} "
          f"({test_m['correct_grids']}/{test_m['total_grids']}) "
          f"empty_cell_acc={test_m['empty_cell_acc']:.4f}")

    results['test'] = test_m
    results['total_time_s'] = total_time
    with open(os.path.join(save_dir, 'results.json'), 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Results saved to {save_dir}/")


if __name__ == '__main__':
    main()
