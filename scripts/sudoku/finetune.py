"""
Sudoku RRN Fine-Tuning Script
==============================
Load a pre-trained checkpoint and continue training on combined easy+hard data
with curriculum learning (easy puzzles first).

Strategy:
  Phase 1: Train on easy data (HF 1M, ~34 givens) with low LR
  Phase 2: Progressive hard data injection (diverse_200k, ~26 givens)
  Phase 3: Mixed curriculum (easy + medium + hard)

Usage:
  python scripts/sudoku_finetune.py --checkpoint sudoku_models/sweep_h256_s16_best.pt
  python scripts/sudoku_finetune.py --checkpoint sudoku_models/sweep_h128_s16_best.pt --phase curriculum
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
from torch.amp import GradScaler, autocast

# Import from core modules
sys.path.insert(0, os.path.dirname(__file__))
from core import (
    SudokuRRN, build_sudoku_edge_index, make_batch_edge_index,
    SudokuGraphDataset, sudoku_collate_fn, evaluate, generate_puzzles,
)

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
MODELS_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
DATA_DIR = os.path.join(MODELS_DIR, 'data_cache')


# ── Data loading utilities ────────────────────────────────────────────────────

def load_hf_1k(max_puzzles=None):
    """Load HF 1M dataset (easy, ~34 givens). Shape: (N, 9, 9) -> flatten to (N, 81)."""
    path = os.path.join(DATA_DIR, 'puzzles_hf_1000000.npz')
    if not os.path.exists(path):
        print(f"  HF 1M not found at {path}")
        return None, None
    data = np.load(path)
    puzzles = data['puzzles'].reshape(-1, 81)  # (N, 81)
    solutions = data['solutions'].reshape(-1, 81)
    if max_puzzles and max_puzzles < len(puzzles):
        idx = np.random.choice(len(puzzles), max_puzzles, replace=False)
        puzzles = puzzles[idx]
        solutions = solutions[idx]
    return puzzles, solutions


def load_diverse_200k():
    """Load diverse_200k dataset (hard, ~26 givens)."""
    path = os.path.join(DATA_DIR, 'diverse_200k.npz')
    if not os.path.exists(path):
        print(f"  diverse_200k not found at {path}")
        return None, None
    data = np.load(path)
    key = list(data.keys())[0]
    puzzles_flat = data[key]
    # Need solutions - check if there's a solutions key
    if 'solutions' in data:
        solutions = data['solutions']
    else:
        # diverse_200k only has puzzles, need to solve them
        print("  WARNING: diverse_200k has no solutions, skipping")
        return None, None
    return puzzles_flat, solutions


def load_kaggle_1m(max_puzzles=None):
    """Load Kaggle 1M dataset (easy/medium, ~34 givens)."""
    path = 'C:/Users/jsboi/.cache/kagglehub/datasets/bryanpark/sudoku/versions/3/sudoku.csv'
    if not os.path.exists(path):
        print(f"  Kaggle 1M not found at {path}")
        return None, None
    import pandas as pd
    df = pd.read_csv(path, nrows=max_puzzles)
    puzzles = np.array([[int(c) for c in q] for q in df['quizzes']], dtype=np.int64)
    solutions = np.array([[int(c) for c in s] for s in df['solutions']], dtype=np.int64)
    return puzzles, solutions


def build_combined_dataset(n_easy=300000, n_hard=100000, n_generated=100000,
                           val_ratio=0.15, test_ratio=0.15, seed=42):
    """Build a combined dataset with diverse difficulty levels.

    Sources:
    - Easy: HF 1M or Kaggle (30-37 givens)
    - Hard: diverse_200k (17-37 givens) — if solutions available
    - Generated: puzzle generator (30-55 empty cells, diverse)
    """
    rng = np.random.RandomState(seed)
    all_puzzles = []
    all_solutions = []

    # Easy data (HF 1M)
    print(f"  Loading HF 1M (easy, taking {n_easy:,})...")
    p, s = load_hf_1k(max_puzzles=n_easy)
    if p is not None:
        idx = rng.choice(len(p), min(n_easy, len(p)), replace=False)
        all_puzzles.append(p[idx])
        all_solutions.append(s[idx])
        givens = (p[idx] > 0).sum(axis=1)
        print(f"    {len(p[idx]):,} puzzles, givens: {givens.mean():.1f} avg")

    # Hard data (diverse_200k) — only if solutions exist
    p, s = load_diverse_200k()
    if p is not None and s is not None:
        n_use = min(n_hard, len(p))
        idx = rng.choice(len(p), n_use, replace=False)
        all_puzzles.append(p[idx])
        all_solutions.append(s[idx])
        givens = (p[idx] > 0).sum(axis=1)
        print(f"    +{n_use:,} hard puzzles, givens: {givens.mean():.1f} avg")

    # Generated medium puzzles
    if n_generated > 0:
        print(f"  Generating {n_generated:,} puzzles...")
        gen_p, gen_s = generate_puzzles(n_generated, n_empty_range=(25, 50), seed=seed)
        all_puzzles.append(gen_p)
        all_solutions.append(gen_s)
        givens = (gen_p > 0).sum(axis=1)
        print(f"    +{n_generated:,} generated, givens: {givens.mean():.1f} avg")

    # Combine
    puzzles = np.concatenate(all_puzzles, axis=0)
    solutions = np.concatenate(all_solutions, axis=0)
    print(f"  Total: {len(puzzles):,} puzzles")

    # Stratified split FIRST (preserve difficulty mix in each split)
    n = len(puzzles)
    perm = rng.permutation(n)
    n_test = int(n * test_ratio)
    n_val = int(n * val_ratio)
    n_train = n - n_test - n_val

    test_idx = perm[:n_test]
    val_idx = perm[n_test:n_test+n_val]
    train_idx = perm[n_test+n_val:]

    train_p, train_s = puzzles[train_idx], solutions[train_idx]
    val_p, val_s = puzzles[val_idx], solutions[val_idx]
    test_p, test_s = puzzles[test_idx], solutions[test_idx]

    # Classify train puzzles into difficulty buckets
    train_givens = (train_p > 0).sum(axis=1)
    easy_mask = train_givens >= 33
    medium_mask = (train_givens >= 25) & (train_givens < 33)
    hard_mask = train_givens < 25

    # Shuffle within each bucket (don't sort by difficulty)
    for mask in [easy_mask, medium_mask, hard_mask]:
        idx = np.where(mask)[0]
        rng.shuffle(idx)

    # Report
    val_givens = (val_p > 0).sum(axis=1)
    test_givens = (test_p > 0).sum(axis=1)
    print(f"  Split: {n_train:,} train / {n_val:,} val / {n_test:,} test")
    print(f"  Train: {easy_mask.sum():,} easy (33+) / {medium_mask.sum():,} medium (25-32) / {hard_mask.sum():,} hard (<25)")
    print(f"  Val givens: {val_givens.min()}-{val_givens.max()}, mean={val_givens.mean():.1f}")
    print(f"  Test givens: {test_givens.min()}-{test_givens.max()}, mean={test_givens.mean():.1f}")

    return train_p, train_s, val_p, val_s, test_p, test_s, (easy_mask, medium_mask, hard_mask)


# ── Curriculum schedulers ─────────────────────────────────────────────────────

class StratifiedCurriculumDataset(Dataset):
    """Dataset that samples from difficulty buckets with adjustable ratios.

    Each curriculum phase defines what fraction of each bucket to include.
    Uses epoch-based seed so the model sees different puzzles each epoch
    while maintaining the same difficulty distribution within a phase.
    """
    def __init__(self, puzzles, solutions, bucket_masks, ratios=(1.0, 1.0, 1.0), epoch=1):
        """
        Args:
            bucket_masks: tuple of (easy_mask, medium_mask, hard_mask) boolean arrays
            ratios: tuple of (easy_frac, medium_frac, hard_frac) — fraction to sample from each bucket
            epoch: used as seed offset so each epoch sees different examples
        """
        rng = np.random.RandomState(epoch * 1000)
        easy_mask, medium_mask, hard_mask = bucket_masks
        indices = []
        for mask, frac in zip([easy_mask, medium_mask, hard_mask], ratios):
            bucket_idx = np.where(mask)[0]
            n_take = max(1, int(len(bucket_idx) * frac))
            perm = rng.permutation(bucket_idx)
            indices.append(perm[:n_take])

        all_idx = np.concatenate(indices)
        rng.shuffle(all_idx)
        self.puzzles = puzzles[all_idx]
        self.solutions = solutions[all_idx]

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        return self.puzzles[idx], self.solutions[idx]


# ── Fine-tuning functions ─────────────────────────────────────────────────────

def finetune(model, train_p, train_s, val_p, val_s, base_edges,
             n_epochs=40, patience=10, lr=1e-4, batch_size=64,
             save_path='finetuned_best.pt', curriculum_schedule=None,
             bucket_masks=None):
    """Fine-tune a pre-trained model.

    Args:
        curriculum_schedule: list of (epoch, (easy_frac, medium_frac, hard_frac)) tuples.
            At epoch E, sample the given fraction from each difficulty bucket.
            None = use all data.
        bucket_masks: tuple of (easy_mask, medium_mask, hard_mask) for stratified sampling.
    """
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    scheduler = optim.lr_scheduler.OneCycleLR(
        optimizer, max_lr=lr, epochs=n_epochs,
        steps_per_epoch=len(range(0, len(train_p), batch_size)),
        pct_start=0.1,
    )
    criterion = nn.CrossEntropyLoss(reduction='none')
    scaler = GradScaler('cuda')
    base_edges = base_edges.to(device)

    best_val_loss = float('inf')
    best_epoch = 0
    best_val_acc = 0
    patience_counter = 0
    history = []

    print(f"\nFine-tuning for up to {n_epochs} epochs (patience={patience})")
    print(f"LR: {lr} | Scheduler: OneCycleLR | Optimizer: AdamW")
    print(f"Curriculum: {curriculum_schedule or 'none (full data)'}")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
        # Curriculum: determine bucket ratios
        if curriculum_schedule and bucket_masks is not None:
            ratios = (1.0, 1.0, 1.0)
            for sched_epoch, sched_ratios in curriculum_schedule:
                if epoch >= sched_epoch:
                    ratios = sched_ratios
        else:
            ratios = (1.0, 1.0, 1.0)
            bucket_masks = (
                np.ones(len(train_p), dtype=bool),
                np.zeros(len(train_p), dtype=bool),
                np.zeros(len(train_p), dtype=bool),
            )

        # Build loader for current curriculum stratified subset (fresh samples each epoch)
        train_ds = StratifiedCurriculumDataset(train_p, train_s, bucket_masks, ratios=ratios, epoch=epoch)
        train_loader = DataLoader(train_ds, batch_size=batch_size, shuffle=True,
                                  collate_fn=sudoku_collate_fn, num_workers=0,
                                  pin_memory=True)

        val_ds = SudokuGraphDataset(val_p, val_s)
        val_loader = DataLoader(val_ds, batch_size=batch_size, shuffle=False,
                                collate_fn=sudoku_collate_fn, num_workers=0,
                                pin_memory=True)

        model.train()
        train_loss_sum = 0
        train_correct = 0
        train_total = 0
        t0 = time.time()

        for batch_x, batch_y, batch_given in train_loader:
            batch_x = batch_x.to(device)
            batch_y = batch_y.to(device)
            batch_given = batch_given.to(device)
            bs = batch_x.size(0)
            edge_index = make_batch_edge_index(base_edges, bs)
            empty = (1.0 - batch_given)
            empty_flat = empty.view(-1)

            optimizer.zero_grad()
            with autocast('cuda'):
                logits_list = model(batch_x, edge_index)
                step_losses = []
                for logits in logits_list:
                    per_cell = criterion(logits.reshape(-1, 9), batch_y.reshape(-1))
                    masked = per_cell * empty_flat
                    step_loss = masked.sum() / empty_flat.sum().clamp(min=1)
                    step_losses.append(step_loss)
                loss = torch.stack(step_losses).mean()

            scaler.scale(loss).backward()
            scaler.unscale_(optimizer)
            torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
            scaler.step(optimizer)
            scaler.update()
            scheduler.step()

            train_loss_sum += loss.item() * bs
            last_logits = logits_list[-1]
            preds = last_logits.argmax(dim=-1)
            correct = (preds == batch_y).float() * empty
            train_correct += correct.sum().item()
            train_total += empty.sum().item()

        train_loss = train_loss_sum / len(train_loader.dataset)
        train_acc = train_correct / train_total if train_total > 0 else 0

        # Validation
        model.eval()
        val_loss_sum = 0
        val_correct = 0
        val_total = 0

        with torch.no_grad():
            for batch_x, batch_y, batch_given in val_loader:
                batch_x = batch_x.to(device)
                batch_y = batch_y.to(device)
                batch_given = batch_given.to(device)
                bs = batch_x.size(0)
                edge_index = make_batch_edge_index(base_edges, bs)
                empty = (1.0 - batch_given)
                empty_flat = empty.view(-1)

                with autocast('cuda'):
                    logits_list = model(batch_x, edge_index)
                    step_losses = []
                    for logits in logits_list:
                        per_cell = criterion(logits.reshape(-1, 9), batch_y.reshape(-1))
                        masked = per_cell * empty_flat
                        step_loss = masked.sum() / empty_flat.sum().clamp(min=1)
                        step_losses.append(step_loss)
                    val_loss = torch.stack(step_losses).mean()

                val_loss_sum += val_loss.item() * bs
                last_logits = logits_list[-1]
                preds = last_logits.argmax(dim=-1)
                correct = (preds == batch_y).float() * empty
                val_correct += correct.sum().item()
                val_total += empty.sum().item()

        val_loss_avg = val_loss_sum / len(val_loader.dataset)
        val_acc = val_correct / val_total if val_total > 0 else 0
        elapsed = time.time() - t0
        current_lr = optimizer.param_groups[0]['lr']

        n_train_cur = len(train_ds)
        ratio_str = f"e={ratios[0]:.0%}/m={ratios[1]:.0%}/h={ratios[2]:.0%}" if curriculum_schedule else "full"
        print(f"Epoch {epoch:3d}/{n_epochs} | "
              f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
              f"val_loss={val_loss_avg:.4f} acc={val_acc:.4f} | "
              f"lr={current_lr:.2e} | {elapsed:.1f}s | {n_train_cur:,} samples ({ratio_str})")

        history.append({
            'epoch': epoch, 'train_loss': train_loss, 'train_acc': train_acc,
            'val_loss': val_loss_avg, 'val_acc': val_acc, 'lr': current_lr,
            'n_train_samples': n_train_cur, 'ratios': ratios,
        })

        if val_loss_avg < best_val_loss:
            best_val_loss = val_loss_avg
            best_val_acc = val_acc
            best_epoch = epoch
            patience_counter = 0
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'val_loss': val_loss_avg,
                'val_acc': val_acc,
            }, save_path)
            print(f"  -> Best model saved (val_loss={val_loss_avg:.4f}, val_acc={val_acc:.4f})")
        else:
            patience_counter += 1
            if patience_counter >= patience:
                print(f"\nEarly stopping at epoch {epoch}. Best: epoch {best_epoch}")
                break

    # Load best
    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    print(f"Loaded best model from epoch {ckpt['epoch']} (val_loss={ckpt['val_loss']:.4f})")
    return model, history


# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description='Fine-tune Sudoku RRN')
    parser.add_argument('--checkpoint', type=str, required=True,
                        help='Path to pre-trained checkpoint (.pt)')
    parser.add_argument('--phase', type=str, default='curriculum',
                        choices=['easy', 'hard', 'curriculum'],
                        help='Fine-tuning phase strategy')
    parser.add_argument('--lr', type=float, default=1e-4, help='Learning rate')
    parser.add_argument('--epochs', type=int, default=40, help='Max epochs')
    parser.add_argument('--patience', type=int, default=10, help='Early stopping patience')
    parser.add_argument('--batch-size', type=int, default=64, help='Batch size')
    parser.add_argument('--n-easy', type=int, default=300000, help='Number of easy puzzles')
    parser.add_argument('--n-hard', type=int, default=100000, help='Number of hard puzzles')
    parser.add_argument('--n-generated', type=int, default=100000, help='Number of generated puzzles')
    parser.add_argument('--hidden-dim', type=int, default=None,
                        help='Override hidden dim (auto-detected from checkpoint)')
    parser.add_argument('--n-steps', type=int, default=None,
                        help='Override reasoning steps (auto-detected from checkpoint)')
    parser.add_argument('--output-suffix', type=str, default='', help='Suffix for output files')
    args = parser.parse_args()

    print("=" * 70)
    print("SUDOKU RRN FINE-TUNING")
    print("=" * 70)

    # Load checkpoint to detect architecture
    print(f"\nLoading checkpoint: {args.checkpoint}")
    ckpt = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    print(f"  Epoch: {ckpt.get('epoch', '?')}, val_loss: {ckpt.get('val_loss', '?'):.4f}, "
          f"val_acc: {ckpt.get('val_acc', '?'):.4f}")

    # Auto-detect architecture from state dict
    state = ckpt['model_state_dict']
    hidden_dim = args.hidden_dim or state['gru.weight_ih'].shape[1]
    msg_dim = state['msg_mlp.0.weight'].shape[0]
    n_steps = args.n_steps or 16  # Can't auto-detect from weights
    print(f"  Architecture: h={hidden_dim}, msg={msg_dim}, steps={n_steps}")

    # Build model and load weights
    model = SudokuRRN(hidden_dim=hidden_dim, msg_dim=msg_dim, n_steps=n_steps, dropout=0.1).to(device)
    model.load_state_dict(state)
    n_params = sum(p.numel() for p in model.parameters())
    print(f"  Model loaded: {n_params:,} params")

    # Build dataset
    print(f"\nBuilding combined dataset...")
    print(f"  Phase: {args.phase}")
    train_p, train_s, val_p, val_s, test_p, test_s, bucket_masks = build_combined_dataset(
        n_easy=args.n_easy, n_hard=args.n_hard, n_generated=args.n_generated,
    )

    base_edges = build_sudoku_edge_index()

    # Curriculum schedule: (epoch, (easy_frac, medium_frac, hard_frac))
    # Each phase has a mix of difficulties, progressively adding harder puzzles
    if args.phase == 'curriculum':
        # Stratified curriculum: always keep easy + medium present, increase hard gradually
        # Epoch  1-5:  50% easy + 30% medium + 10% hard  (varied mix from the start)
        # Epoch  6-11: 75% easy + 60% medium + 40% hard  (more medium + hard)
        # Epoch 12-17: 90% easy + 80% medium + 70% hard  (most data)
        # Epoch 18+:   all easy + all medium + all hard   (full dataset)
        # Note: each epoch resamples different puzzles from each bucket (epoch-based seed)
        curriculum_schedule = [
            (1,  (0.50, 0.30, 0.10)),
            (6,  (0.75, 0.60, 0.40)),
            (12, (0.90, 0.80, 0.70)),
            (18, (1.00, 1.00, 1.00)),
        ]
    else:
        curriculum_schedule = None

    # Fine-tune
    suffix = args.output_suffix or f"_{args.phase}"
    save_path = os.path.join(MODELS_DIR, f'finetuned_h{hidden_dim}_s{n_steps}{suffix}_best.pt')
    print(f"\nSave path: {save_path}")

    model, history = finetune(
        model, train_p, train_s, val_p, val_s, base_edges,
        n_epochs=args.epochs, patience=args.patience, lr=args.lr,
        batch_size=args.batch_size, save_path=save_path,
        curriculum_schedule=curriculum_schedule,
        bucket_masks=bucket_masks,
    )

    # Evaluate on test set
    print("\n" + "=" * 70)
    print("EVALUATION ON TEST SET")
    print("=" * 70)
    cell_acc, grid_acc, test_loss = evaluate(
        model, test_p, test_s, base_edges, device, batch_size=args.batch_size,
    )
    n_solved = int(grid_acc * len(test_p))
    print(f"Cell accuracy: {cell_acc:.4f}")
    print(f"Grid accuracy: {grid_acc:.4f} ({n_solved}/{len(test_p)})")
    print(f"Test loss: {test_loss:.4f}")

    # Save results
    results = {
        'checkpoint': args.checkpoint,
        'phase': args.phase,
        'architecture': {'hidden_dim': hidden_dim, 'msg_dim': msg_dim,
                         'n_steps': n_steps, 'n_params': n_params},
        'dataset': {'n_easy': args.n_easy, 'n_hard': args.n_hard,
                    'n_generated': args.n_generated,
                    'n_train': len(train_p), 'n_val': len(val_p), 'n_test': len(test_p)},
        'training': {'lr': args.lr, 'epochs': len(history), 'best_epoch': history[-1]['epoch'] if history else 0,
                     'curriculum': curriculum_schedule},
        'results': {'cell_acc': float(cell_acc), 'grid_acc': float(grid_acc),
                    'test_loss': float(test_loss), 'n_solved': int(n_solved)},
        'history_summary': history[::max(1, len(history)//8)] if len(history) > 8 else history,
    }
    results_path = os.path.join(MODELS_DIR, f'finetuned_h{hidden_dim}_s{n_steps}{suffix}_results.json')
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {results_path}")

    # GPU cleanup
    if torch.cuda.is_available():
        torch.cuda.empty_cache()


if __name__ == '__main__':
    main()
