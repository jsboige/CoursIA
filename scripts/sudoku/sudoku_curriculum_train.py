"""
Sudoku RRN Curriculum Training.

Finetune a pretrained model with stratified curriculum on diverse_400k (hard puzzles).
Progressive difficulty: start easy → add hard puzzles progressively.

Usage:
    python scripts/sudoku/sudoku_curriculum_train.py [--pretrained PATH] [--epochs N]
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
from torch.utils.data import Dataset, DataLoader, WeightedRandomSampler

sys.path.insert(0, os.path.dirname(__file__))
from sudoku_rrn import SudokuRRN, build_sudoku_edge_index, make_batch_edge_index

MODELS_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'sudoku_models')
DATA_DIR = os.path.join(MODELS_DIR, 'data_cache')


class SudokuDataset(Dataset):
    def __init__(self, puzzles, solutions, givens=None):
        self.puzzles = puzzles
        self.solutions = solutions
        self.givens = givens

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        p = self.puzzles[idx]
        s = self.solutions[idx]
        x = np.zeros((81, 10), dtype=np.float32)
        for i in range(81):
            x[i, int(p[i])] = 1.0
        y = (s - 1).astype(np.int64)
        n_empty = int(np.sum(p == 0))
        return x, y, n_empty


class CurriculumSampler:
    """Stratified curriculum that progressively includes harder puzzles."""

    def __init__(self, givens, curriculum_schedule):
        """
        Args:
            givens: array of givens count per puzzle
            curriculum_schedule: list of (epoch, (easy_pct, medium_pct, hard_pct))
                easy = givens >= 30
                medium = givens 23-29
                hard = givens <= 22
        """
        self.givens = givens
        self.schedule = curriculum_schedule
        self.easy_idx = np.where(givens >= 30)[0]
        self.medium_idx = np.where((givens >= 23) & (givens < 30))[0]
        self.hard_idx = np.where(givens < 23)[0]
        print(f"  Difficulty buckets: easy={len(self.easy_idx)}, "
              f"medium={len(self.medium_idx)}, hard={len(self.hard_idx)}")

    def get_indices(self, epoch):
        """Get training indices for this epoch based on curriculum schedule."""
        pct = (1.0, 1.0, 1.0)
        for sched_epoch, sched_pct in self.schedule:
            if epoch >= sched_epoch:
                pct = sched_pct

        easy_n = int(len(self.easy_idx) * pct[0])
        med_n = int(len(self.medium_idx) * pct[1])
        hard_n = int(len(self.hard_idx) * pct[2])

        indices = np.concatenate([
            np.random.choice(self.easy_idx, easy_n, replace=False) if easy_n > 0 else np.array([], dtype=int),
            np.random.choice(self.medium_idx, med_n, replace=False) if med_n > 0 else np.array([], dtype=int),
            np.random.choice(self.hard_idx, hard_n, replace=False) if hard_n > 0 else np.array([], dtype=int),
        ])
        np.random.shuffle(indices)
        return indices


def load_curriculum_data():
    """Load diverse_400k (hard) dataset for curriculum training."""
    path = os.path.join(DATA_DIR, 'diverse_400k.npz')
    if not os.path.exists(path):
        raise FileNotFoundError(f"diverse_400k.npz not found at {path}")

    d = np.load(path)
    puzzles = d['puzzles'].reshape(-1, 81)
    solutions = d['solutions'].reshape(-1, 81)
    givens = (puzzles > 0).sum(axis=1)

    print(f"Loaded diverse_400k: {len(puzzles)} puzzles, "
          f"givens {givens.min()}-{givens.max()}, mean={givens.mean():.1f}")

    # Also load easy puzzles for curriculum mixing
    easy_path = os.path.join(DATA_DIR, 'puzzles_hf_1000000.npz')
    if os.path.exists(easy_path):
        d2 = np.load(easy_path)
        easy_puzzles = d2['puzzles'].reshape(-1, 81)
        easy_solutions = d2['solutions'].reshape(-1, 81)
        # Take 100K easy puzzles for balance
        n_easy = min(100000, len(easy_puzzles))
        idx = np.random.choice(len(easy_puzzles), n_easy, replace=False)
        easy_puzzles = easy_puzzles[idx]
        easy_solutions = easy_solutions[idx]
        easy_givens = (easy_puzzles > 0).sum(axis=1)

        puzzles = np.concatenate([puzzles, easy_puzzles])
        solutions = np.concatenate([solutions, easy_solutions])
        givens = np.concatenate([givens, easy_givens])

        print(f"  + {n_easy} easy puzzles (mean givens {easy_givens.mean():.1f})")
        print(f"  Total: {len(puzzles)} puzzles")

    # Shuffle and split 70/15/15
    n = len(puzzles)
    perm = np.random.permutation(n)
    puzzles, solutions, givens = puzzles[perm], solutions[perm], givens[perm]

    i_val = int(n * 0.7)
    i_test = int(n * 0.85)

    splits = {
        'train': (puzzles[:i_val], solutions[:i_val], givens[:i_val]),
        'val': (puzzles[i_val:i_test], solutions[i_val:i_test], givens[i_val:i_test]),
        'test': (puzzles[i_test:], solutions[i_test:], givens[i_test:]),
    }

    for k, (p, s, g) in splits.items():
        print(f"  {k}: {len(p)} puzzles, givens {g.min()}-{g.max()}, mean={g.mean():.1f}")

    return splits


def train_epoch_curriculum(model, train_puzzles, train_solutions, train_givens,
                           sampler, epoch, optimizer, scheduler, edge_index_base,
                           device, scaler, config):
    """Train one epoch with curriculum-sampled data."""
    model.train()

    indices = sampler.get_indices(epoch)
    if len(indices) == 0:
        return 0.0, 0.0

    epoch_puzzles = train_puzzles[indices]
    epoch_solutions = train_solutions[indices]

    ds = SudokuDataset(epoch_puzzles, epoch_solutions)
    loader = DataLoader(ds, batch_size=config['batch_size'], shuffle=True,
                        num_workers=0, pin_memory=True)

    total_loss = 0
    total_correct = 0
    total_cells = 0
    n_batches = 0
    criterion = nn.CrossEntropyLoss(reduction='none')
    aux_weight = config.get('aux_weight', 0.3)
    grad_accum = config.get('grad_accum', 1)

    for step_idx, (x, y, n_empty) in enumerate(loader):
        x = x.to(device)
        y = y.to(device)
        B = x.size(0)

        x_flat = x.reshape(B * 81, 10)
        y_flat = y.reshape(B * 81)
        edge_index = make_batch_edge_index(edge_index_base, B).to(device)

        empty_mask = (x[:, :, 0] == 1.0)
        mask_flat = empty_mask.reshape(B * 81)

        with torch.amp.autocast('cuda', enabled=device.type == 'cuda'):
            final_logits, all_logits = model(x_flat, edge_index)

            loss_per_cell = criterion(final_logits, y_flat)
            masked_loss = (loss_per_cell * mask_flat).sum() / mask_flat.sum().clamp(min=1)

            aux_loss = 0
            if aux_weight > 0:
                for i, logits in enumerate(all_logits[:-1]):
                    weight = aux_weight * (i + 1) / len(all_logits)
                    step_loss = criterion(logits, y_flat)
                    aux_loss += weight * (step_loss * mask_flat).sum() / mask_flat.sum().clamp(min=1)

            loss = (masked_loss + aux_loss) / grad_accum

        with torch.no_grad():
            preds = final_logits.argmax(dim=-1)
            correct = ((preds == y_flat) & mask_flat).sum().item()
            total_correct += correct
            total_cells += mask_flat.sum().item()

        if device.type == 'cuda':
            scaler.scale(loss).backward()
            if (step_idx + 1) % grad_accum == 0:
                scaler.unscale_(optimizer)
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                scaler.step(optimizer)
                scaler.update()
                optimizer.zero_grad()
                scheduler.step()
            del final_logits, all_logits, preds
            torch.cuda.empty_cache()
        else:
            loss.backward()
            if (step_idx + 1) % grad_accum == 0:
                torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
                optimizer.step()
                optimizer.zero_grad()
                scheduler.step()

        total_loss += loss.item() * grad_accum
        n_batches += 1

    pct = (1.0, 1.0, 1.0)
    for sched_epoch, sched_pct in sampler.schedule:
        if epoch >= sched_epoch:
            pct = sched_pct

    n_samples = len(indices)
    print(f"    {n_samples:,} samples (e={pct[0]:.0%}/m={pct[1]:.0%}/h={pct[2]:.0%})")

    return total_loss / n_batches, total_correct / max(total_cells, 1)


@torch.no_grad()
@torch.no_grad()
def evaluate(model, loader, edge_index_base, device):
    model.eval()
    total_loss = 0
    total_correct_cells = 0
    total_cells = 0
    correct_grids = 0
    total_grids = 0
    n_batches = 0
    criterion = nn.CrossEntropyLoss(reduction='none')

    for x, y, n_empty in loader:
        x = x.to(device)
        y = y.to(device)
        B = x.size(0)

        x_flat = x.reshape(B * 81, 10)
        y_flat = y.reshape(B * 81)
        edge_index = make_batch_edge_index(edge_index_base, B).to(device)

        empty_mask = (x[:, :, 0] == 1.0)
        mask_flat = empty_mask.reshape(B * 81)

        logits, _ = model(x_flat, edge_index)

        loss_per_cell = criterion(logits, y_flat)
        masked_loss = (loss_per_cell * mask_flat).sum() / mask_flat.sum().clamp(min=1)
        total_loss += masked_loss.item()
        n_batches += 1

        preds = logits.argmax(dim=-1)
        correct = ((preds == y_flat) & mask_flat).sum().item()
        total_correct_cells += correct
        total_cells += mask_flat.sum().item()

        preds_grid = preds.reshape(B, 81)
        y_grid = y.reshape(B, 81)
        mask_grid = empty_mask
        grid_ok = ((preds_grid == y_grid) | ~mask_grid).all(dim=1)
        correct_grids += grid_ok.sum().item()
        total_grids += B

    return {
        'loss': total_loss / n_batches,
        'cell_acc': total_correct_cells / max(total_cells, 1),
        'grid_acc': correct_grids / total_grids,
        'correct_grids': correct_grids,
        'total_grids': total_grids,
    }


@torch.no_grad()
def evaluate_by_difficulty(model, puzzles, solutions, givens, edge_index_base, device, batch_size=8):
    """Evaluate model broken down by difficulty buckets."""
    model.eval()
    buckets = {
        'easy (30+)': np.where(givens >= 30)[0],
        'medium (23-29)': np.where((givens >= 23) & (givens < 30))[0],
        'hard (17-22)': np.where(givens < 23)[0],
    }
    results = {}
    for name, idx in buckets.items():
        if len(idx) == 0:
            continue
        ds = SudokuDataset(puzzles[idx], solutions[idx])
        loader = DataLoader(ds, batch_size=batch_size, shuffle=False, num_workers=0, pin_memory=True)
        metrics = evaluate(model, loader, edge_index_base, device)
        results[name] = {
            'n': len(idx),
            'cell_acc': metrics['cell_acc'],
            'grid_acc': metrics['grid_acc'],
        }
    return results


def main():
    parser = argparse.ArgumentParser(description='Sudoku RRN Curriculum Training')
    parser.add_argument('--pretrained', type=str,
                        default=os.path.join(MODELS_DIR, 'track_a_h256_s24', 'best_model.pt'),
                        help='Path to pretrained model checkpoint')
    parser.add_argument('--epochs', type=int, default=80,
                        help='Max number of training epochs')
    parser.add_argument('--patience', type=int, default=20,
                        help='Early stopping patience')
    parser.add_argument('--lr', type=float, default=1e-4,
                        help='Learning rate')
    parser.add_argument('--batch_size', type=int, default=12,
                        help='Batch size')
    parser.add_argument('--grad_accum', type=int, default=2,
                        help='Gradient accumulation steps')
    parser.add_argument('--save_name', type=str, default='curriculum_h256_s24',
                        help='Model save directory name')
    parser.add_argument('--resume', action='store_true',
                        help='Resume from checkpoint')
    args = parser.parse_args()

    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"Device: {device}")
    if device.type == 'cuda':
        print(f"GPU: {torch.cuda.get_device_name()}")
        print(f"VRAM: {torch.cuda.get_device_properties().total_memory / 1e9:.1f} GB")

    torch.manual_seed(42)
    np.random.seed(42)
    torch.backends.cudnn.benchmark = True

    edge_index_base = build_sudoku_edge_index()

    # Load pretrained model
    print(f"\nLoading pretrained model: {args.pretrained}")
    ckpt = torch.load(args.pretrained, map_location=device, weights_only=False)
    config = ckpt.get('config', {})
    hidden_dim = config.get('hidden_dim', 256)
    msg_dim = config.get('msg_dim', 256)
    n_steps = config.get('n_steps', 24)
    dropout = config.get('dropout', 0.1)

    model = SudokuRRN(
        hidden_dim=hidden_dim,
        msg_dim=msg_dim,
        n_steps=n_steps,
        dropout=dropout,
    ).to(device)

    state_dict_key = 'model_state_dict' if 'model_state_dict' in ckpt else None
    model.load_state_dict(ckpt[state_dict_key] if state_dict_key else ckpt)
    print(f"  Architecture: h={hidden_dim}, msg={msg_dim}, steps={n_steps}")
    print(f"  Params: {model.count_params():,}")
    print(f"  Pretrained: epoch {ckpt.get('epoch', '?')}, "
          f"val_grid_acc={ckpt.get('val_grid_acc', '?')}")

    # Load curriculum data
    print(f"\nBuilding curriculum dataset...")
    splits = load_curriculum_data()

    train_puzzles, train_solutions, train_givens = splits['train']
    val_puzzles, val_solutions, val_givens = splits['val']
    test_puzzles, test_solutions, test_givens = splits['test']

    # Curriculum schedule: 5 phases
    # Phase 1 (epoch 0-4):  60% easy, 30% medium, 10% hard — warm up
    # Phase 2 (epoch 5-9):  80% easy, 60% medium, 30% hard — add medium
    # Phase 3 (epoch 10-19): 90% easy, 80% medium, 60% hard — ramp hard
    # Phase 4 (epoch 20-34): 100% easy, 100% medium, 90% hard — almost full
    # Phase 5 (epoch 35+):   100% all — full difficulty
    curriculum_schedule = [
        (0,  (0.6, 0.3, 0.1)),
        (5,  (0.8, 0.6, 0.3)),
        (10, (0.9, 0.8, 0.6)),
        (20, (1.0, 1.0, 0.9)),
        (35, (1.0, 1.0, 1.0)),
    ]

    sampler = CurriculumSampler(train_givens, curriculum_schedule)

    # Validation/test loaders (full data, no curriculum)
    val_ds = SudokuDataset(val_puzzles, val_solutions)
    val_loader = DataLoader(val_ds, batch_size=args.batch_size, shuffle=False,
                            num_workers=0, pin_memory=True)
    test_ds = SudokuDataset(test_puzzles, test_solutions)
    test_loader = DataLoader(test_ds, batch_size=args.batch_size * 2, shuffle=False,
                             num_workers=0, pin_memory=True)

    # Optimizer setup
    save_dir = os.path.join(MODELS_DIR, args.save_name)
    os.makedirs(save_dir, exist_ok=True)
    log_path = os.path.join(save_dir, 'training.log')

    start_epoch = 0
    best_val_loss = float('inf')
    best_val_grid = 0.0

    optimizer = optim.AdamW(model.parameters(), lr=args.lr, weight_decay=1e-4)
    scaler = torch.amp.GradScaler('cuda', enabled=(device.type == 'cuda'))

    train_config = {
        'pretrained': args.pretrained,
        'hidden_dim': hidden_dim, 'msg_dim': msg_dim, 'n_steps': n_steps,
        'dropout': dropout, 'lr': args.lr, 'batch_size': args.batch_size,
        'grad_accum': args.grad_accum, 'n_epochs': args.epochs,
        'patience': args.patience, 'curriculum_schedule': curriculum_schedule,
    }

    if args.resume:
        resume_path = os.path.join(save_dir, 'best_model.pt')
        if os.path.exists(resume_path):
            rckpt = torch.load(resume_path, map_location=device, weights_only=False)
            model.load_state_dict(rckpt['model_state_dict'])
            optimizer.load_state_dict(rckpt['optimizer_state_dict'])
            start_epoch = rckpt.get('epoch', 0) + 1
            best_val_loss = rckpt.get('val_loss', float('inf'))
            best_val_grid = rckpt.get('val_grid_acc', 0.0)
            print(f"  Resumed from epoch {start_epoch}, val_loss={best_val_loss:.4f}")

    # Estimate steps for scheduler
    est_steps_per_epoch = len(train_puzzles) // args.batch_size // args.grad_accum
    total_steps = args.epochs * est_steps_per_epoch
    scheduler = optim.lr_scheduler.OneCycleLR(
        optimizer, max_lr=args.lr, total_steps=total_steps,
        pct_start=0.1, anneal_strategy='cos'
    )

    print(f"\n{'='*70}")
    print(f"CURRICULUM TRAINING: {args.save_name}")
    print(f"  Pretrained: {os.path.basename(args.pretrained)}")
    print(f"  Params: {model.count_params():,}")
    print(f"  LR: {args.lr} | Epochs: {args.epochs} | Patience: {args.patience}")
    print(f"  Batch: {args.batch_size} | Grad accum: {args.grad_accum}")
    print(f"  Schedule: {len(curriculum_schedule)} phases")
    print(f"{'='*70}")

    patience_counter = 0
    results = {'config': train_config, 'epochs': []}

    # Pre-training evaluation
    print(f"\nPre-training evaluation on val set:")
    pre_metrics = evaluate(model, val_loader, edge_index_base, device)
    print(f"  val_loss={pre_metrics['loss']:.4f} cell_acc={pre_metrics['cell_acc']:.4f} "
          f"grid_acc={pre_metrics['grid_acc']:.4f}")

    pre_diff = evaluate_by_difficulty(model, val_puzzles, val_solutions, val_givens,
                                       edge_index_base, device)
    for name, m in pre_diff.items():
        print(f"  {name}: cell={m['cell_acc']:.4f} grid={m['grid_acc']:.4f} ({m['n']} puzzles)")

    del pre_metrics, pre_diff
    if device.type == 'cuda':
        torch.cuda.empty_cache()

    t0 = time.time()

    for epoch in range(start_epoch, args.epochs):
        t_epoch = time.time()

        train_loss, train_acc = train_epoch_curriculum(
            model, train_puzzles, train_solutions, train_givens,
            sampler, epoch, optimizer, scheduler, edge_index_base,
            device, scaler, train_config,
        )

        val_metrics = evaluate(model, val_loader, edge_index_base, device)
        if device.type == 'cuda':
            torch.cuda.empty_cache()

        elapsed = time.time() - t_epoch
        lr_now = optimizer.param_groups[0]['lr']

        epoch_info = {
            'epoch': epoch + 1,
            'train_loss': train_loss,
            'train_acc': train_acc,
            'val_loss': val_metrics['loss'],
            'val_acc': val_metrics['cell_acc'],
            'val_grid_acc': val_metrics['grid_acc'],
            'lr': lr_now,
            'time_s': elapsed,
        }
        results['epochs'].append(epoch_info)

        log_line = (f"Epoch {epoch+1:3d}/{args.epochs} | "
                    f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
                    f"val_loss={val_metrics['loss']:.4f} acc={val_metrics['cell_acc']:.4f} "
                    f"grid={val_metrics['grid_acc']:.4f} | "
                    f"lr={lr_now:.2e} | {elapsed:.0f}s")

        print(log_line)
        with open(log_path, 'a') as f:
            f.write(log_line + '\n')

        # Save best model
        if val_metrics['loss'] < best_val_loss:
            best_val_loss = val_metrics['loss']
            best_val_grid = val_metrics['grid_acc']
            patience_counter = 0
            save_path = os.path.join(save_dir, 'best_model.pt')
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'val_loss': val_metrics['loss'],
                'val_acc': val_metrics['cell_acc'],
                'val_grid_acc': val_metrics['grid_acc'],
                'config': train_config,
            }, save_path)
            print(f"  -> Best saved (val_loss={val_metrics['loss']:.4f}, "
                  f"grid_acc={val_metrics['grid_acc']:.4f})")
        else:
            patience_counter += 1

        # Periodic difficulty breakdown (every 10 epochs)
        if (epoch + 1) % 10 == 0:
            diff = evaluate_by_difficulty(model, val_puzzles, val_solutions, val_givens,
                                           edge_index_base, device)
            for name, m in diff.items():
                print(f"    {name}: cell={m['cell_acc']:.4f} grid={m['grid_acc']:.4f}")

        if patience_counter >= args.patience:
            print(f"  Early stopping at epoch {epoch+1}. Best: val_loss={best_val_loss:.4f}")
            break

        # GPU cleanup
        if device.type == 'cuda':
            torch.cuda.empty_cache()

    # Final evaluation
    total_time = time.time() - t0

    print(f"\n{'='*70}")
    print("CURRICULUM TRAINING COMPLETE")
    print(f"  Total time: {total_time:.0f}s ({total_time/3600:.1f}h)")

    best_ckpt = torch.load(os.path.join(save_dir, 'best_model.pt'), map_location=device, weights_only=False)
    model.load_state_dict(best_ckpt['model_state_dict'])

    print(f"\nTest set evaluation:")
    test_metrics = evaluate(model, test_loader, edge_index_base, device)
    print(f"  Cell accuracy: {test_metrics['cell_acc']:.4f}")
    print(f"  Grid accuracy: {test_metrics['grid_acc']:.4f} "
          f"({test_metrics['correct_grids']}/{test_metrics['total_grids']})")
    print(f"  Test loss: {test_metrics['loss']:.4f}")

    print(f"\nDifficulty breakdown (test):")
    test_diff = evaluate_by_difficulty(model, test_puzzles, test_solutions, test_givens,
                                        edge_index_base, device)
    for name, m in test_diff.items():
        print(f"  {name}: cell={m['cell_acc']:.4f} grid={m['grid_acc']:.4f} ({m['n']} puzzles)")

    results['test'] = test_metrics
    results['test_by_difficulty'] = test_diff
    results['total_time_s'] = total_time

    with open(os.path.join(save_dir, 'results.json'), 'w') as f:
        json.dump(results, f, indent=2, default=str)

    print(f"\nResults saved to {save_dir}/")
    print(f"{'='*70}")


if __name__ == '__main__':
    main()
