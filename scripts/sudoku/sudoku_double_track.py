"""
Sudoku RRN Double-Track Training Pipeline.

Track A: h256_s24 — larger model, slow warmup, curriculum finetuning
Track B: h192_s32 — deeper message-passing, aggressive passes

Between trainings: slow LR warmup (cosine ramp from 1e-5 to max_lr).
Within trainings: fast passes at max_lr with OneCycle scheduling.

Usage:
    python scripts/sudoku/sudoku_double_track.py [--track A|B|both] [--resume]
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
DATA_DIR = os.path.join(MODELS_DIR, 'data_cache')


# ── Dataset ──────────────────────────────────────────────────────────────────

class SudokuDataset(Dataset):
    def __init__(self, puzzles, solutions):
        self.puzzles = puzzles
        self.solutions = solutions

    def __len__(self):
        return len(self.puzzles)

    def __getitem__(self, idx):
        p = self.puzzles[idx]
        s = self.solutions[idx]
        # One-hot encode puzzle (10 channels: 0=empty, 1-9=digits)
        x = np.zeros((81, 10), dtype=np.float32)
        for i in range(81):
            x[i, int(p[i])] = 1.0
        # Target: 0-8 indices for cross-entropy
        y = (s - 1).astype(np.int64)
        return x, y, int(np.sum(p == 0))


def load_data(data_file, max_samples=None, difficulty_split=False):
    """Load sudoku data from npz file."""
    path = os.path.join(DATA_DIR, data_file)
    d = np.load(path)
    puzzles = d['puzzles'].reshape(-1, 81)
    solutions = d['solutions'].reshape(-1, 81)

    if max_samples and max_samples < len(puzzles):
        idx = np.random.choice(len(puzzles), max_samples, replace=False)
        puzzles = puzzles[idx]
        solutions = solutions[idx]

    # Compute givens count for stratification
    givens = (puzzles > 0).sum(axis=1)

    # Split 70/15/15
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


# ── Training ─────────────────────────────────────────────────────────────────

def train_epoch(model, loader, optimizer, scheduler, edge_index_base, device, scaler,
                aux_weight=0.3, curriculum_mask=None, grad_accum=1):
    model.train()
    total_loss = 0
    total_correct = 0
    total_cells = 0
    n_batches = 0

    criterion = nn.CrossEntropyLoss(reduction='none')

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
            correct = ((preds == y_flat) & mask_flat).sum().item()
            total_correct += correct
            total_cells += mask_flat.sum().item()

        total_loss += loss.item() * grad_accum
        n_batches += 1

    return total_loss / n_batches, total_correct / max(total_cells, 1)


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

        # Grid accuracy
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


def run_track(config, edge_index_base, splits, device, resume_path=None):
    """Run one training track with slow warmup + fast passes."""
    model = SudokuRRN(
        hidden_dim=config['hidden_dim'],
        msg_dim=config['msg_dim'],
        n_steps=config['n_steps'],
        dropout=config['dropout'],
    ).to(device)

    start_epoch = 0
    best_val_loss = float('inf')

    if resume_path and os.path.exists(resume_path):
        ckpt = torch.load(resume_path, map_location=device, weights_only=False)
        model.load_state_dict(ckpt['model_state_dict'] if 'model_state_dict' in ckpt else ckpt)
        if 'epoch' in ckpt:
            start_epoch = ckpt['epoch'] + 1
        if 'val_loss' in ckpt:
            best_val_loss = ckpt['val_loss']
        print(f"  Resumed from epoch {start_epoch}, val_loss={best_val_loss:.4f}")

    print(f"  Model: {model.count_params():,} params")
    print(f"  Config: {config['name']} h={config['hidden_dim']} s={config['n_steps']}")

    # Data
    train_ds = SudokuDataset(*splits['train'][:2])
    val_ds = SudokuDataset(*splits['val'][:2])
    test_ds = SudokuDataset(*splits['test'][:2])

    train_loader = DataLoader(train_ds, batch_size=config['batch_size'], shuffle=True,
                              num_workers=0, pin_memory=True)
    val_loader = DataLoader(val_ds, batch_size=config['batch_size'] * 2, shuffle=False,
                            num_workers=0, pin_memory=True)
    test_loader = DataLoader(test_ds, batch_size=config['batch_size'] * 2, shuffle=False,
                             num_workers=0, pin_memory=True)

    grad_accum = config.get('grad_accum', 1)
    total_steps = config['n_epochs'] * (len(train_loader) // grad_accum)
    optimizer = optim.AdamW(model.parameters(), lr=config['max_lr'], weight_decay=1e-4)
    scaler = torch.amp.GradScaler('cuda', enabled=(device.type == 'cuda'))

    # Phase 1: Slow warmup (10% of total steps, ramp from 1e-5 to max_lr)
    warmup_steps = int(total_steps * 0.1)
    # Phase 2: Fast passes at max_lr with cosine decay
    remaining_steps = total_steps - warmup_steps

    def lr_lambda(step):
        if step < warmup_steps:
            return (step + 1) / warmup_steps
        else:
            progress = (step - warmup_steps) / max(remaining_steps, 1)
            return 0.5 * (1 + np.cos(np.pi * progress))

    scheduler = optim.lr_scheduler.LambdaLR(optimizer, lr_lambda)

    save_dir = os.path.join(MODELS_DIR, config['name'])
    os.makedirs(save_dir, exist_ok=True)
    log_path = os.path.join(save_dir, 'training.log')
    results = {'config': config, 'epochs': []}

    patience = config['patience']
    patience_counter = 0

    print(f"\n{'='*70}")
    print(f"TRACK: {config['name']} | {model.count_params():,} params")
    print(f"LR: warmup {config['max_lr']/10:.1e} -> {config['max_lr']:.1e} (10%) then cosine")
    print(f"Epochs: {config['n_epochs']} | Patience: {patience}")
    print(f"{'='*70}")

    t0 = time.time()

    for epoch in range(start_epoch, config['n_epochs']):
        t_epoch = time.time()

        train_loss, train_acc = train_epoch(
            model, train_loader, optimizer, scheduler, edge_index_base, device, scaler,
            aux_weight=config.get('aux_weight', 0.3),
            grad_accum=config.get('grad_accum', 1),
        )

        val_metrics = evaluate(model, val_loader, edge_index_base, device)

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

        log_line = (f"Epoch {epoch+1:3d}/{config['n_epochs']} | "
                    f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
                    f"val_loss={val_metrics['loss']:.4f} acc={val_metrics['cell_acc']:.4f} "
                    f"grid={val_metrics['grid_acc']:.4f} | "
                    f"lr={lr_now:.2e} | {elapsed:.0f}s")

        print(log_line)
        with open(log_path, 'a') as f:
            f.write(log_line + '\n')

        # Save best
        if val_metrics['loss'] < best_val_loss:
            best_val_loss = val_metrics['loss']
            patience_counter = 0
            save_path = os.path.join(save_dir, 'best_model.pt')
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'optimizer_state_dict': optimizer.state_dict(),
                'val_loss': val_metrics['loss'],
                'val_acc': val_metrics['cell_acc'],
                'val_grid_acc': val_metrics['grid_acc'],
                'config': config,
            }, save_path)
            print(f"  -> Best model saved (val_loss={val_metrics['loss']:.4f}, "
                  f"grid_acc={val_metrics['grid_acc']:.4f})")
        else:
            patience_counter += 1

        if patience_counter >= patience:
            print(f"  Early stopping at epoch {epoch+1}. Best: val_loss={best_val_loss:.4f}")
            break

    # Final test evaluation
    best_ckpt = torch.load(os.path.join(save_dir, 'best_model.pt'), map_location=device, weights_only=False)
    model.load_state_dict(best_ckpt['model_state_dict'])
    test_metrics = evaluate(model, test_loader, edge_index_base, device)

    total_time = time.time() - t0
    print(f"\n{'='*70}")
    print(f"TRACK {config['name']} COMPLETE")
    print(f"  Cell accuracy: {test_metrics['cell_acc']:.4f}")
    print(f"  Grid accuracy: {test_metrics['grid_acc']:.4f} ({test_metrics['correct_grids']}/{test_metrics['total_grids']})")
    print(f"  Test loss: {test_metrics['loss']:.4f}")
    print(f"  Total time: {total_time:.0f}s ({total_time/3600:.1f}h)")
    print(f"{'='*70}")

    results['test'] = test_metrics
    results['total_time_s'] = total_time

    with open(os.path.join(save_dir, 'results.json'), 'w') as f:
        json.dump(results, f, indent=2, default=str)

    return results


# ── Track Definitions ────────────────────────────────────────────────────────

TRACK_A = {
    'name': 'track_a_h256_s24',
    'hidden_dim': 256,
    'msg_dim': 256,
    'n_steps': 24,
    'dropout': 0.1,
    'batch_size': 16,
    'grad_accum': 3,
    'max_lr': 3e-4,
    'n_epochs': 60,
    'patience': 15,
    'aux_weight': 0.3,
    'data_file': 'puzzles_hf_1000000.npz',
    'max_samples': 400000,
}

TRACK_B = {
    'name': 'track_b_h192_s32',
    'hidden_dim': 192,
    'msg_dim': 192,
    'n_steps': 32,
    'dropout': 0.15,
    'batch_size': 16,
    'grad_accum': 4,
    'max_lr': 5e-4,
    'n_epochs': 50,
    'patience': 12,
    'aux_weight': 0.4,
    'data_file': 'puzzles_hf_1000000.npz',
    'max_samples': 400000,
}


def main():
    parser = argparse.ArgumentParser(description='Sudoku RRN Double-Track Training')
    parser.add_argument('--track', choices=['A', 'B', 'both'], default='both',
                        help='Which track to run')
    parser.add_argument('--resume', action='store_true',
                        help='Resume from checkpoint if available')
    parser.add_argument('--quick', action='store_true',
                        help='Quick test run (10 epochs, small data)')
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
    print(f"Edge index: {edge_index_base.shape[1]} edges (bidirectional)")

    tracks = []
    if args.track in ('A', 'both'):
        tracks.append(('A', TRACK_A))
    if args.track in ('B', 'both'):
        tracks.append(('B', TRACK_B))

    all_results = {}

    for label, config in tracks:
        print(f"\n{'#'*70}")
        print(f"# TRACK {label}: {config['name']}")
        print(f"{'#'*70}")

        if args.quick:
            config = {**config, 'n_epochs': 10, 'patience': 5, 'max_samples': 20000}

        print(f"\nLoading data: {config['data_file']}")
        splits = load_data(config['data_file'], config.get('max_samples'))

        resume_path = None
        if args.resume:
            candidate = os.path.join(MODELS_DIR, config['name'], 'best_model.pt')
            if os.path.exists(candidate):
                resume_path = candidate

        results = run_track(config, edge_index_base, splits, device, resume_path)
        all_results[label] = results

        # Clear GPU cache between tracks
        if device.type == 'cuda':
            torch.cuda.empty_cache()

    # Summary
    print(f"\n{'='*70}")
    print("DOUBLE-TRACK TRAINING SUMMARY")
    print(f"{'='*70}")
    for label, results in all_results.items():
        test = results.get('test', {})
        print(f"Track {label} ({results['config']['name']}): "
              f"cell_acc={test.get('cell_acc', 0):.4f} "
              f"grid_acc={test.get('grid_acc', 0):.4f} "
              f"({test.get('correct_grids', '?')}/{test.get('total_grids', '?')})")

    with open(os.path.join(MODELS_DIR, 'double_track_summary.json'), 'w') as f:
        json.dump(all_results, f, indent=2, default=str)


if __name__ == '__main__':
    main()
