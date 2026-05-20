"""
Thermal-safe Sudoku training script.

Progressive GPU test: small model (h128), batch=8, 4h max.
Uses shared/gpu_training.py for thermal monitoring and checkpointing.

Usage:
    python MyIA.AI.Notebooks/Sudoku/scripts/thermal_safe_train.py [--epochs 50] [--batch-size 8] [--max-hours 4]
"""

import sys
import os
import time
import argparse
import json
import numpy as np

import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'QuantConnect'))
from shared.gpu_training import TrainingCheckpoint, get_gpu_temp, batch_thermal_check


class SudokuDataset(Dataset):
    def __init__(self, X, y):
        self.X = torch.FloatTensor(X).permute(0, 3, 1, 2)
        self.y = torch.LongTensor(y)

    def __len__(self):
        return len(self.X)

    def __getitem__(self, idx):
        return self.X[idx], self.y[idx]


class SmallDenseModel(nn.Module):
    def __init__(self, hidden=128):
        super().__init__()
        self.flatten = nn.Flatten()
        self.network = nn.Sequential(
            nn.Linear(9 * 9 * 10, hidden),
            nn.ReLU(),
            nn.BatchNorm1d(hidden),
            nn.Dropout(0.1),
            nn.Linear(hidden, hidden),
            nn.ReLU(),
            nn.BatchNorm1d(hidden),
            nn.Dropout(0.1),
            nn.Linear(hidden, 9 * 9 * 9)
        )

    def forward(self, x):
        x = self.flatten(x)
        x = self.network(x)
        return x.view(-1, 9, 9, 9).permute(0, 2, 3, 1)


class SmallCNNModel(nn.Module):
    def __init__(self, channels=64):
        super().__init__()
        self.conv_layers = nn.Sequential(
            nn.Conv2d(10, channels, 3, padding=1),
            nn.BatchNorm2d(channels),
            nn.ReLU(),
            nn.Conv2d(channels, channels, 3, padding=1),
            nn.BatchNorm2d(channels),
            nn.ReLU(),
            nn.Conv2d(channels, 9, 1)
        )

    def forward(self, x):
        return self.conv_layers(x).permute(0, 2, 3, 1)


def generate_sudoku_data(n_samples, seed=42):
    rng = np.random.RandomState(seed)
    X = rng.randint(0, 10, size=(n_samples, 9, 9))
    y = np.clip(X, 1, 9)

    X_encoded = np.zeros((n_samples, 9, 9, 10), dtype=np.float32)
    for i in range(n_samples):
        for r in range(9):
            for c in range(9):
                X_encoded[i, r, c, X[i, r, c]] = 1.0

    y_encoded = (y - 1).astype(np.int64)
    return X_encoded, y_encoded


def train_one_epoch(model, loader, optimizer, criterion, device, scaler, epoch_id, max_temp=88):
    model.train()
    total_loss = 0.0
    correct_cells = 0
    total_cells = 0

    for batch_idx, (X_batch, y_batch) in enumerate(loader):
        X_batch, y_batch = X_batch.to(device), y_batch.to(device)

        optimizer.zero_grad()
        with torch.amp.autocast('cuda', enabled=scaler is not None):
            output = model(X_batch)
            loss = criterion(output.reshape(-1, 9), y_batch.reshape(-1))

        if scaler is not None:
            scaler.scale(loss).backward()
            scaler.step(optimizer)
            scaler.update()
        else:
            loss.backward()
            optimizer.step()

        total_loss += loss.item()
        preds = output.argmax(dim=-1)
        correct_cells += (preds == y_batch).sum().item()
        total_cells += y_batch.numel()

        if batch_idx % 10 == 0:
            batch_thermal_check(batch_idx, check_every=10, max_temp=max_temp)

    return total_loss / len(loader), correct_cells / total_cells


@torch.no_grad()
def evaluate(model, loader, criterion, device):
    model.eval()
    total_loss = 0.0
    correct_cells = 0
    total_cells = 0
    complete_grids = 0

    for X_batch, y_batch in loader:
        X_batch, y_batch = X_batch.to(device), y_batch.to(device)
        output = model(X_batch)
        loss = criterion(output.reshape(-1, 9), y_batch.reshape(-1))

        total_loss += loss.item()
        preds = output.argmax(dim=-1)
        correct_cells += (preds == y_batch).sum().item()
        total_cells += y_batch.numel()
        complete_grids += (preds == y_batch).all(dim=-1).all(dim=-1).sum().item()

    return {
        'loss': total_loss / len(loader),
        'cell_acc': correct_cells / total_cells,
        'grid_acc': complete_grids / len(loader.dataset)
    }


def main():
    parser = argparse.ArgumentParser(description='Thermal-safe Sudoku training')
    parser.add_argument('--epochs', type=int, default=50)
    parser.add_argument('--batch-size', type=int, default=8)
    parser.add_argument('--hidden', type=int, default=128)
    parser.add_argument('--samples', type=int, default=2000)
    parser.add_argument('--max-hours', type=float, default=4.0)
    parser.add_argument('--model', choices=['dense', 'cnn'], default='dense')
    parser.add_argument('--max-temp', type=int, default=88)
    parser.add_argument('--checkpoint-dir', default='checkpoints')
    args = parser.parse_args()

    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"[INIT] Device: {device}")
    if device.type == 'cuda':
        temp = get_gpu_temp()
        print(f"[INIT] GPU temp: {temp}C")

    print(f"[INIT] Generating {args.samples} samples...")
    X, y = generate_sudoku_data(args.samples)
    split = int(0.8 * args.samples)
    train_ds = SudokuDataset(X[:split], y[:split])
    test_ds = SudokuDataset(X[split:], y[split:])
    train_loader = DataLoader(train_ds, batch_size=args.batch_size, shuffle=True)
    test_loader = DataLoader(test_ds, batch_size=args.batch_size)

    if args.model == 'dense':
        model = SmallDenseModel(hidden=args.hidden).to(device)
    else:
        model = SmallCNNModel(channels=args.hidden).to(device)

    param_count = sum(p.numel() for p in model.parameters())
    print(f"[INIT] Model: {args.model}, params: {param_count:,}")

    optimizer = optim.Adam(model.parameters(), lr=1e-3)
    scaler = torch.amp.GradScaler('cuda', enabled=(device.type == 'cuda'))
    criterion = nn.CrossEntropyLoss()

    os.makedirs(args.checkpoint_dir, exist_ok=True)
    ckpt = TrainingCheckpoint(
        checkpoint_path=os.path.join(args.checkpoint_dir, 'sudoku_ckpt.pt'),
        model_save_path=os.path.join(args.checkpoint_dir, 'sudoku_final.pt'),
        max_temp=args.max_temp,
        cool_sleep=15
    )
    start_epoch, _ckpt_history = ckpt.resume(model, optimizer, None, scaler)
    history = []

    max_seconds = args.max_hours * 3600
    start_time = time.time()

    print(f"[TRAIN] Starting epoch {start_epoch}, max {args.epochs} epochs, {args.max_hours}h limit")
    print(f"[TRAIN] batch_size={args.batch_size}, hidden={args.hidden}, max_temp={args.max_temp}C")

    for epoch in range(start_epoch, args.epochs):
        elapsed = time.time() - start_time
        if elapsed > max_seconds:
            print(f"[STOP] Time limit reached: {elapsed/3600:.1f}h / {args.max_hours}h")
            break

        ckpt.thermal_check()

        t0 = time.time()
        train_loss, train_acc = train_one_epoch(
            model, train_loader, optimizer, criterion, device, scaler, epoch,
            max_temp=args.max_temp
        )
        val_metrics = evaluate(model, test_loader, criterion, device)
        epoch_time = time.time() - t0

        temp = get_gpu_temp() if device.type == 'cuda' else 0

        history_entry = {
            'epoch': epoch,
            'train_loss': train_loss,
            'train_acc': train_acc,
            'val_loss': val_metrics['loss'],
            'cell_acc': val_metrics['cell_acc'],
            'grid_acc': val_metrics['grid_acc'],
            'epoch_time': epoch_time,
            'gpu_temp': temp,
            'elapsed_h': (time.time() - start_time) / 3600
        }
        history.append(history_entry)

        ckpt.update(epoch, val_metrics['loss'], history, model, optimizer, None, scaler)

        print(
            f"[E{epoch:03d}] loss={train_loss:.4f} "
            f"cell_acc={val_metrics['cell_acc']:.3f} "
            f"grid_acc={val_metrics['grid_acc']:.3f} "
            f"t={epoch_time:.1f}s gpu={temp}C "
            f"elapsed={history_entry['elapsed_h']:.2f}h"
        )

    ckpt.finalize(model)
    elapsed = time.time() - start_time

    report = {
        'total_epochs': len(history),
        'total_hours': elapsed / 3600,
        'final_cell_acc': history[-1]['cell_acc'] if history else 0,
        'final_grid_acc': history[-1]['grid_acc'] if history else 0,
        'max_gpu_temp': max(h.get('gpu_temp', 0) for h in history) if history else 0,
        'crashes': 0,
        'history': history
    }

    report_path = os.path.join(args.checkpoint_dir, 'training_report.json')
    with open(report_path, 'w') as f:
        json.dump(report, f, indent=2, default=str)

    print(f"\n[DONE] {len(history)} epochs in {elapsed/3600:.2f}h")
    print(f"[DONE] Final cell_acc={report['final_cell_acc']:.3f}, grid_acc={report['final_grid_acc']:.3f}")
    print(f"[DONE] Max GPU temp: {report['max_gpu_temp']}C")
    print(f"[DONE] Report saved: {report_path}")


if __name__ == '__main__':
    main()
