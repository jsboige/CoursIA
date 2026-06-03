"""Training loop for Sudoku RRN."""

import time
import torch
import torch.nn as nn
import torch.optim as optim
from torch.amp import GradScaler, autocast

from .graph import make_batch_edge_index


def train_rrn(model, train_loader, val_loader, base_edges, device,
              n_epochs=80, patience=12, lr=3e-4, save_path='sudoku_rrn_v4_best.pt'):
    """Train SudokuRRN with OneCycleLR + masked cross-entropy at every step."""
    optimizer = optim.AdamW(model.parameters(), lr=lr, weight_decay=1e-4)
    scheduler = optim.lr_scheduler.OneCycleLR(
        optimizer, max_lr=lr, epochs=n_epochs,
        steps_per_epoch=len(train_loader), pct_start=0.1,
    )
    criterion = nn.CrossEntropyLoss(reduction='none')
    scaler = GradScaler('cuda')
    base_edges = base_edges.to(device)

    best_val_loss = float('inf')
    best_epoch = 0
    best_val_acc = 0
    patience_counter = 0
    history = []

    print(f"\nTraining RRN for up to {n_epochs} epochs (patience={patience})")
    print(f"LR: {lr} | Scheduler: OneCycleLR | Optimizer: AdamW")
    print(f"Loss: masked CrossEntropy at every step (averaged over steps)")
    print("-" * 70)

    for epoch in range(1, n_epochs + 1):
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
                    per_cell = criterion(
                        logits.reshape(-1, 9),
                        batch_y.reshape(-1),
                    )
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
                    val_batch_loss = torch.stack(step_losses).mean()

                val_loss_sum += val_batch_loss.item() * bs

                last_logits = logits_list[-1]
                preds = last_logits.argmax(dim=-1)
                correct = (preds == batch_y).float() * empty
                val_correct += correct.sum().item()
                val_total += empty.sum().item()

        val_loss = val_loss_sum / len(val_loader.dataset)
        val_acc = val_correct / val_total if val_total > 0 else 0
        elapsed = time.time() - t0
        current_lr = optimizer.param_groups[0]['lr']

        print(f"Epoch {epoch:3d}/{n_epochs} | "
              f"train_loss={train_loss:.4f} acc={train_acc:.4f} | "
              f"val_loss={val_loss:.4f} acc={val_acc:.4f} | "
              f"lr={current_lr:.2e} | {elapsed:.1f}s")

        history.append({
            'epoch': epoch,
            'train_loss': train_loss,
            'train_acc': train_acc,
            'val_loss': val_loss,
            'val_acc': val_acc,
            'lr': current_lr,
        })

        if val_loss < best_val_loss:
            best_val_loss = val_loss
            best_val_acc = val_acc
            best_epoch = epoch
            patience_counter = 0
            torch.save({
                'epoch': epoch,
                'model_state_dict': model.state_dict(),
                'val_loss': val_loss,
                'val_acc': val_acc,
            }, save_path)
            print(f"  -> Best model saved (val_loss={val_loss:.4f}, val_acc={val_acc:.4f})")
        else:
            patience_counter += 1
            if patience_counter >= patience:
                print(f"\nEarly stopping at epoch {epoch}. Best: epoch {best_epoch}")
                break

    ckpt = torch.load(save_path, weights_only=False)
    model.load_state_dict(ckpt['model_state_dict'])
    print(f"Loaded best model from epoch {ckpt['epoch']} (val_loss={ckpt['val_loss']:.4f})")

    return model, history
