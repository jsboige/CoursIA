"""
Sudoku RRN Phase 2 — Iterative refinement solver + evaluator.

Phase 1 inference is zero-shot: a single forward pass through the RRN, then
argmax per empty cell. Even a well-trained RRN has a per-cell error rate that
compounds over ~55 empty cells on hard puzzles, capping grid accuracy.

Phase 2 inference adds confidence-based iterative refinement (issue #605 goal 3):
  1. Run the RRN forward pass.
  2. Fill ONLY the most confident empty cells (above a confidence threshold,
     and only if the prediction is constraint-valid given the current grid).
  3. Re-encode the now-larger set of givens and run the RRN again.
  4. Repeat until solved or no progress; the threshold decays so harder cells
     get committed in later rounds. A naked-single constraint-propagation pass
     fills any cell with a single valid candidate regardless of NN confidence.

This adapts the solver strategies from the (archived) CNN-era iterative_eval.py
to the RRN one-hot graph input format. The RRN itself is unchanged.

Usage:
    python scripts/sudoku/phase2_iterative.py --checkpoint <path> \
        --data sudoku_models/data_cache/sudoku_extreme_test.npz \
        --n-steps 16 --n-eval 2000

Outputs JSON with zero-shot and iterative grid/cell accuracy.
"""

import os
import sys
import json
import time
import argparse
import numpy as np

import torch
import torch.nn.functional as F

sys.path.insert(0, os.path.dirname(__file__))
from sudoku_rrn import SudokuRRN, build_sudoku_edge_index, make_batch_edge_index


# ── Encoding ──────────────────────────────────────────────────────────────────

def onehot_batch(puzzles):
    """Encode (B,81) int puzzles into (B,81,10) one-hot.

    Canonical RRN encoding (matches scripts/sudoku/core/dataset.py, the format the
    Phase 1 checkpoints were trained with): channels 0-8 = digits 1-9 one-hot,
    channel 9 = is-given flag. Empty cells are all-zero in channels 0-8.
    """
    B = puzzles.shape[0]
    p = puzzles.astype(np.int64)
    x = np.zeros((B, 81, 10), dtype=np.float32)
    for d in range(1, 10):
        x[:, :, d - 1] = (p == d)
    x[:, :, 9] = (p > 0)
    return x


# ── Constraint helpers (vectorised over a batch) ──────────────────────────────

def valid_candidate_mask(grids):
    """For a batch of (B,81) grids return (B,81,9) bool: digit d (1..9) legal at cell.

    A digit is legal at an empty cell if it does not already appear in the cell's
    row, column or 3x3 block. Filled cells get all-False (no candidate needed).
    """
    B = grids.shape[0]
    g = grids.reshape(B, 9, 9)
    mask = np.ones((B, 9, 9, 9), dtype=bool)  # (B, row, col, digit-1)

    for d in range(1, 10):
        present = (g == d)  # (B,9,9)
        row_has = present.any(axis=2)            # (B,9)
        col_has = present.any(axis=1)            # (B,9)
        blk = present.reshape(B, 3, 3, 3, 3)
        blk_has = blk.any(axis=(2, 4))           # (B,3,3)
        blk_full = np.repeat(np.repeat(blk_has, 3, axis=1), 3, axis=2)  # (B,9,9)
        illegal = row_has[:, :, None] | col_has[:, None, :] | blk_full
        mask[:, :, :, d - 1] &= ~illegal

    filled = (g > 0)
    mask[filled] = False
    return mask.reshape(B, 81, 9)


# ── RRN forward (probabilities) ───────────────────────────────────────────────

@torch.no_grad()
def rrn_probs(model, puzzles, edge_index_base, device, batch_size=512):
    """Return (N,81,9) softmax probabilities from a single RRN forward pass."""
    model.eval()
    N = puzzles.shape[0]
    out = np.zeros((N, 81, 9), dtype=np.float32)
    for i in range(0, N, batch_size):
        chunk = puzzles[i:i + batch_size]
        B = chunk.shape[0]
        x = torch.from_numpy(onehot_batch(chunk)).to(device)
        x_flat = x.reshape(B * 81, 10)
        edge_index = make_batch_edge_index(edge_index_base, B).to(device)
        with torch.amp.autocast('cuda', enabled=device.type == 'cuda'):
            final_logits, _ = model(x_flat, edge_index)
        probs = F.softmax(final_logits.float(), dim=-1).reshape(B, 81, 9)
        out[i:i + B] = probs.cpu().numpy()
    return out


# ── Evaluators ────────────────────────────────────────────────────────────────

def eval_zero_shot(model, puzzles, solutions, edge_index_base, device, batch_size=512):
    """Single forward pass, argmax on empty cells. Grid + empty-cell accuracy."""
    N = puzzles.shape[0]
    probs = rrn_probs(model, puzzles, edge_index_base, device, batch_size)
    preds = probs.argmax(axis=-1) + 1          # (N,81) digits 1..9
    empty = (puzzles == 0)
    filled = (puzzles > 0)
    pred_full = np.where(empty, preds, puzzles)
    correct_empty = ((pred_full == solutions) & empty).sum()
    total_empty = empty.sum()
    grid_ok = ((pred_full == solutions) | filled).all(axis=1)
    return {
        'empty_cell_acc': float(correct_empty / max(total_empty, 1)),
        'grid_acc': float(grid_ok.mean()),
        'solved': int(grid_ok.sum()),
        'total': int(N),
    }


def solve_iterative(model, puzzles, solutions, edge_index_base, device,
                    max_rounds=40, init_threshold=0.95, decay=0.93,
                    min_threshold=0.30, batch_size=512, use_naked_singles=True):
    """Confidence-based iterative refinement over a batch of puzzles.

    Each round: forward pass -> fill constraint-valid cells above threshold ->
    re-encode. Naked singles (single legal candidate) are filled first. Threshold
    decays so stubborn cells commit later. Returns grid/cell accuracy.
    """
    grids = puzzles.copy().astype(np.int64)
    N = grids.shape[0]
    active = np.ones(N, dtype=bool)  # puzzles still being solved
    threshold = init_threshold

    for _ in range(max_rounds):
        empty_any = (grids == 0).any(axis=1)
        active &= empty_any
        if not active.any():
            break

        cand = valid_candidate_mask(grids)          # (N,81,9) legal digits

        # Naked singles: empty cell with exactly one legal candidate.
        if use_naked_singles:
            n_cand = cand.sum(axis=-1)              # (N,81)
            singles = (grids == 0) & (n_cand == 1)
            if singles.any():
                single_digit = cand.argmax(axis=-1) + 1
                grids[singles] = single_digit[singles]
                # Recompute after structural fills before NN step.
                continue

        probs = rrn_probs(model, grids[active], edge_index_base, device, batch_size)
        # Restrict probabilities to legal candidates; renormalise.
        cand_active = cand[active]
        masked = probs * cand_active
        denom = masked.sum(axis=-1, keepdims=True)
        masked = np.where(denom > 0, masked / np.clip(denom, 1e-9, None), probs)

        conf = masked.max(axis=-1)                  # (n_active,81)
        choice = masked.argmax(axis=-1) + 1
        empty_active = (grids[active] == 0)

        commit = empty_active & (conf >= threshold)
        progressed = np.zeros(active.sum(), dtype=bool)
        if commit.any():
            act_idx = np.where(active)[0]
            for j, gi in enumerate(act_idx):
                cmask = commit[j]
                if cmask.any():
                    grids[gi, cmask] = choice[j, cmask]
                    progressed[j] = True

        # Fallback: if nothing committed this round, fill the single globally most
        # confident legal cell per still-empty active puzzle (avoids deadlock).
        if not progressed.any():
            act_idx = np.where(active)[0]
            for j, gi in enumerate(act_idx):
                ea = (grids[gi] == 0)
                if not ea.any():
                    continue
                c = conf[j].copy()
                c[~ea] = -1.0
                cell = int(c.argmax())
                if c[cell] > 0:
                    grids[gi, cell] = choice[j, cell]

        threshold = max(min_threshold, threshold * decay)

    empty = (puzzles == 0)
    filled = (puzzles > 0)
    correct_empty = ((grids == solutions) & empty).sum()
    total_empty = empty.sum()
    grid_ok = ((grids == solutions) | filled).all(axis=1)
    return {
        'empty_cell_acc': float(correct_empty / max(total_empty, 1)),
        'grid_acc': float(grid_ok.mean()),
        'solved': int(grid_ok.sum()),
        'total': int(N),
    }


# ── Checkpoint loading ────────────────────────────────────────────────────────

def load_rrn(checkpoint, device, n_steps=None):
    ckpt = torch.load(checkpoint, map_location=device, weights_only=False)
    sd = ckpt['model_state_dict'] if 'model_state_dict' in ckpt else ckpt
    hidden_dim = sd['input_embed.0.weight'].shape[0]
    msg_dim = sd['msg_mlp.0.weight'].shape[0]
    cfg = ckpt.get('config', {}) if isinstance(ckpt, dict) else {}
    if n_steps is None:
        n_steps = cfg.get('n_steps', 16)
    model = SudokuRRN(hidden_dim=hidden_dim, msg_dim=msg_dim, n_steps=n_steps).to(device)
    model.load_state_dict(sd)
    model.eval()
    return model, {'hidden_dim': hidden_dim, 'msg_dim': msg_dim, 'n_steps': n_steps,
                   'params': model.count_params()}


def main():
    parser = argparse.ArgumentParser(description='RRN Phase 2 iterative evaluation')
    parser.add_argument('--checkpoint', type=str, required=True)
    parser.add_argument('--data', type=str, required=True,
                        help='npz with puzzles/solutions (e.g. sudoku_extreme_test.npz)')
    parser.add_argument('--n-steps', type=int, default=None,
                        help='Override RRN reasoning steps (default: from checkpoint)')
    parser.add_argument('--n-eval', type=int, default=2000)
    parser.add_argument('--batch-size', type=int, default=512)
    parser.add_argument('--max-rounds', type=int, default=40)
    parser.add_argument('--out', type=str, default=None)
    args = parser.parse_args()

    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
    print(f"Device: {device}")
    if device.type == 'cuda':
        print(f"GPU: {torch.cuda.get_device_name()}")

    edge_index_base = build_sudoku_edge_index()
    model, info = load_rrn(args.checkpoint, device, args.n_steps)
    print(f"Loaded RRN: {info}")

    d = np.load(args.data)
    puzzles = d['puzzles'].astype(np.int64).reshape(-1, 81)
    solutions = d['solutions'].astype(np.int64).reshape(-1, 81)
    n = min(args.n_eval, len(puzzles))
    puzzles, solutions = puzzles[:n], solutions[:n]
    givens = (puzzles > 0).sum(axis=1)
    print(f"Eval set: {n} puzzles, givens {givens.min()}-{givens.max()} mean={givens.mean():.1f}")

    print("\nZero-shot evaluation...")
    t0 = time.time()
    zs = eval_zero_shot(model, puzzles, solutions, edge_index_base, device, args.batch_size)
    print(f"  zero-shot: grid_acc={zs['grid_acc']:.4f} ({zs['solved']}/{zs['total']}) "
          f"empty_cell_acc={zs['empty_cell_acc']:.4f} | {time.time()-t0:.1f}s")

    print("\nIterative refinement evaluation...")
    t0 = time.time()
    it = solve_iterative(model, puzzles, solutions, edge_index_base, device,
                         max_rounds=args.max_rounds, batch_size=args.batch_size)
    print(f"  iterative: grid_acc={it['grid_acc']:.4f} ({it['solved']}/{it['total']}) "
          f"empty_cell_acc={it['empty_cell_acc']:.4f} | {time.time()-t0:.1f}s")

    results = {
        'checkpoint': os.path.basename(args.checkpoint),
        'data': os.path.basename(args.data),
        'model_info': info,
        'n_eval': n,
        'givens_mean': float(givens.mean()),
        'zero_shot': zs,
        'iterative': it,
    }
    out = args.out or os.path.join(os.path.dirname(args.checkpoint),
                                   f'phase2_eval_{os.path.basename(args.checkpoint)}.json')
    with open(out, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {out}")


if __name__ == '__main__':
    main()
