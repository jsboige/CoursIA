"""Evaluate RRN models on Easy/Medium/Hard puzzles from Sudoku-18 notebook."""

import os
import sys
import numpy as np
import torch

sys.path.insert(0, os.path.dirname(__file__))
from core import (
    SudokuRRN, build_sudoku_edge_index, evaluate, solve_sudoku, is_valid_puzzle,
)

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')
print(f"Device: {device}")


# ── Puzzles from Sudoku-18-Comparison-Python.ipynb (cell 21) ──────────────────
EASY_PUZZLES = [
    "003020600900305001001806400008102900700000008006708200002609500800203009005010300",
    "200080300060070084030500209000105408000000000402706000301007040720040060004010003",
    "000000907000420180000705026100904000050000040000507009920108000034059000507000000",
    "030050040008010500460000012070502080000603000040109030250000098001020600080060020",
    "020810740700003100090002805009040087400208003160030200302700060005600008076051090",
    "100920000524010000000000070050008102000000000402700090060000000000030945000071006",
    "043080250600000000000001094900004070000608000010200003820500000000000005034090710",
    "480006902002008001900370060840010200003704100001060049020085007700900600609200018",
    "000900002050123400030000160908000000070000090000000205091000050007439020400007000",
    "001900003900700160030005007050000009004302600200000070600100030042007006500006800",
]

MEDIUM_PUZZLES_DOT = [
    "4.....8.5.3..........7......2.....6.....8.4......1.......6.3.7.5..2.....1.4......",
    "52...6.........7.13...........4..8..6......5...........418.........3..2...87.....",
    "6.....8.3.4.7.................5.4.7.3..2.....1.6.......2.....5.....8.6......1....",
    "48.3............71.2.......7.5....6....2..8.............1.76...3.....4......5....",
    "....14....3....2...7..........9...3.6.1.............8.2.....1.4....5.6.....7.8...",
    "......52..8.4......3...9...5.1...6..2..7........3.....6...1..........7.4.......3.",
    "6.2.5.........3.4..........43...8....1....2........7..5..27...........81...6.....",
    ".524.........7.1..............8.2...3.....6...9.5.....1.6.3...........897........",
    "6.2.5.........4.3..........43...8....1....2........7..5..27...........81...6.....",
    ".923.........8.1...........1.7.4...........658.........6.5.2...4.....7.....9.....",
]

HARD_PUZZLES_DOT = [
    "85...24..72......9..4.........1.7..23.5...9...4...........8..7..17..........36.4.",
    "..53.....8......2..7..1.5..4....53...1..7...6..32...8..6.5....9..4....3......97..",
    "12..4......5.69.1...9...5.........7.7...52.9..3......2.9.6...5.4..9..8.1..3...9.4",
    "...57..3.1......2.7...234......8...4..7..4...49....6.5.42...3.....7..9....18.....",
    "7..1523........92....3.....1....47.8.......6............9...5.6.4.9.7...8....6.1.",
    "1....7.9..3..2...8..96..5....53..9...1..8...26....4...3......1..4......7..7...3..",
    "1...34.8....8..5....4.6..21.18......3..1.2..6......81.52..7.9....6..9....9.64...2",
    "...92......68.3...19..7...623..4.1....1...7....8.3..297...8..91...5.72......64...",
    ".6.5.4.3.1...9...8.........9...5...6.4.6.2.7.7...4...5.........4...8...1.5.2.3.4.",
    "7.....4...2..7..8...3..8.799..5..3...6..2..9...1.97..6...3..9...3..4..6...9..1.35",
    "....7..2.8.......6.1.2.5...9.54....8.........3....85.1...3.2.8.4.......9.7..6....",
]

MEDIUM_PUZZLES = [s.replace('.', '0') for s in MEDIUM_PUZZLES_DOT]
HARD_PUZZLES = [s.replace('.', '0') for s in HARD_PUZZLES_DOT]


def parse_puzzle(s):
    return np.array([int(c) for c in s], dtype=np.int64)


def main():
    MODEL_PATH = os.path.join(
        os.path.dirname(__file__), '..', '..', 'sudoku_models', 'sudoku_rrn_v4_best.pt'
    )
    if not os.path.exists(MODEL_PATH):
        MODEL_PATH = os.path.join(
            os.path.dirname(__file__), '..', '..', 'sudoku_models', 'finetuned_h192_s16_strat_v2_best.pt'
        )

    print("=" * 70)
    print("RRN Evaluation on Notebook Puzzles")
    print("=" * 70)

    ckpt = torch.load(MODEL_PATH, weights_only=False)
    print(f"Checkpoint: epoch {ckpt['epoch']}, val_loss={ckpt['val_loss']:.4f}, val_acc={ckpt['val_acc']:.4f}")

    # Detect architecture from checkpoint
    sd = ckpt['model_state_dict']
    hidden_dim = sd['input_embed.0.weight'].shape[0]
    msg_dim = sd['msg_mlp.0.weight'].shape[0] // 2 if 'msg_mlp.0.weight' in sd else hidden_dim
    model = SudokuRRN(hidden_dim=hidden_dim, msg_dim=msg_dim, n_steps=8, dropout=0.15).to(device)
    model.load_state_dict(sd)
    model.eval()

    from core.models import count_params
    n_params = count_params(model)
    print(f"Model: SudokuRRN ({n_params:,} params, 8 reasoning steps)")

    base_edges = build_sudoku_edge_index()

    datasets = {
        'EASY': EASY_PUZZLES,
        'MEDIUM': MEDIUM_PUZZLES,
        'HARD': HARD_PUZZLES,
    }

    results = {}
    for name, puzzles_str in datasets.items():
        print(f"\n{'='*70}")
        print(f"{name} Puzzles ({len(puzzles_str)})")
        print(f"{'='*70}")

        valid_puzzles = []
        valid_solutions = []
        for i, ps in enumerate(puzzles_str):
            p = parse_puzzle(ps)
            n_empty = int((p == 0).sum())
            if n_empty == 0 or n_empty == 81:
                continue
            if not is_valid_puzzle(p):
                print(f"  #{i}: SKIP (invalid, {n_empty} empties)")
                continue

            sol = solve_sudoku(p)
            if sol is None:
                print(f"  #{i}: SKIP (unsolvable, {n_empty} empties)")
                continue

            valid_puzzles.append(p)
            valid_solutions.append(sol)

        if not valid_puzzles:
            print("  No valid puzzles!")
            continue

        puzzles_arr = np.array(valid_puzzles, dtype=np.int64)
        solutions_arr = np.array(valid_solutions, dtype=np.int64)

        n_empty = (puzzles_arr == 0).sum(axis=1)
        print(f"\n  Valid: {len(valid_puzzles)} puzzles, empties: min={n_empty.min()} max={n_empty.max()} avg={n_empty.mean():.1f}")

        cell_acc, grid_acc, avg_loss = evaluate(
            model, puzzles_arr, solutions_arr, base_edges, device, batch_size=16
        )

        print(f"\n  Overall: cell_acc={cell_acc:.4f} | grid_acc={grid_acc:.4f} | loss={avg_loss:.4f}")
        print(f"  {'#':<5} {'Empty':>6} {'Correct':>8} {'Solved':>7}")
        print(f"  {'-'*30}")

        for i in range(len(valid_puzzles)):
            p = puzzles_arr[i:i+1]
            s = solutions_arr[i:i+1]
            c, g, _ = evaluate(model, p, s, base_edges, device, batch_size=1)
            ne = int((p == 0).sum())
            nc = int(c * ne)
            solved = "YES" if g > 0.5 else "no"
            print(f"  {i:<5} {ne:>6} {nc:>5}/{ne:<2} {solved:>7}")

        results[name] = {
            'cell_acc': cell_acc, 'grid_acc': grid_acc,
            'n_puzzles': len(valid_puzzles), 'avg_empty': float(n_empty.mean()),
        }

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print(f"{'Dataset':<15} {'Puzzles':>8} {'Avg Empty':>10} {'Cell Acc':>10} {'Grid Acc':>10} {'Solved':>8}")
    print("-" * 65)
    for name, r in results.items():
        n_solved = int(r['grid_acc'] * r['n_puzzles'])
        print(f"{name:<15} {r['n_puzzles']:>8} {r['avg_empty']:>10.1f} {r['cell_acc']:>9.1%} "
              f"{r['grid_acc']:>9.1%} {n_solved}/{r['n_puzzles']:>2}")


if __name__ == '__main__':
    main()
