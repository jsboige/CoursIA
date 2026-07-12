"""DEPRECATED — Archived 2026-04-28.
Superseded by: scripts/sudoku/core/ + scripts/sudoku/train_v4.py
Original: scripts/test_student_model.py
This file is kept for reference only. Do not use for new work.
"""

"""
Test the EPF student's sudoku_solver_final.h5 model.
1. Inspect architecture
2. Test on notebook puzzles (Easy/Medium/Hard)
3. Compare with our RRN results
"""

import os
import sys
import numpy as np

os.environ['TF_CPP_MIN_LOG_LEVEL'] = '2'
import tensorflow as tf

# Suppress TF warnings
tf.get_logger().setLevel('ERROR')


def inspect_model(model_path):
    """Load and inspect the student model architecture."""
    print("=" * 70)
    print("STUDENT MODEL ARCHITECTURE INSPECTION")
    print("=" * 70)

    model = tf.keras.models.load_model(model_path)
    model.summary()

    print(f"\nTotal params: {model.count_params():,}")
    print(f"Input shape: {model.input_shape}")
    print(f"Output shape: {model.output_shape}")

    print("\nLayer details:")
    for i, layer in enumerate(model.layers):
        config = layer.get_config()
        params = layer.count_params()
        out_shape = "N/A"
        try:
            out_shape = str(layer.output.shape)
        except Exception:
            pass
        print(f"  [{i}] {layer.__class__.__name__:20s} "
              f"shape={out_shape:20s} "
              f"params={params:>10,}  "
              f"activation={config.get('activation', 'N/A')}")

    # Check for batch norm, dropout, etc.
    for layer in model.layers:
        if isinstance(layer, (tf.keras.layers.BatchNormalization,
                              tf.keras.layers.Dropout)):
            print(f"\n  Regularization: {layer.__class__.__name__} "
                  f"(rate={getattr(layer, 'rate', 'N/A')})")

    return model


def preprocess_sudoku(grid):
    """Student's preprocessing: /9 - 0.5, reshape to (9,9,1)."""
    quiz_array = np.array(grid).reshape(9, 9, 1).astype(np.float32)
    quiz_array = quiz_array / 9 - 0.5
    return quiz_array


def predict_sudoku(model, quiz_array):
    """Student's prediction: softmax -> argmax + 1."""
    quiz_array = np.expand_dims(quiz_array, axis=0)
    predictions = model.predict(quiz_array, verbose=0)
    predicted = np.argmax(predictions, axis=-1).reshape(9, 9) + 1
    return predicted


def check_sudoku(grid):
    """Verify a complete 9x9 sudoku is valid."""
    grid = np.array(grid).reshape(9, 9)
    target = set(range(1, 10))
    for i in range(9):
        if set(grid[i, :]) != target:
            return False
        if set(grid[:, i]) != target:
            return False
    for br in range(0, 9, 3):
        for bc in range(0, 9, 3):
            if set(grid[br:br+3, bc:bc+3].flatten()) != target:
                return False
    return True


# Puzzles from Sudoku-18 notebook
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


def test_on_puzzles(model, puzzles_str, dataset_name):
    """Test the student model on a set of puzzles."""
    print(f"\n{'='*70}")
    print(f"{dataset_name} Puzzles ({len(puzzles_str)})")
    print(f"{'='*70}")

    total_cells = 0
    correct_cells = 0
    grids_solved = 0
    total_puzzles = 0

    for i, ps in enumerate(puzzles_str):
        puzzle = parse_puzzle(ps)
        n_empty = int((puzzle == 0).sum())
        if n_empty == 0 or n_empty == 81:
            print(f"  #{i}: SKIP (trivial)")
            continue

        # Get solution: fill in zeros with student model prediction
        preprocessed = preprocess_sudoku(puzzle)
        predicted = predict_sudoku(model, preprocessed).flatten()

        # Check accuracy on empty cells only
        empty_mask = puzzle == 0
        # For non-empty cells, the prediction should match the given clue
        # For empty cells, check if prediction is correct
        # We don't have ground truth, so we check if the full grid is valid
        # and if clues are preserved

        # Build full grid: keep clues, fill predictions for empty cells
        full_grid = puzzle.copy()
        full_grid[empty_mask] = predicted[empty_mask].astype(np.int64)

        # Check clue consistency
        clues_ok = np.all(full_grid[~empty_mask] == puzzle[~empty_mask])

        # Check if complete grid is valid sudoku
        is_valid = check_sudoku(full_grid)

        if is_valid:
            grids_solved += 1
            status = "SOLVED"
        else:
            status = "failed"

        total_puzzles += 1
        print(f"  #{i}: {n_empty:>2} empties | clues_ok={clues_ok} | {status}")

    grid_acc = grids_solved / total_puzzles if total_puzzles > 0 else 0
    print(f"\n  Result: {grids_solved}/{total_puzzles} solved = {grid_acc:.1%} grid accuracy")
    return {'solved': grids_solved, 'total': total_puzzles, 'grid_acc': grid_acc}


def test_cell_accuracy(model, puzzles_str, dataset_name):
    """Test cell-level accuracy using constraint propagation for ground truth."""
    from sudoku_eval_notebook_puzzles import solve_sudoku

    print(f"\n  Cell-level accuracy (with ground truth):")

    total_empty = 0
    correct_empty = 0

    for i, ps in enumerate(puzzles_str):
        puzzle = parse_puzzle(ps)
        n_empty = int((puzzle == 0).sum())
        if n_empty == 0 or n_empty == 81:
            continue

        solution = solve_sudoku(puzzle)
        if solution is None:
            print(f"    #{i}: could not solve for ground truth, skip")
            continue

        preprocessed = preprocess_sudoku(puzzle)
        predicted = predict_sudoku(model, preprocessed).flatten().astype(np.int64)

        empty_mask = puzzle == 0
        correct = (predicted[empty_mask] == solution[empty_mask]).sum()
        total_empty += n_empty
        correct_empty += correct

    cell_acc = correct_empty / total_empty if total_empty > 0 else 0
    print(f"    Cell accuracy: {correct_empty}/{total_empty} = {cell_acc:.1%}")
    return cell_acc


def main():
    model_path = os.path.join(
        os.path.dirname(__file__), '..', 'sudoku_models', 'sudoku_solver_final.h5'
    )

    # Step 1: Inspect architecture
    model = inspect_model(model_path)

    # Step 2: Test on notebook puzzles
    print(f"\n{'='*70}")
    print("TESTING STUDENT MODEL ON NOTEBOOK PUZZLES")
    print(f"{'='*70}")

    results = {}
    for name, puzzles in [('EASY', EASY_PUZZLES), ('MEDIUM', MEDIUM_PUZZLES), ('HARD', HARD_PUZZLES)]:
        r = test_on_puzzles(model, puzzles, name)
        cell_acc = test_cell_accuracy(model, puzzles, name)
        results[name] = {**r, 'cell_acc': cell_acc}

    # Step 3: Summary comparison
    print(f"\n{'='*70}")
    print("COMPARISON: Student Model vs Our RRN h128/16")
    print(f"{'='*70}")
    print(f"{'Dataset':<12} {'Student Grid':>14} {'Student Cell':>14} {'Our Grid':>12} {'Our Cell':>12}")
    print("-" * 66)

    our_results = {
        'EASY': {'grid': 0.30, 'cell': 0.75},
        'MEDIUM': {'grid': 0.00, 'cell': 0.42},
        'HARD': {'grid': 0.00, 'cell': 0.30},
    }

    for name in ['EASY', 'MEDIUM', 'HARD']:
        sg = results[name]['grid_acc']
        sc = results[name]['cell_acc']
        og = our_results.get(name, {}).get('grid', 0)
        oc = our_results.get(name, {}).get('cell', 0)
        print(f"{name:<12} {sg:>13.1%} {sc:>13.1%} {og:>11.1%} {oc:>11.1%}")

    print(f"\n{'='*70}")
    print("CONCLUSION")
    print("=" * 70)

    # Save architecture details for reverse engineering
    print("\nArchitecture summary for reverse engineering:")
    for i, layer in enumerate(model.layers):
        print(f"  Layer {i}: {layer.__class__.__name__} "
              f"(in={layer.input_shape}, out={layer.output_shape}, "
              f"params={layer.count_params():,})")
        if hasattr(layer, 'get_config'):
            cfg = layer.get_config()
            for k in ['filters', 'kernel_size', 'strides', 'padding', 'activation',
                       'units', 'rate', 'momentum', 'use_bias']:
                if k in cfg:
                    print(f"    {k}: {cfg[k]}")


if __name__ == '__main__':
    main()
