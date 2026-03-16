---
name: Sudoku series audit completion
description: Status of the Sudoku notebook series audit (32 notebooks, RESOLVED/NO_EX/OPEN patterns)
type: project
---

## Sudoku Series Audit - Completed

All 32 notebooks in `MyIA.AI.Notebooks/Sudoku/` have been processed according to the audit plan.

### Status by notebook

**OPEN (do not touch)**:
- Sudoku-4-SA-Csharp: skipped
- Sudoku-7-Norvig-Csharp: skipped
- Sudoku-15-Infer-Csharp: skipped

**Already complete before audit started**:
- Sudoku-0-Environment-Csharp: already had header + exercise
- Sudoku-1-Backtracking-Python: already had header + exercise
- Sudoku-7-Norvig-Python: already had header + exercise
- Sudoku-4-SA-Python: file not found

**OPEN without code cell (added code TODO after existing exercise markdown)**:
- Sudoku-8-HumanStrategies-Python: added code cell after cell `1491cac0`
- Sudoku-9-GraphColoring-Csharp: added code cell after `cell-21`

**RESOLVED (renamed exercises to Exemple guide + added new exercise + code TODO)**:
- Sudoku-5-PSO-Csharp: cell-16 renamed + new exercise
- Sudoku-5-PSO-Python: cell bf6de260 renamed + new exercise
- Sudoku-6-AIMA-CSP-Csharp: cell-27 renamed + CBJ exercise
- Sudoku-6-AIMA-CSP-Python: cell-26 renamed + CBJ exercise
- Sudoku-8-HumanStrategies-Csharp: cell fa4fca2e renamed + Swordfish exercise
- Sudoku-11-Choco-Python: cell `exercises` renamed + count_solutions exercise
- Sudoku-13-SymbolicAutomata-Csharp: cell `exercises` renamed + diagonal exercise
- Sudoku-14-BDD-Csharp: cell `exercises` renamed + BDD propagator exercise
- Sudoku-16-NeuralNetwork-Python: cell `exercises-section` renamed + NeuroConstraintSolver exercise
- Sudoku-17-LLM-Python: cell `exercises` renamed + ChainOfThoughtSudokuSolver exercise

**NO_EX (added exercise at end)**:
- Sudoku-9-GraphColoring-Python: added LCV exercise
- Sudoku-15-Infer-Python: added HybridProbabilisticSolver exercise
- Sudoku-18-Comparison-Python: added BacktrackingAC3Solver exercise
- Sudoku-12-Z3-Csharp: added Z3SudokuPropertyChecker exercise
- (Others done in earlier session: Sudoku-1/2/3/10/11/12-Python etc.)

### Why:
Task was a comprehensive pedagogical audit to ensure every Sudoku notebook has at least one open-ended exercise with a code TODO cell.

### How to apply:
If adding more exercises in the future, follow the same patterns:
- RESOLVED: rename old exercises to "Exemple guide" + insert new exercise + code TODO cell
- NO_EX: insert exercise markdown + code TODO before last navigation cell
- Use cell_id (not index) for NotebookEdit
- Work top-to-bottom by inserting before the target cell
