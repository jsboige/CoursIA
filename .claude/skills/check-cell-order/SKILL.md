---
name: check-cell-order
description: Detect cell-ordering / enchainement problems in Jupyter notebooks (canonical-order slippage, misplaced or forgotten cells). Arguments: [target] [--severity HIGH|MED|LOW] [--json]
---

# Check Cell Order

Scan notebooks for **cell-ordering and enchainement (flow) problems** — the class
friction reported after the SymbolicLearning session: *"certaines choses
n'étaient pas à leur place"* (canonical-order slippage and forgotten / misplaced
cells that slip through upstream review).

Backed by `scripts/notebook_tools/scan_cell_ordering.py`, which reads the
**beginning and the end of every cell** and reports graded findings, each citing
the offending text so it is spot-checkable. Epic #3240.

**Target**: `$ARGUMENTS`

## Arguments

- `target`: a notebook path, a family subpath (`--family SymbolicAI/SymbolicLearning`), or `--all`
- `--severity HIGH|MED|LOW`: only show findings at or above this level
- `--json`: machine-readable output (for piping / CI)
- `--fail-on HIGH|MED|LOW`: exit 1 if any finding at/above this level (default `HIGH`)

## What it detects

| Severity | Category | Meaning |
|----------|----------|---------|
| HIGH | `SECTION_ORDER` | numbered markdown headers go backwards under the same parent (`## 3.` then `## 2.`) |
| HIGH | `EXERCISE_ORDER` | `Exercice N` / `Exemple N` labels out of order |
| MED | `DANGLING_INTRO` | a markdown cell ends announcing imminent code, but the next cell is **not** code (forgotten / misplaced cell) |
| MED | `INTERP_BEFORE_CODE` | an interpretation markdown sits **before** the code it comments instead of after its output |
| LOW | `SECTION_GAP` | a numbered header skips a value (possible omission) |
| LOW | `CONSECUTIVE_CODE` | more than 3 code cells in a row with no markdown between |

Legitimate numbering is **silent by design**: a normal increment (1→2), a
sub-section open/close (3→3.1→4), a reset-to-1 group restart, a level-mixed H1
title (`# 13.` series number vs `## 1.` sections), fenced-code comments, and
TOC / overview cells listing ≥2 labels.

## Process

1. **Run the scanner** on the target:
   ```bash
   python scripts/notebook_tools/scan_cell_ordering.py <target> --severity HIGH
   # or a whole family:
   python scripts/notebook_tools/scan_cell_ordering.py --family SymbolicAI/SymbolicLearning
   # or the whole repo:
   python scripts/notebook_tools/scan_cell_ordering.py --all --severity HIGH
   ```
   On this machine the script needs a Python with the stdlib only; any of the
   notebook kernels works (e.g. `C:/Users/MYIA/AppData/Local/Programs/Python/Python310/python.exe`).

2. **Ground-truth every HIGH finding before acting** (rule G.1 — the finding is
   a *signal*, not a verdict). Dump the actual headers / labels in document
   order to confirm it is a true positive, e.g.:
   ```bash
   python - <<'PY'
   import json, re
   from pathlib import Path
   H = re.compile(r"^(#{1,6})\s+(\d+(?:\.\d+)*)\b")
   nb = json.loads(Path("<notebook>").read_text(encoding="utf-8"))
   for i, c in enumerate(nb["cells"]):
       if c.get("cell_type") != "markdown":
           continue
       for ln in "".join(c["source"]).splitlines():
           if H.match(ln.strip()):
               print(f"cell#{i}", ln.strip()[:70])
   PY
   ```

3. **Fix or justify**:
   - **True positive** → re-order the cells with `NotebookEdit` (work **bottom→top** to avoid index shift). Re-order **clears outputs**, so re-execute the affected notebook (Papermill, rule C.2) before commit.
   - **Defensible by design** (rare residual FP) → leave it; if recurrent, harden the scanner and add a regression case to `scripts/notebook_tools/tests/test_scan_cell_ordering.py`.

4. **Re-scan** the notebook / family to confirm 0 unjustified HIGH before commit.

## Conventions

- Canonical ordering convention: see `.claude/rules/notebook-conventions.md`
  ("Structure pédagogique" + "Enchaînement des cellules").
- Classification of Exercice vs Exemple is **content-based** — do NOT relabel to
  silence a finding (see `.claude/rules/exercise-example-labeling.md`).
- C.1/C.2/C.3 still apply: no `raise NotImplementedError` in stubs; commit with
  outputs; only stage notebooks whose source changed.

## CI

The scanner is wired into a per-PR gate that scans the notebooks changed by a PR
and fails on HIGH (`--fail-on HIGH`). Pre-existing findings in untouched
notebooks are tracked separately under Epic #3240 and do not block unrelated PRs.

## Notes

- The scanner is **read-only** — it never edits notebooks. Fixes are a separate,
  deliberate step.
- Exit codes: `0` clean / `1` finding at/above `--fail-on` / `2` usage or IO error.
- A malformed notebook prints `ERROR <path>: <reason>` and the scan continues.
