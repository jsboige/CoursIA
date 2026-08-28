# Mathlib Examples

Basic Mathlib usage examples for the SymbolicAI/Lean series.

## Status

- **Toolchain**: v4.31.0-rc1
- **Sorry count**: 0
- **Build**: `lake build MathLibExamples` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `MathLibExamples/Basic.lean` | 0 | Basic Mathlib usage patterns and examples |

## Key Results

- Demonstrates common Mathlib tactics and proof patterns
- Serves as reference for students learning Lean 4 with Mathlib

## Notes

- **Assumed role: smoke test / validation environment** — this lake checks that
  the toolchain and Mathlib resolve the four everyday automators. No notebook
  imports the `MathLibExamples` module: series notebooks import Mathlib
  directly; `Lean-28-Munkres-Tribute.ipynb` uses this lake as the **execution
  environment** for the `lean4-wsl` kernel (Mathlib olean resolution), without
  consuming its content.
- Part of the SymbolicAI/Lean pedagogical series

## Conclusion

A thin **reference module** of basic Mathlib usage patterns
(`MathLibExamples/Basic.lean`, 0 `sorry`, `lake build MathLibExamples` SUCCESS):
a **smoke test** of the Mathlib installation — and the Mathlib execution
environment of the `lean4-wsl` kernel for Lean-28 — not a module-to-notebook
companion. It is intentionally minimal — a starting point for students, not a
survey.

### Where to go next

- **Mathlib hands-on in notebook form**: `Lean-6-Mathlib-Essentials.ipynb`
  (tactics exercised on directly imported Mathlib) and
  `Lean-28-Munkres-Tribute.ipynb` (Munkres' course 18.901, executed on this lake).
- **Fuller Lean projects**: [`calibration_lean/`](../calibration_lean/),
  [`conway_lean/`](../conway_lean/), [`sensitivity_lean/`](../sensitivity_lean/)
  — production Lean built on Mathlib.
