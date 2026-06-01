# Sensitivity Lean

Lean 4 formalization of the Sensitivity Theorem from Boolean function analysis.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 0
- **Build**: `lake build Sensitivity` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `Sensitivity.lean` | 0 | Root import file |
| `Sensitivity/Hypercube.lean` | 0 | Boolean hypercube definitions |
| `Sensitivity/MainTheorem.lean` | 0 | Sensitivity theorem statement and proof |
| `Sensitivity/Operator.lean` | 0 | Sensitivity operator definitions |
| `Sensitivity/VectorSpace.lean` | 0 | Vector space structure for Boolean functions |

## Key Results

- **COMPLETE**: All proofs done, 0 sorry
- Formalization of the **Huang degree theorem** (Huang 2019, `huang_degree_theorem` in `MainTheorem.lean`): an induced subgraph of the hypercube on more than half its vertices has a vertex of degree `>= sqrt(n)` -- the combinatorial result that resolves the Sensitivity Conjecture (`deg(f) <= s(f)^2`)
- Boolean hypercube structure
- Sensitivity and block sensitivity operators

## Notes

- The Sensitivity Theorem was conjectured by Nisan and Szegedy (1992) and proved by Huang (2019)
- Part of the SymbolicAI/Lean formalization series
