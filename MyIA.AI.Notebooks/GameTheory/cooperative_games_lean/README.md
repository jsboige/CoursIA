# Cooperative Games Lean

Lean 4 formalization of cooperative game theory (Shapley value, core).

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 0 (grep hit in Basic.lean is in comment only)
- **Build**: `lake build CooperativeGames` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value definition and uniqueness theorem |
| `CooperativeGames/Basic.lean` | 0 | Cooperative game definitions (hCore removed in refactor) |

## Key Results

- **Shapley value uniqueness**: Proved that the Shapley value is the unique value satisfying efficiency, symmetry, null player, and additivity axioms
- **Core definitions**: Cooperative game, characteristic function, player set
- **COMPLETE**: 0 sorry in production code

## Notes

- Bondareva-Shapley theorem (core non-emptiness) remains unformalized -- requires hyperplane separation which is not yet available in Mathlib4
- Related to `stable_marriage_lean/` (matching theory as cooperative game, Shapley value)
