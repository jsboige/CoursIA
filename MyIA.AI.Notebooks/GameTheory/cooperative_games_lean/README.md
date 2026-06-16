# Cooperative Games Lean

Lean 4 formalization of cooperative game theory (Shapley value, core).

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 1 production (`Basic.lean` L312, `bondareva_shapley_forward.hCore`, tagged `INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION`)
- **Build**: `lake build CooperativeGames` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value definition and uniqueness theorem |
| `CooperativeGames/Basic.lean` | 1 | Cooperative game / characteristic function / Core / Bondareva-Shapley scaffolding |

## Key Results

- **Shapley value uniqueness**: Proved that the Shapley value is the unique value satisfying efficiency, symmetry, null player, and additivity axioms (Shapley.lean, 0 sorry)
- **Core definitions**: Cooperative game, characteristic function, player set, Core (Basic.lean)
- **Bondareva-Shapley `←` direction** (balanced ⇒ Core nonempty): all scaffolding closed except the final extraction step at L312

## Notes

- The lone `sorry` lives in `bondareva_shapley_forward.hCore` (Basic.lean L312). The proof reduces "P ⊆ {x : ∑ xᵢ ≥ v(N)}" to extracting an allocation with equality, which requires either Farkas-style hyperplane separation or a constructive minimum-existence argument over a compact convex set
- Mathlib4 currently lacks the hyperplane-separation lemma needed; tagged **INTRACTABLE** by the multi-agent prover until that infrastructure lands (cf [LEAN_INVENTORY.md](../LEAN_INVENTORY.md) GO/NO-GO table)
- Related to `stable_marriage_lean/` (matching theory as cooperative game)
