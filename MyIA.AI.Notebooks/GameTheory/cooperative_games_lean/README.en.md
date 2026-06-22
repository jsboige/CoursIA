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

## Conclusion

This project formalizes cooperative game theory in Lean 4 — the **Shapley value**
(closed, 0 `sorry`) and the **Core** with the **Bondareva-Shapley theorem** (1 `sorry`,
WIP). It builds with `lake build CooperativeGames` on Mathlib4 (toolchain
`v4.30.0-rc2`).

### What is proven

- **Shapley value uniqueness** (`Shapley.lean`, 0 `sorry`): the Shapley value is the
  *unique* allocation satisfying efficiency, symmetry, null-player, and additivity —
  Shapley's (1953) axiomatic characterization.
- **Core + Bondareva-Shapley scaffolding** (`Basic.lean`): cooperative game,
  characteristic function, the Core, and the balanced-game condition, with the `←`
  direction (balanced ⇒ Core nonempty) reduced to a single extraction step.

### Why the lone sorry remains

The one `sorry` (`Basic.lean:312`, `hb_witness`) is the **LP-dual kernel** of the
Bondareva-Shapley backward direction: extracting from the balanced condition an
allocation `x ∈ Core` with `∑ xᵢ ≤ v(N)`. This is a Farkas / hyperplane-separation
argument over a cone. It is **WIP, not abandoned** — an active plan
([`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)) validates the
infrastructure (`ProperCone.hyperplane_separation_point` via an `(Option N) → ℝ`
encoding) and isolates the remaining translation (~150-180 lines; the
`StrongDual → balanced weights` step is the crux). `FORMAL_STATUS.md` records it as
WIP_HARD.

### Where to go next

- **Theory**: Bondareva (1963) / Shapley (1967), the Core characterizations;
  Shapley (1953), *A Value for n-Person Games*.
- **Active plan**: [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)
  and [`FORMAL_STATUS.md`](FORMAL_STATUS.md).
- **Related**: [`stable_marriage_lean/`](../stable_marriage_lean/) (Gale-Shapley
  matching) and [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).
