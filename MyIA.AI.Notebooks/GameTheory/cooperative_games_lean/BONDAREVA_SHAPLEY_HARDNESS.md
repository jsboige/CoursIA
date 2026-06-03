# Bondareva-Shapley Backward: Hardness Investigation

**Agent:** po-2025 | **Date:** 2026-05-12 | **Cycle:** 28 Track A

## Verdict: PARTIALLY_PROUVABLE (reclassified from HONEST_UNPROVABLE)

The `bondareva_shapley_backward` sorry at `Basic.lean:234` was classified as
HONEST_UNPROVABLE because "LP duality / Farkas' lemma is missing in Mathlib."
This assessment is **partially outdated**: Farkas' lemma IS available since 2025
(Dillies/Yang). LP strong duality remains absent but is NOT required for the proof.

## What changed in Mathlib

The comment in `Basic.lean:221-224` claims Mathlib lacks:

| Claimed missing | Actual status (Mathlib v4.28-rc1) |
|-----------------|----------------------------------|
| LP duality theorem | Still absent (TODO in Cone.Basic) |
| Farkas' lemma usable on `Finset N -> R` | **Available** as `ProperCone.hyperplane_separation` |
| `Polyhedral.cone_of_nonempty` | Still absent |

**Key module:** `Mathlib.Analysis.Convex.Cone.Dual` (Copyright 2025 Yaël Dillies, Andrew Yang)

Provides:
- `ProperCone.dual` — dual cone with respect to a continuous perfect pairing
- `ProperCone.hyperplane_separation` — Farkas' lemma (separate compact convex from proper cone)
- `ProperCone.hyperplane_separation_point` — Point version of Farkas' lemma
- `ProperCone.dual_dual_flip` — Double dual of proper cone = itself

## Proof strategy (Farkas-based, no LP duality needed)

The classical proof does NOT require LP strong duality. It only needs Farkas' lemma
(theorem of alternatives):

### Step 1: Formulate as feasibility

Find `x : N -> R` satisfying:
- `sum_{i in S} x i >= v(S)` for all nonempty `S : Finset N`
- `sum_i x i <= v(N)`

### Step 2: Apply Farkas' alternative theorem

This system is feasible iff the alternative is infeasible:

> For all `lambda_S >= 0` and `mu >= 0`:
> if `sum_S lambda_S * 1_{i in S} = mu` for all `i`, then `sum_S lambda_S * v(S) <= mu * v(N)`

### Step 3: Connect to balanced condition

Setting `w_S = lambda_S / mu` (when `mu > 0`), the alternative becomes:
> For all balanced weights `w`: `sum_S w_S * v(S) <= v(N)`

This is EXACTLY the balanced condition of the game.

### Step 4: Extract core membership

From feasibility: `sum_i x i <= v(N)` and `sum_{i in N} x i >= v(N)`, so `sum_i x i = v(N)`.
Combined with coalition constraints, `x` is in the Core.

## Infrastructure gap: theorem of alternatives

`ProperCone.hyperplane_separation` gives Farkas in **separation form**:
```
C : ProperCone R E, K compact convex, Disjoint K C =>
  exists f : StrongDual R E, (forall x in C, 0 <= f x) /\ forall x in K, f x < 0
```

The proof needs Farkas in **alternatives form**:
```
Either {x | Ax >= b} has a solution, or {y >= 0 | A^T y = 0, y . b > 0} has a solution
```

Deriving alternatives from separation requires:
1. Encode `{Ax >= b}` as the preimage of a proper cone under a linear map
2. Show this preimage (or the associated cone) is proper (closed, pointed, convex)
3. Apply `hyperplane_separation` to get the separating functional
4. Translate back to the alternatives formulation

**In finite dimensions** (`Fin n -> R`), all linear maps are continuous, all
finite-dimensional subspaces are closed, so the "proper cone" conditions are
automatic. Mathlib provides `LinearMap.continuous_of_finiteDimensional` and
`Submodule.closed_of_finiteDimensional`.

## Estimated work

| Component | Lines | Difficulty | Mathlib support |
|-----------|-------|------------|----------------|
| Theorem of alternatives from separation | ~60-80 | HARD | hyperplane_separation + fd continuity |
| Coalition constraint system as proper cone | ~30-50 | MEDIUM | ProperCone, finite-dimensional |
| Balanced ↔ alternative equivalence | ~20-30 | MEDIUM | Finset algebra, balanced def |
| Extract core membership | ~10-20 | EASY | Core definition, sum manipulation |
| **Total** | **~150-200** | **MEDIUM-HARD** | |

## Recommendations

1. **Reclassify** `bondareva_shapley_backward` from HONEST_UNPROVABLE to
   **WIP_HARD** (feasible, ~150-200 lines of preparatory lemmas)
2. **Do NOT attempt now** — 150-200 lines of convex analysis infrastructure
   is a multi-day effort, better suited for a focused sprint
3. **Update FORMAL_STATUS.md** — change BLOCKED to WIP_HARD with the
   Farkas-based strategy outlined here
4. **Prerequisite:** verify `Fin N -> R` can be given `LocallyConvexSpace R`
   and `IsContPerfPair` instances (likely yes via `Pi.topologicalSpace`)

## Alternative: reduced game approach

An inductive proof on `|N|` via reduced games avoids Farkas entirely but requires:
- Defining the Davis-Maschler reduced game
- Proving the reduced game inherits balancedness
- More game-theory-specific infrastructure

This is likely MORE work than the Farkas approach since Mathlib's convex
analysis is already well-developed.

## References

- Dillies, Y., Yang, A. (2025). `Mathlib.Analysis.Convex.Cone.Dual`
- Bondareva, O.N. (1963). "Some Applications of Linear Programming Methods
  to the Theory of Cooperative Games"
- Shapley, L.S. (1967). "On Balanced Sets and Cores"
