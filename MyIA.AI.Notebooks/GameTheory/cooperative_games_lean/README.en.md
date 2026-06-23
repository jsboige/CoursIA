# Cooperative Games Lean

Lean 4 formalization of cooperative game theory (Shapley value, core).

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: **0** -- the Bondareva-Shapley theorem is proved in both directions
- **Build**: `lake build CooperativeGames` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `CooperativeGames/Shapley.lean` | 0 | Shapley value (definition + uniqueness), null/dummy players, Banzhaf power index |
| `CooperativeGames/Basic.lean` | 0 | Cooperative game / characteristic function / Core / Bondareva-Shapley theorem |
| `CooperativeGames/ConeKernel.lean` | 0 | Farkas / cone-separation kernel (machinery proving the backward direction) |

## Key Results

- **Shapley value uniqueness**: Proved that the Shapley value is the unique value satisfying efficiency, symmetry, null player, and additivity axioms (Shapley.lean, 0 sorry)
- **Core definitions**: Cooperative game, characteristic function, player set, Core (Basic.lean)
- **Bondareva-Shapley `←` direction** (balanced ⇒ Core nonempty): **fully proved** via the cone-separation machinery in the `ConeKernel.lean` module (Mathlib's `ProperCone.hyperplane_separation_point`)
- **Banzhaf power index**: framework defined (`Critical G i S`, `BanzhafRaw G i` — the number of coalitions for which `i` is critical) with the theorem `dummy_banzhaf_raw_zero`: a dummy player (who never changes a coalition's value) has zero raw Banzhaf index (Shapley.lean, 0 sorry, PR #4011)

## Banzhaf power index

The Shapley value is not the only relevant power index in cooperative game theory. The
**Banzhaf index** measures a player's power as their number of *swings* (pivotal
coalitions): combinations where moving from out-of-coalition to in-coalition flips the
coalition's value. Unlike the Shapley value (which weights each coalition by a factorial
factor), the raw Banzhaf index treats all coalitions equally.

The module formalizes this framework over weighted voting games (`WeightedVotingGame`):

- **Critical player** — `Critical G i S` holds when `i ∈ S`, the coalition `S` wins
  (`G.v S = 1`) but the coalition without `i` loses (`G.v (S.erase i) = 0`). A player is
  critical for `S` if removing them turns a winning coalition into a losing one.
- **Raw Banzhaf index** — `BanzhafRaw G i` is the number of coalitions for which `i` is
  critical, i.e. `(Finset.univ.filter fun S => Critical G i S).card`.

Two nullity theorems are proved (both at 0 `sorry`):

- `dummy_shapley_zero`: a dummy player receives zero Shapley value.
- `dummy_banzhaf_raw_zero` (PR #4011): a dummy player has zero raw Banzhaf index.

A dummy player (`DummyPlayer`) never changes a coalition's value, so it is never critical:
its raw Banzhaf index is indeed zero. This is the Banzhaf-index analogue of the null-player
theorem for the Shapley value.

**Proven** (PR #4037, merged `ba3b169e`): the symmetry theorem `banzhaf_raw_symmetric`
(`Shapley.lean:1106`) — two interchangeable players (`SymmetricPlayers`) have equal raw
Banzhaf indices, the Banzhaf analogue of `shapley_symmetric`. The proof builds an involution
`banzhafSwap` that exchanges `i` and `j` in each coalition (four cases: containing both,
neither, or exactly one of them), shows it preserves the game's value (by `SymmetricPlayers`,
after a case split on `S ∩ {i, j}`), and transports the critical coalitions of `i`
bijectively onto those of `j`; the two critical-coalition filters are thus in bijection, so
their cardinalities coincide — the raw Banzhaf indices. This power-index lineage
(`dummy_banzhaf_raw_zero` #4011 → `banzhaf_raw_symmetric` #4037) parallels the Shapley
characterisation.

## Notes

- The Bondareva-Shapley theorem is closed in both directions (`forward` + `backward`), **0 sorry**. The `←` direction extracted a Core allocation via a Farkas / hyperplane-separation argument over a cone; this argument, long tagged **INTRACTABLE**, is now constructed and proved in `CooperativeGames/ConeKernel.lean` (augmented cone `augCone`, dual lemma `augCone_dual_iff`, separator `separatingFunctional_none_neg`, witness decoding `exists_preimputation_strict_core`)
- Proof arc: PR #3933 (ConeKernel kernel, TUGame-free) → #3941 (`balancedUnit` bridge) → #3945 (decoding core) → #3951 (pipeline wiring) → #3954 (sorry 1→0). `hb_witness` is now a certified `have` (`Basic.lean:348`)
- Related to `stable_marriage_lean/` (matching theory as cooperative game)

## Conclusion

This project formalizes cooperative game theory in Lean 4 — the **Shapley value**
(closed, 0 `sorry`) and the **Core** with the **Bondareva-Shapley theorem** (0 `sorry`,
proved in both directions). It builds with `lake build CooperativeGames` on Mathlib4
(toolchain `v4.30.0-rc2`).

### What is proven

- **Shapley value uniqueness** (`Shapley.lean`, 0 `sorry`): the Shapley value is the
  *unique* allocation satisfying efficiency, symmetry, null-player, and additivity —
  Shapley's (1953) axiomatic characterization.
- **Power indices and dummy players** (`Shapley.lean`, 0 `sorry`): beyond the Shapley value
  characterization, the module formalizes the notion of null/dummy player
  (`NullPlayer`, `DummyPlayer`) with the two nullity theorems `dummy_shapley_zero`
  (a dummy player gets zero Shapley value) and `dummy_banzhaf_raw_zero` (a dummy player
  has zero raw Banzhaf index). The Banzhaf framework rests on the definition
  `Critical G i S` (player `i` is critical for coalition `S` when `i ∈ S`, `G.v S = 1`
  but `G.v (S.erase i) = 0`) and on the raw index `BanzhafRaw G i` counting critical
  coalitions via a filter over `Finset.univ` (PR #4011).
- **Core + Bondareva-Shapley theorem** (`Basic.lean` + `ConeKernel.lean`): cooperative
  game, characteristic function, the Core, and the balanced-game condition, with the `←`
  direction (balanced ⇒ Core nonempty) **fully proved** by cone separation.

### How the backward direction was proved

The step once tagged **INTRACTABLE** — extracting from the balanced condition an
allocation `x ∈ Core` with `∑ xᵢ ≤ v(N)`, a Farkas / hyperplane-separation argument over a
cone — is now closed. The machinery lives in `CooperativeGames/ConeKernel.lean`: the
augmented cone `augCone` encodes balanced-weight violations, and
`ProperCone.hyperplane_separation_point` (Mathlib `Analysis.Convex.Cone.Dual`) supplies a
separator `f`; the duality lemmas (`augCone_dual_iff`), non-negative separator
(`separatingFunctional_none_neg`) and witness decoding (`exists_preimputation_strict_core`)
convert that separator into a Core imputation. `hb_witness` is now a certified `have`
(`Basic.lean:348`). Arc: #3933 → #3941 → #3945 → #3951 → #3954 (sorry 1→0). The original
plan remains documented in
[`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md).

### Where to go next

- **Theory**: Bondareva (1963) / Shapley (1967), the Core characterizations;
  Shapley (1953), *A Value for n-Person Games*.
- **Active plan**: [`docs/BONDAREVA_FARKAS_PLAN.md`](docs/BONDAREVA_FARKAS_PLAN.md)
  and [`FORMAL_STATUS.md`](FORMAL_STATUS.md).
- **Related**: [`stable_marriage_lean/`](../stable_marriage_lean/) (Gale-Shapley
  matching) and [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen).
