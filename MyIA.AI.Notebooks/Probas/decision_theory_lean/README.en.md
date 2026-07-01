# decision_theory_lean — Decision Theory (Lean 4)

Lake **at the `Probas` series root**, formalizing canonical decision-theory
results — visible from both series tracks (Infer.NET / PyMC).

Three modules delivered:

- **Gittins** — the **multi-armed bandit** problem and the **Gittins index**
  (Gittins 1979, Weber 1992): the optimal policy for the discounted
  infinite-horizon bandit. The **geometric-discount building blocks are fully
  proven** (PR #2911, + finite partial-sum companion #4252); the **marquee
  optimality theorem is stated but intractable** in the current Mathlib (no
  MDP/Bellman formalization), held as `sorry`.
- **Utility** (`#4049`, `#4250`) — the **von Neumann–Morgenstern** expected-utility
  representation. Proves **sorry-free** the **sound direction** (a utility
  representation ⟹ rationality, i.e. the four axioms), **affine stability**
  (cardinality), and the **strict-preference / indifference characterization**
  (`rep_strict_iff`, `rep_indifference_iff`). The existence direction
  (Herstein–Milnor 1953) is an **open milestone** (deliberately not `sorry`-backed).
- **Coherence** (`#4050`, `#4193`, `#4244`) — the **de Finetti / Dutch Book**
  coherence argument. Proves **sorry-free** the **constructive direction** (prices
  violating inclusion–exclusion expose the agent to an explicit Dutch Book) and its
  contrapositive; the **single-ticket case is fully closed**
  (`single_coherent_iff_prob_bounds`); weights ⟹ single-coherent price
  (`priceFromWeights_single_coherent`). The full reciprocal on arbitrary book sizes
  (`coherent_iff_probability`, needs hyperplane separation / LP duality) is an
  **open milestone** (deliberately not `sorry`-backed).

Lean companion notebook:
[`Infer/Infer-9-Lean-Gittins.ipynb`](../DecisionTheory/Infer/Infer-9-Lean-Gittins.ipynb).

## Status

- **Toolchain**: `leanprover/lean4:v4.30.0-rc2`
- **Sorry**: **5** — all in `Gittins/GittinsTheorem.lean` (the optimality theorem +
  index properties). `Gittins/Discount.lean` = **0 sorry** (fully proven),
  `Gittins/Basic.lean` = 0. The **entire `Utility` and `Coherence` modules = 0 sorry**
  (fully proven, open milestones documented, not `sorry`-backed).
- **Build**: `lake build Gittins Utility Coherence` (depends on Mathlib4)
- **Dependencies**: Mathlib4 (`v4.30.0-rc2`) — real analysis for the discount lemmas,
  the ordered and affine structure of `ℝ` for vNM, `Finset` / inclusion–exclusion for
  de Finetti coherence

## What it formalizes

A **multi-armed bandit**: at each step a policy chooses one of several arms
(`BanditArm`) and observes a reward; the goal is to maximize total expected
discounted reward (discount `γ ∈ (0,1)`). The **Gittins index** of an arm is the
fixed point of an optimal-stopping problem; the **Gittins index policy** (play
the arm with the highest index) is optimal for the discounted bandit.

The formalization is split into a **proven** layer and a **stated** layer:

- **Proven** (`Discount.lean`): the geometric-series identities underpinning
  discounted value — `∑' γ^n = 1/(1-γ)`, `∑' γ^n·r = r/(1-γ)`, and
  `discount_monotone` (γ₁ ≤ γ₂ ⇒ ∑' γ₁^n ≤ ∑' γ₂^n). `discount_monotone` is
  proven **closed-form** via `geometric_series_converges` +
  `one_div_le_one_div_of_le`, sidestepping the missing `tsum_le_tsum` on bare `ℝ`
  in Mathlib v4.30.0-rc2.
- **Stated, intractable** (`GittinsTheorem.lean`): `gittinsIndex` (optimal
  stopping), `gittins_optimality` (the central theorem — the index policy
  maximizes expected discounted reward), `gittins_index_known_arm`,
  `gittins_index_monotone_discount`. All `sorry`.

## Modules

| File | Lines | sorry | Content |
|------|-------|-------|---------|
| `Gittins/Basic.lean` | 37 | 0 | Core types — `BanditArm`, `BanditInstance` (arms + discount γ), `Policy := Nat → Nat`, `RewardHistory`, `pullCount`, `empiricalMean`. Pure Lean 4, no Mathlib. |
| `Gittins/Discount.lean` | 107 | 0 | Geometric discounting **proven** via Mathlib real analysis: `geometric_series_converges`, `one_minus_gamma_pos`, `present_value_constant`, `discount_monotone`. **Finite partial-sum companion** (PR #4252): `geometricPartialSum γ n` with `_zero`/`_succ` (telescoping recurrence) and `_closed` (closed form `(1−γ^n)/(1−γ)`). |
| `Gittins/GittinsTheorem.lean` | 96 | 5 | The marquee theorem **stated with sorry**: `gittinsIndex`, `gittinsPolicy` (argmax), `gittins_optimality`, `gittins_index_known_arm`, `gittins_index_monotone_discount`. (`gittins_beats_greedy` is a `: True := trivial` placeholder, not a sorry.) |
| `Gittins.lean` | 19 | 0 | Umbrella imports |
| `Utility/Basic.lean` | 91 | 0 | vNM primitives — `Lottery` (lottery on `Fintype`), `expectation`, convex `mix`, affine expectation identities (`expectation_mix`, `expectation_add`, `expectation_smul`, `expectation_const`, `expectation_affine`). |
| `Utility/Axioms.lean` | 65 | 0 | The **four vNM axioms** — `IsComplete`, `IsTransitive`, `IsIndependent`, `IsContinuous` (mixture solvability), `IsRational`, plus `StrictPref`. |
| `Utility/Representation.lean` | 236 | 0 | **Sound direction proven** (`rep_complete`, `rep_transitive`, `rep_independent`, `rep_continuous`, `expected_utility_rep_is_rational`) + **affine stability** (`affine_rep_is_rep`) + **strict/indifference characterization** (PR #4250: `rep_strict_iff` `StrictPref ↔ E_p > E_q`, `rep_indifference_iff`, `strict_irrefl`). Existence direction documented as open milestone. |
| `Utility.lean` | ~30 | 0 | Umbrella imports + status doc |
| `Coherence/Basic.lean` | 52 | 0 | Finetti primitives — `Event` (= `Finset Ω`), `Price` (= `Event Ω → ℝ`), indicator `ind`, and the keystone `ind_inclusion_exclusion`. |
| `Coherence/DutchBook.lean` | 101 | 0 | **Constructive direction proven** (`non_additive_implies_dutch_book`, explicit stakes `(1,1,−1,−1)`/inverse) + contrapositive `coherent_on_implies_additive`. Full reciprocal (LP duality) documented as open milestone. |
| `Coherence/Probability.lean` | 255 | 0 | **Single-ticket coherence** (PR #4193: `single_coherent_iff_prob_bounds` — iff between single-ticket coherence and probability bounds `0 ≤ q ≤ 1`, via trichotomy on stake sign + explicit Dutch Books) + **weights-to-coherence** (PR #4244: `priceFromWeights_single_coherent`). The full `coherent_iff_probability` (arbitrary book sizes) remains open. |
| `Coherence.lean` | 33 | 0 | Umbrella imports + status doc |

## Why the optimality theorem is intractable

A complete proof of `gittins_optimality` requires:

1. **Optimal-stopping characterization** of the Gittins index (retirement value / fixed point),
2. **Index decomposability** across independent arms,
3. **Induction on the planning horizon**, and
4. A **formal expected value** over the reward distribution.

Mathlib (v4.30.0-rc2) has **no MDP, bandit, or Bellman-equation** formalization,
nor a measure-theoretic expected-value API suitable here. A full proof is
estimated at ~2000–5000 lines of supporting definitions — research-level, beyond
a single PR. The theorem is therefore **stated** (with the precise statement
preserved in its docstring) rather than silently weakened.

## Build

```bash
# From this directory (WSL required)
lake build Gittins
# Depends on Mathlib4 — first build is heavy, subsequent builds use the cache
```

## Notebook companion

[`Infer/Infer-9-Lean-Gittins.ipynb`](../DecisionTheory/Infer/Infer-9-Lean-Gittins.ipynb) — pedagogical
presentation of the bandit problem and the Gittins index, bridging the Infer.NET
probabilistic-programming material to the Lean formalization.

## See also

- **PR #2911** — `discount_monotone` proven closed-form (sorry 1→0)
- **`Probas/Infer/`** — Infer.NET probabilistic series (Bayesian inference, conjugate priors)
- **Epic #2651** — README/structure audit (Lean-series)
