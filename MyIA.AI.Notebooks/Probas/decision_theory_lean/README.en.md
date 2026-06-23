# decision_theory_lean — Decision Theory (Lean 4)

Lake **at the `Probas` series root**, formalizing canonical decision-theory
results — visible from both series tracks (Infer.NET / PyMC). First module
delivered: the **multi-armed bandit** problem and the **Gittins index** (Gittins
1979, Weber 1992) — the optimal policy for the discounted infinite-horizon
bandit. The **geometric-discount building blocks are fully proven** (PR #2911);
the **marquee optimality theorem is stated but intractable** in the current
Mathlib (no MDP/Bellman formalization), held as `sorry`.

Planned modules (Lean roadmap #4038): **von Neumann–Morgenstern** representation
(#4049) and **Dutch Book / de Finetti** coherence (#4050). Lean companion notebook:
[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb).

## Status

- **Toolchain**: `leanprover/lean4:v4.30.0-rc2`
- **Sorry**: **5** — all in `GittinsTheorem.lean` (the optimality theorem + index
  properties). `Discount.lean` = **0 sorry** (fully proven), `Basic.lean` = 0.
- **Build**: `lake build Gittins` (depends on Mathlib4)
- **Dependencies**: Mathlib4 (`v4.30.0-rc2`) — real analysis for the discount lemmas

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
| `Gittins/Discount.lean` | 68 | 0 | Geometric discounting **proven** via Mathlib real analysis: `geometric_series_converges`, `one_minus_gamma_pos`, `present_value_constant`, `discount_monotone`. |
| `Gittins/GittinsTheorem.lean` | 96 | 5 | The marquee theorem **stated with sorry**: `gittinsIndex`, `gittinsPolicy` (argmax), `gittins_optimality`, `gittins_index_known_arm`, `gittins_index_monotone_discount`. (`gittins_beats_greedy` is a `: True := trivial` placeholder, not a sorry.) |
| `Gittins.lean` | 19 | 0 | Umbrella imports |

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

[`Infer/Infer-20b-Lean-Gittins.ipynb`](../Infer/Infer-20b-Lean-Gittins.ipynb) — pedagogical
presentation of the bandit problem and the Gittins index, bridging the Infer.NET
probabilistic-programming material to the Lean formalization.

## See also

- **PR #2911** — `discount_monotone` proven closed-form (sorry 1→0)
- **`Probas/Infer/`** — Infer.NET probabilistic series (Bayesian inference, conjugate priors)
- **Epic #2651** — README/structure audit (Lean-series)
