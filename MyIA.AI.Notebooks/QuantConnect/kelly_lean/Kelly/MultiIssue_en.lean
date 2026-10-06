import Mathlib
import Kelly.Bet_en
import Kelly.Growth_en
import Kelly.Kelly_en

/-!
# Kelly.MultiIssue — multi-bet extension of the Kelly criterion (independent case, N = 2)

The Kelly theorem (cf. `Kelly.Kelly`) maximises the log-growth `g(f)` for a
**single** Bernoulli bet. This generalisation handles the **independent
multi-bet** case with two bets (the general N-bet case follows by induction,
see note below): given two independent bets `β_1, β_2` (each with its own
probability and net odds), the optimal allocation `(f_1, f_2)` maximises the
**sum** of individual log-growths:

    growth(β_1, f_1) + growth(β_2, f_2)

## Proof strategy

We avoid abstract joint optimisation and exploit the **separability** of the
problem: the sum is a linear operator, and the log-growth of each bet depends
only on its own `f_i`. Fix `f_2` and optimise in `f_1` (`kelly_optimal` gives
`f_1* = kellyFrac β_1` independently of `f_2`); then fix `f_1 = kellyFrac β_1`
and optimise in `f_2` (same argument, `f_2* = kellyFrac β_2`). The pair
`(kellyFrac β_1, kellyFrac β_2)` is therefore the **joint maximiser**.

**Uniqueness** follows from `kelly_unique`: if one of the `f_i` differs from
`kellyFrac`, the joint log-growth is strictly smaller, regardless of the other
component.

## General case (N bets)

The extension to N independent bets follows by induction: adding a bet to an
optimal family preserves optimality because the new bet is independent of the
others and maximises its own log-growth by `kelly_optimal` (the N = 1 case
reduces to `kelly_optimal` itself).

## Module lemmas

| Name | Type | Role |
|---|---|---|
| `jointGrowth2` | `def` | Sum of two bets' log-growths |
| `multiKelly_optimal_2` | `theorem` | Any feasible allocation ≤ (kellyFrac β_1, kellyFrac β_2) |
| `multiKelly_unique_2` | `theorem` | If an `f_i` differs, joint log-growth is strictly < |
| `multiKelly_unique_2'` | `theorem` | Symmetric variant on f_2 |

See issue #19516, carnet 3 of plan #16231.
-/

namespace KellyLean_en

open Real

/-- The **joint log-growth** of two bets: sum of individual log-growths. For
    independent bets, the expected log-capital after one step is indeed the
    sum of contributions (total capital is the product of multipliers, whose
    log is the sum of logs). -/
noncomputable def jointGrowth2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ) : ℝ :=
  growth β₁ f₁ + growth β₂ f₂

/-- **Multi-bet Kelly theorem at 2 bets (maximiser)**: for two independent
    bets `β₁, β₂`, the Kelly allocation `(kellyFrac β₁, kellyFrac β₂)`
    maximises the joint log-growth. For any feasible allocation `(f₁, f₂)`,

        jointGrowth2 β₁ β₂ f₁ f₂ ≤ jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂)

    **Proof strategy**: by `kelly_optimal` applied to each component (the bets
    are independent, so the inequalities add up). -/
theorem multiKelly_optimal_2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂) :
    jointGrowth2 β₁ β₂ f₁ f₂ ≤
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_optimal β₁ f₁ hf₁
  have h₂ := kelly_optimal β₂ f₂ hf₂
  linarith

/-- **Multi-bet Kelly theorem at 2 bets (uniqueness)**: if one of the `f_i`
    differs from `kellyFrac β_i`, the joint log-growth is strictly smaller.
    Follows from `kelly_unique` applied to the differing component (the
    other being dominated by `kelly_optimal` which gives a non-strict ≤
    inequality, addition preserves the strict inequality on the differing
    component). -/
theorem multiKelly_unique_2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂)
    (hf₁ne : f₁ ≠ kellyFrac β₁) :
    jointGrowth2 β₁ β₂ f₁ f₂ <
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_unique β₁ f₁ hf₁ hf₁ne
  have h₂ := kelly_optimal β₂ f₂ hf₂
  linarith

/-- **Symmetric**: if `f₂ ≠ kellyFrac β₂`, the joint log-growth is strictly
    smaller. Variant of `multiKelly_unique_2` by symmetry. -/
theorem multiKelly_unique_2' (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂)
    (hf₂ne : f₂ ≠ kellyFrac β₂) :
    jointGrowth2 β₁ β₂ f₁ f₂ <
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_optimal β₁ f₁ hf₁
  have h₂ := kelly_unique β₂ f₂ hf₂ hf₂ne
  linarith

end KellyLean_en
