import Mathlib
import Kelly.Bet_en

/-!
# Kelly.Growth — the expected growth rate `g(f) = E[log(wealth)]`

The **expected growth rate** of a Bernoulli bet under fraction `f` is

    g(f) = p · log(1 + b·f) + q · log(1 − f)

where `p` (resp. `q`) is the win (resp. loss) probability and `b` the net odds.
Maximizing `g` amounts to maximizing the **asymptotic growth of compounded capital**
over infinitely many independent bets (this is Kelly optimality). See issue #4052.

This module defines `growth` and `growthGrad`, and establishes the **baseline facts**
(zero growth without betting, slope at the origin = the edge). The strict concavity of
`g` over the admissible region (a `g''(f) < 0` computation) is the proof strategy
**bypassed** by the flagship optimality theorem, which directly proves `g(f) ≤ g(f*)`
via the tangent `log t ≤ t − 1` rather than invoking abstract concavity — that flagship
lives in `Kelly.lean`.
-/

namespace KellyLean_en

open Real

/-- The **expected growth rate** `g(f) = p·log(1 + b·f) + q·log(1 − f)`:
    expectation of the logarithm of relative wealth. -/
noncomputable def growth (β : Bet) (f : ℝ) : ℝ :=
  β.p * log (winWealth β f) + q β * log (loseWealth β f)

/-- The **slope** (derivative) of the growth rate: `g'(f) = p·b/(1+bf) − q/(1−f)`.
    This is the quantity whose vanishing characterizes the optimal fraction. It is
    exposed explicitly because it is at the heart of the optimality theorem (first-order
    condition `growthGrad β f* = 0`). -/
noncomputable def growthGrad (β : Bet) (f : ℝ) : ℝ :=
  β.p * β.b / winWealth β f - q β / loseWealth β f

/-- **Zero growth without betting**: `g(0) = 0`. Betting nothing (`f = 0`) leaves the
    capital unchanged — both wealth multipliers equal `1`, and `log 1 = 0`. This is the
    **baseline** of the Kelly criterion: any fraction `f` with `g(f) > 0` beats "do
    nothing", any fraction with `g(f) < 0` is worse (cf `Kelly.kelly_optimal`, which
    guarantees `g(f) ≤ g(f*)` and, the edge being positive, `g(f*) > 0 = g(0)`). -/
lemma growth_zero (β : Bet) : growth β 0 = 0 := by
  unfold growth winWealth loseWealth
  simp [Real.log_one]

/-- **Slope at the origin = the edge**: `g'(0) = b·p − q`. With no stake (`f = 0`), the
    slope of the log-growth equals exactly the "edge" `b·p − q` — i.e. the **numerator**
    of the Kelly fraction `f* = (b·p − q)/b`. Thus `g'(0) > 0` ⟺ `f* > 0` (favorable
    bet, bet), `g'(0) < 0` ⟺ `f* < 0` (unfavorable bet, short). This is the bridge
    between the local geometry of `g` (its slope at `0`) and the sign of the optimal
    stake. -/
lemma growthGrad_zero (β : Bet) : growthGrad β 0 = β.p * β.b - q β := by
  unfold growthGrad winWealth loseWealth
  simp [div_one]

end KellyLean_en
