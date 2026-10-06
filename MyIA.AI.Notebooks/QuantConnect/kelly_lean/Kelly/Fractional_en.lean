import Mathlib
import Kelly.Bet_en
import Kelly.Growth_en
import Kelly.Kelly_en

/-!
# Kelly.Fractional — fundamental inequality of *fractional* Kelly

The Kelly fraction `f* = (b·p − q)/b` maximizes the expected growth rate
`g(f) = p·log(1 + b·f) + q·log(1 − f)`. This module proves the **fractional
Kelly inequality**: for `c ∈ [0, 1]`, betting the fraction `c·f*` never
outperforms the full optimal fraction:

    growth(c·f*) ≤ growth(f*)     (with equality iff c = 1)

This is the **formal justification of the *half-Kelly*** (c = 1/2), and more
generally of all *position sizing* strategies that shrink the optimal fraction
to trade some log-growth for much smaller variance (cf. Thorp, *The Kelly
Criterion in Blackjack, Sports Betting, and the Stock Market*; see also the
companion notebook `Kelly_companion-Fractional-Python.ipynb` which **measures**
this trade-off).

## Proof strategy

We do **not** invoke the concavity of `growth` (that strategy is sidestepped in
`Kelly.lean` itself — cf. comment `Growth.lean:22`). We prove directly that
`c·f*` stays inside the **admissible region** `(−1/b, 1)` whenever `f*` does,
then apply the **flagship theorem** `kelly_optimal`:

1. `c·f* ∈ [0, f*]` when `f* ≥ 0` (and `c·f* ∈ [f*, 0]` when `f* < 0`),
   but in both cases `c·f*` is sandwiched in `(−1/b, 1)`.
2. `kelly_optimal β (c·f*)` (which applies to **any** admissible fraction)
   then gives directly `growth(c·f*) ≤ growth(f*)`.

Equality at `c = 1` is trivial (`1·f* = f*`). Strict inequality for
`c < 1` and `f* ≠ 0` (a bet with non-zero edge) follows from `kelly_unique` —
the same logic, with the strict version of the flagship theorem.

Reference: see issue #19516 (growth plan #16231).
-/

namespace KellyLean_en

open Real

/-- The fraction `c·f*` (c ∈ [0, 1]) stays inside the **admissible region** `(−1/b, 1)`
    whenever `f*` itself does. The case `f* < 0` is subtler: we then have
    `c·f* ∈ [f*, 0]`, but the lower bound `f* > −1/b` (since f* is admissible) still
    protects us. -/
lemma fractional_feasible (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Feasible β (c * kellyFrac β) := by
  obtain ⟨hfs_left, hfs_right⟩ := kellyFrac_feasible β
  refine ⟨?_, ?_⟩
  · -- -1/b < c·f*
    -- Case c = 0 : c·f* = 0 > -1/b (b > 0).
    -- Case c > 0 : multiply hfs_left by c ; then -c/b ≥ -1/b (c ≤ 1, b > 0).
    rcases eq_or_lt_of_le hc0 with rfl | hc0_pos
    · simp [β.hb_pos]
    · -- hfs_left : -1/b < f* ; hc0_pos : 0 < c ; so c·f* > c·(-1/b) = -c/b
      have h1 : c * (-(1 / β.b)) < c * kellyFrac β :=
        (mul_lt_mul_left hc0_pos).mpr hfs_left
      -- -c/b ≥ -1/b (since c ≤ 1 and b > 0)
      have h2 : -(1 / β.b) ≤ c * (-(1 / β.b)) := by
        rw [neg_mul, neg_div]
        exact div_le_div_of_nonneg_right (by linarith [hc1]) β.hb_pos.le
      linarith
  · -- c·f* < 1
    -- Case c = 0 : 0 < 1 trivially.
    -- Case c > 0 : c·f* < c·1 = c ≤ 1.
    rcases eq_or_lt_of_le hc0 with rfl | hc0_pos
    · simp
    · have h1 : c * kellyFrac β < c * 1 := (mul_lt_mul_left hc0_pos).mpr hfs_right
      linarith [hc1]

/-- **Fundamental inequality of *fractional Kelly***: for `c ∈ [0, 1]`,
    `growth(c·f*) ≤ growth(f*)`. This is the formal justification of the
    *half-Kelly*: betting a fraction `c` of the optimal fraction `f*` never
    outperforms the full optimal stake. Follows from `kelly_optimal` applied
    to `c·f*` (admissible by `fractional_feasible`). -/
theorem growth_fractional_le (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    growth β (c * kellyFrac β) ≤ growth β (kellyFrac β) :=
  kelly_optimal β (c * kellyFrac β) (fractional_feasible β c hc0 hc1)

/-- **Equality at c = 1**: the fraction `1·f*` returns `f*`, hence the same
    growth. This is the upper bound of `growth_fractional_le` (attained at
    `c = 1`). -/
theorem growth_fractional_eq_one (β : Bet) :
    growth β (1 * kellyFrac β) = growth β (kellyFrac β) := by
  simp

/-- **Strict inequality for c < 1 and a bet with non-zero edge**: if `c ∈ [0, 1)`
    and `f* ≠ 0` (the bet has an advantage), then `growth(c·f*) < growth(f*)`.
    Follows from `kelly_unique` applied to `c·f*` (admissible and distinct from
    `f*`). Special case of the *half-Kelly* (c = 1/2) on a favourable bet. -/
theorem growth_fractional_lt (β : Bet) (c : ℝ) (hc0 : 0 ≤ c) (hclt : c < 1)
    (hfne : kellyFrac β ≠ 0) :
    growth β (c * kellyFrac β) < growth β (kellyFrac β) := by
  -- c·f* is admissible (hclt.le = hc1)
  have hfeas := fractional_feasible β c hc0 hclt.le
  -- c·f* ≠ f* : if c·f* = f* then (1-c)·f* = 0
  have hne : c * kellyFrac β ≠ kellyFrac β := by
    intro heq
    have hmul : (1 - c) * kellyFrac β = 0 := by
      have h1 := congrArg (fun x => x - kellyFrac β) heq
      linarith
    rcases mul_eq_zero.mp hmul with h1 | h2
    · linarith
    · exact hfne h2
  exact kelly_unique β (c * kellyFrac β) hfeas hne

end KellyLean_en