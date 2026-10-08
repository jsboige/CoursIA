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
  have hfeas := kellyFrac_feasible β
  -- hfeas.1 : -1/β.b < kellyFrac β
  -- hfeas.2 : kellyFrac β < 1
  refine ⟨?_, ?_⟩
  · -- -1/β.b < c·f* : exploit `kellyFrac_feasible.1` (hfeas.1) + c ∈ [0, 1].
    -- Case c = 0 : c·f* = 0 > -1/b. Case c > 0, c < 1 : c·(-1/b) > -1/b
    -- (c < 1, b > 0) then c·f* > c·(-1/b) (hfeas.1, c > 0). Case c = 1 :
    -- c·f* = f* > -1/b (hfeas.1). Avoids the `mul_assoc` route of the broken
    -- commit (Lean 4.33 changed the behaviour of rewrites on 3-factor products).
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · rw [zero_mul]
      -- -1 / β.b < 0.  Just use `linarith` on the explicit positive of 1/β.b.
      -- The contradiction arises because -1/β.b is the negation of 1/β.b and
      -- they have opposite signs.
      have hpos : 0 < 1 / β.b := one_div_pos.mpr β.hb_pos
      -- (-1/β.b) + (1/β.b) = 0, and 1/β.b > 0, so 1/β.b > 0 implies -1/β.b < 0.
      linarith [show (1 / β.b) + (-1 / β.b) = 0 from by ring, hpos]
    · -- 0 < c
      rcases lt_or_ge c 1 with hclt | hcge
      · -- 0 < c < 1
        have hm1 : -1 / β.b < c * (-1 / β.b) := by
          have h1 : -1 * (1 / β.b) = -1 / β.b := by ring
          have h2 : c * (-1 / β.b) = -c * (1 / β.b) := by ring
          have h3 : -1 * (1 / β.b) < -c * (1 / β.b) :=
            mul_lt_mul_of_pos_right (by linarith : -1 < -c) (one_div_pos.mpr β.hb_pos)
          linarith [h1, h2, h3]
        have hm2 : c * (-1 / β.b) < c * kellyFrac β := mul_lt_mul_of_pos_left hfeas.1 hcpos
        linarith [hm1, hm2]
      · -- 0 < c and c ≥ 1 and c ≤ 1, hence c = 1
        have h1 : c = 1 := le_antisymm hc1 hcge
        rw [h1, one_mul]
        exact hfeas.1
  · -- c·f* < 1 : symmetrically, exploit `kellyFrac_feasible.2` (hfeas.2).
    -- Case c = 0 : c·f* = 0 < 1. Case c > 0 : c·f* < c·1 = c ≤ 1
    -- (hfeas.2, c > 0 then hc1).
    rcases eq_or_lt_of_le hc0 with rfl | hcpos
    · simp  -- c = 0
    · have hmul : c * kellyFrac β < c * 1 := mul_lt_mul_of_pos_left hfeas.2 hcpos
      linarith [hmul, hc1]

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