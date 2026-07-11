import Mathlib
import Kelly.Bet_en
import Kelly.Growth_en

/-!
# Kelly.Kelly — optimality of the fraction `f*` (Kelly criterion)

The **Kelly theorem**: the optimal fraction to bet on a Bernoulli bet (win probability
`p`, net odds `b`) is

    f* = (b·p − q) / b        (q = 1 − p)

which **uniquely maximizes** the expected growth rate `g(f) = p·log(1+bf) +
q·log(1−f)`. Any over-bet (`f > f*`) or under-bet (`f < f*`) is strictly suboptimal.

## Proof strategy

We avoid abstract concavity and prove `g(f) ≤ g(f*)` **directly** via the tangent of
the logarithm at 1, `log t ≤ t − 1` (with equality iff `t = 1`). Writing

    g(f) − g(f*) = p · log((1+bf)/(1+bf*)) + q · log((1−f)/(1−f*))

and applying `log t ≤ t − 1` to each ratio yields

    g(f) − g(f*) ≤ (f − f*) · [p·b/(1+bf*) − q/(1−f*)] = (f − f*) · g'(f*).

Now `g'(f*) = 0` (first-order condition, verified by computation). Hence
`g(f) ≤ g(f*)`. Uniqueness follows from the strict version `log t < t − 1` for
`t ≠ 1`: if `f ≠ f*`, the ratios differ from `1`, so the inequalities are strict, and
`g(f) < g(f*)`.

Reference: J. L. Kelly Jr., *A New Interpretation of Information Rate*, BSTT (1956).
See issue #4052.
-/

namespace KellyLean_en

open Real

/-- The **Kelly fraction** `f* = (b·p − q)/b` (the optimal stake per unit of capital). -/
noncomputable def kellyFrac (β : Bet) : ℝ := (β.b * β.p - q β) / β.b

/-- The Kelly fraction lies in the admissible region `(−1/b, 1)`: both wealth
    multipliers at `f*` are strictly positive. -/
lemma kellyFrac_feasible (β : Bet) : Feasible β (kellyFrac β) := by
  have hb := β.hb_pos
  -- kellyFrac β * β.b = β.b·p − (1 − p)  (on multiplie par b > 0)
  have hkf : kellyFrac β * β.b = β.b * β.p - (1 - β.p) := by
    simp [kellyFrac, q]; field_simp [hb.ne']
  refine ⟨?_, ?_⟩
  · -- −1/b < f*  ⟺  −1 < f*·b  (b > 0)
    rw [div_lt_iff₀ hb, hkf]
    nlinarith [β.hp_pos, hb]
  · -- f* < 1  ⟺  1 − f* = (1 − p)·(b + 1)/b > 0
    have h1f : 1 - kellyFrac β = (1 - β.p) * (β.b + 1) / β.b := by
      unfold kellyFrac q; field_simp [β.hb_pos.ne']; ring
    have hpos : 0 < 1 - kellyFrac β := by
      rw [h1f]
      exact div_pos (mul_pos (by linarith [β.hp_lt_one]) (b_add_one_pos β)) β.hb_pos
    linarith

/-- Win multiplier evaluated at `f*`: `winWealth β f* = p · (b + 1)`. -/
lemma winWealth_kelly (β : Bet) : winWealth β (kellyFrac β) = β.p * (β.b + 1) := by
  unfold winWealth kellyFrac q; field_simp [β.hb_pos.ne']; ring

/-- Loss multiplier evaluated at `f*`: `loseWealth β f* = q · (b + 1) / b`. -/
lemma loseWealth_kelly (β : Bet) : loseWealth β (kellyFrac β) = q β * (β.b + 1) / β.b := by
  unfold loseWealth kellyFrac q; field_simp [β.hb_pos.ne']; ring

/-- **First-order condition**: the slope of the log-growth vanishes at `f*`,
    `g'(f*) = growthGrad β f* = 0`. -/
lemma growthGrad_kelly_zero (β : Bet) : growthGrad β (kellyFrac β) = 0 := by
  have hq : q β ≠ 0 := (q_pos β).ne'
  have hbo : β.b + 1 ≠ 0 := (b_add_one_pos β).ne'
  have hpb : β.p * (β.b + 1) ≠ 0 := mul_ne_zero β.hp_pos.ne' hbo
  rw [growthGrad, winWealth_kelly, loseWealth_kelly]
  field_simp [β.hp_pos.ne', hq, β.hb_pos.ne', hbo, hpb]
  ring

/-- **Key upper bound**: for any admissible fraction `f`,
    `g(f) − g(f*) ≤ (f − f*) · g'(f*)`. Follows from `log t ≤ t − 1` applied to both
    ratios. -/
lemma growth_diff_le (β : Bet) (f : ℝ) (hf : Feasible β f) :
    growth β f - growth β (kellyFrac β) ≤ (f - kellyFrac β) * growthGrad β (kellyFrac β) := by
  have hfs := kellyFrac_feasible β
  set fstar := kellyFrac β with hfstar
  have hwp := winWealth_pos_of_feasible β f hf
  have hwl := loseWealth_pos_of_feasible β f hf
  have hwsp := winWealth_pos_of_feasible β fstar hfs
  have hwlp := loseWealth_pos_of_feasible β fstar hfs
  -- g(f) − g(f*) = p·log(Ww_f/Ww_*) + q·log(Wl_f/Wl_*)
  have h1 : log (winWealth β f / winWealth β fstar) =
      log (winWealth β f) - log (winWealth β fstar) := Real.log_div hwp.ne' hwsp.ne'
  have h2 : log (loseWealth β f / loseWealth β fstar) =
      log (loseWealth β f) - log (loseWealth β fstar) := Real.log_div hwl.ne' hwlp.ne'
  have hdiffeq : growth β f - growth β fstar =
      β.p * log (winWealth β f / winWealth β fstar) +
        q β * log (loseWealth β f / loseWealth β fstar) := by
    unfold growth; rw [h1, h2]; ring
  -- borne chaque rapport via log t ≤ t − 1 (en fait : égalité algébrique du majorant)
  have hwin_bound : log (winWealth β f / winWealth β fstar) ≤
      (f - fstar) * (β.b / winWealth β fstar) := by
    refine (log_le_sub_one_of_pos (div_pos hwp hwsp)).trans ?_
    simp only [winWealth] at hwsp ⊢
    field_simp [hwsp.ne']
    linarith
  have hlose_bound : log (loseWealth β f / loseWealth β fstar) ≤
      (f - fstar) * (-1 / loseWealth β fstar) := by
    refine (log_le_sub_one_of_pos (div_pos hwl hwlp)).trans ?_
    simp only [loseWealth] at hwlp ⊢
    field_simp [hwlp.ne']
    linarith
  -- combine (p,q > 0 préservent les inégalités)
  calc growth β f - growth β fstar
      = β.p * log (winWealth β f / winWealth β fstar) +
          q β * log (loseWealth β f / loseWealth β fstar) := hdiffeq
    _ ≤ β.p * ((f - fstar) * (β.b / winWealth β fstar)) +
          q β * ((f - fstar) * (-1 / loseWealth β fstar)) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hwin_bound β.hp_pos.le
        · exact mul_le_mul_of_nonneg_left hlose_bound (q_pos β).le
    _ = (f - fstar) * growthGrad β fstar := by
        rw [growthGrad]; field_simp [hwsp.ne', hwlp.ne']; ring

/-- **Kelly theorem** (maximizer): `f*` maximizes the expected growth rate.
    For any admissible fraction `f`, `g(f) ≤ g(f*)`. -/
theorem kelly_optimal (β : Bet) (f : ℝ) (hf : Feasible β f) :
    growth β f ≤ growth β (kellyFrac β) := by
  have hbound := growth_diff_le β f hf
  rw [growthGrad_kelly_zero, mul_zero] at hbound
  linarith

/-- **Over-bet and under-bet are strictly suboptimal**: if `f ≠ f*` is admissible,
    then `g(f) < g(f*)` (uniqueness of the maximizer). Follows from `log t < t − 1` for
    `t ≠ 1`. -/
theorem kelly_unique (β : Bet) (f : ℝ) (hf : Feasible β f) (hfne : f ≠ kellyFrac β) :
    growth β f < growth β (kellyFrac β) := by
  have hfs := kellyFrac_feasible β
  set fstar := kellyFrac β with hfstar
  have hwp := winWealth_pos_of_feasible β f hf
  have hwl := loseWealth_pos_of_feasible β f hf
  have hwsp := winWealth_pos_of_feasible β fstar hfs
  have hwlp := loseWealth_pos_of_feasible β fstar hfs
  -- f ≠ f* ⟹ les multiplicateurs de richesse diffèrent (1+b·_ et 1−_ sont injectifs)
  have hwin_inj : winWealth β f = winWealth β fstar → f = fstar := by
    intro h
    unfold winWealth at h
    have : β.b * f = β.b * fstar := by linarith
    exact mul_left_cancel₀ β.hb_pos.ne' this
  have hlose_inj : loseWealth β f = loseWealth β fstar → f = fstar := by
    intro h; unfold loseWealth at h; linarith
  have hwinne : winWealth β f / winWealth β fstar ≠ 1 := by
    intro heq
    apply hfne
    apply hwin_inj
    field_simp [hwsp.ne'] at heq
    exact heq
  have hlosene : loseWealth β f / loseWealth β fstar ≠ 1 := by
    intro heq
    apply hfne
    apply hlose_inj
    field_simp [hwlp.ne'] at heq
    exact heq
  -- versions strictes : log t < t − 1 pour t ≠ 1
  have h1 : log (winWealth β f / winWealth β fstar) =
      log (winWealth β f) - log (winWealth β fstar) := Real.log_div hwp.ne' hwsp.ne'
  have h2 : log (loseWealth β f / loseWealth β fstar) =
      log (loseWealth β f) - log (loseWealth β fstar) := Real.log_div hwl.ne' hwlp.ne'
  have hdiffeq : growth β f - growth β fstar =
      β.p * log (winWealth β f / winWealth β fstar) +
        q β * log (loseWealth β f / loseWealth β fstar) := by
    unfold growth; rw [h1, h2]; ring
  -- f ≠ f* ⟹ AU MOINS l'un des rapports diffère de 1 ; utilisons la borne stricte
  have hwin_strict : log (winWealth β f / winWealth β fstar) <
      (f - fstar) * (β.b / winWealth β fstar) := by
    refine (log_lt_sub_one_of_pos (div_pos hwp hwsp) hwinne).trans_le ?_
    simp only [winWealth] at hwsp ⊢
    field_simp [hwsp.ne']
    linarith
  have hlose_strict : log (loseWealth β f / loseWealth β fstar) <
      (f - fstar) * (-1 / loseWealth β fstar) := by
    refine (log_lt_sub_one_of_pos (div_pos hwl hwlp) hlosene).trans_le ?_
    simp only [loseWealth] at hwlp ⊢
    field_simp [hwlp.ne']
    linarith
  have hgrad0 : growthGrad β fstar = 0 := growthGrad_kelly_zero β
  have hdiff : growth β f - growth β fstar < 0 := by
    calc growth β f - growth β fstar
        = β.p * log (winWealth β f / winWealth β fstar) +
            q β * log (loseWealth β f / loseWealth β fstar) := hdiffeq
      _ < β.p * ((f - fstar) * (β.b / winWealth β fstar)) +
            q β * ((f - fstar) * (-1 / loseWealth β fstar)) := by
          refine add_lt_add ?_ ?_
          · exact mul_lt_mul_of_pos_left hwin_strict β.hp_pos
          · exact mul_lt_mul_of_pos_left hlose_strict (q_pos β)
      _ = (f - fstar) * growthGrad β fstar := by
          rw [growthGrad]; field_simp [hwsp.ne', hwlp.ne']; ring
      _ = 0 := by rw [hgrad0, mul_zero]
  linarith

/-! ## 8. Practical criterion: bet iff the edge is positive

The operational decision rule of the Kelly criterion: the optimal fraction `f*` is
**strictly positive exactly when the bet is favorable** (`b·p − q > 0`). Conversely,
an unfavorable bet (`b·p − q < 0`) yields `f* < 0`: the maximizer flips to the short
side. The neutral case `b·p − q = 0` (actuarially fair bet) yields `f* = 0`: staking
nothing is optimal. This sign equivalence is the formal counterpart of the prose in
`Growth.lean` (§ the "edge" `g'(0) = b·p − q`).
-/

/-- **Kelly fraction positive iff bet is favorable**: `f* > 0` exactly when the
    "edge" `b·p − q` is strictly positive (the bet is advantageous, `b·p > q`). This
    is Kelly's practical criterion — only bet the long side if one holds a
    mathematical edge. Follows directly from `f* = (b·p − q)/b` with `b > 0`: the sign
    of the fraction equals that of the numerator. -/
theorem kellyFrac_pos_iff (β : Bet) :
    0 < kellyFrac β ↔ 0 < β.b * β.p - q β := by
  unfold kellyFrac
  rw [lt_div_iff₀ β.hb_pos, zero_mul]

/-- **Positive edge iff positive Kelly**: the log-growth gradient at `f = 0` (the
    "edge" `g'(0) = b·p − q`, cf `growthGrad_zero`) is strictly positive exactly when
    the optimal fraction `f*` is. Formally realizes the decision rule "bet iff
    `g'(0) > 0`": the initial slope of the log-growth signs the direction of the
    optimal stake (long if positive, short if negative, flat if zero). -/
theorem growthGrad_zero_pos_iff (β : Bet) :
    0 < growthGrad β 0 ↔ 0 < kellyFrac β := by
  rw [growthGrad_zero, kellyFrac_pos_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

/-- **Kelly fraction negative iff bet is unfavorable**: `f* < 0` exactly when the
    "edge" `b·p − q` is strictly negative (the bet is disadvantageous, `b·p < q`).
    The maximizer then flips to the short side. Formalizes the second case of the
    §8 prose ("an unfavorable bet yields `f* < 0`"). -/
theorem kellyFrac_neg_iff (β : Bet) :
    kellyFrac β < 0 ↔ β.b * β.p - q β < 0 := by
  unfold kellyFrac
  rw [div_lt_iff₀ β.hb_pos, zero_mul]

/-- **Negative edge iff negative Kelly**: the initial slope `g'(0) = b·p − q` is
    strictly negative exactly when `f* < 0`. The short direction is signed by the
    log-growth slope at the origin. -/
theorem growthGrad_zero_neg_iff (β : Bet) :
    growthGrad β 0 < 0 ↔ kellyFrac β < 0 := by
  rw [growthGrad_zero, kellyFrac_neg_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

/-- **Kelly fraction zero iff actuarially fair bet**: `f* = 0` exactly when the
    "edge" `b·p − q` is zero (a fair bet, `b·p = q`). Staking nothing is then
    optimal. Formalizes the neutral case of the §8 prose. -/
theorem kellyFrac_eq_zero_iff (β : Bet) :
    kellyFrac β = 0 ↔ β.b * β.p - q β = 0 := by
  unfold kellyFrac
  rw [div_eq_iff₀ β.hb_pos.ne', zero_mul]

/-- **Zero edge iff zero Kelly**: the initial slope `g'(0)` vanishes exactly when
    `f* = 0`. The neutral regime where staking nothing is optimal — the boundary
    between the long and short regimes. -/
theorem growthGrad_zero_eq_zero_iff (β : Bet) :
    growthGrad β 0 = 0 ↔ kellyFrac β = 0 := by
  rw [growthGrad_zero, kellyFrac_eq_zero_iff]
  constructor <;> intro h <;> linarith [mul_comm β.p β.b]

end KellyLean_en
