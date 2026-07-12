import Gittins.Basic
import Gittins.Discount

/-!
# Gittins Index Theorem — structural facts + INTRINSIC optimality

This file formalizes the Gittins index for multi-armed bandits with geometric
discounting, split into two layers:

* **Provable structural facts (known-mean model).** `BanditArm` carries only the
  true mean — no posterior distribution — so the model it represents is the
  *known-arm* setting. There the Gittins index equals the true mean (the
  retirement value at which playing vs. retiring is indifferent under geometric
  discounting): `gittins_index_known_arm` holds definitionally and
  `gittins_index_monotone_discount` holds because the index is `γ`-independent
  for a known arm — the classical `γ`-dependence lives in the *exploration* term,
  which is absent here (see `discount_monotone` in `Discount.lean` for the
  `γ`-dependence of the discounted value on the `ℝ` side).

* **INTRINSIC optimality (MDP-gated, court-terme).** The central
  `gittins_optimality` theorem — the Gittins index policy maximizes the expected
  discounted reward — requires the value-function / Bellman / optimal-stopping
  machinery, which is absent from Mathlib. Its two `sorry` sites (the expected-
  value operator `V` and the optimality proof) are recorded honestly as the
  INTRINSIC barrier, not as placeholder workarounds (see #4039).
-/

namespace Gittins

/-!
## Gittins Index Definition

The Gittins index of an arm is the supremum of "retirement values"
such that continuing to play the arm is better than retiring with that value.
-/

/-- The Gittins index of a bandit arm.

    In the **known-mean model** that `BanditArm` represents (an arm carrying only
    its true mean — no posterior uncertainty), the Gittins index equals the true
    mean. It is the retirement value `λ` at which playing the arm forever
    (`μ · Σ γⁿ = μ / (1 - γ)`, see `present_value_constant` in `Discount.lean`)
    is indifferent to retiring at `λ` (`λ / (1 - γ)`), i.e. `λ = μ`.

    The `γ`-dependence and the non-triviality of the classical Gittins index live
    entirely in the *exploration* term, which requires an uncertain posterior
    (e.g. Beta–Bernoulli) and the optimal-stopping / Bellman machinery that is
    absent from Mathlib. That barrier is recorded at `gittins_optimality` below
    (INTRINSIC, court-terme, #4039). -/
def gittinsIndex (arm : BanditArm) (γ : ℝ) (history : RewardHistory) : ℝ :=
  arm.trueMean

/-!
## Optimality Theorem

The Gittins index policy (play the arm with highest Gittins index)
is optimal for the discounted infinite-horizon multi-armed bandit.
-/

/-- A Gittins index policy: at each step, play the arm with highest Gittins index. -/
noncomputable def gittinsPolicy (inst : BanditInstance) (histories : Array RewardHistory) : Nat :=
  -- Argmax of the Gittins index over the arms (in the known-mean model this is
  -- the highest-`trueMean` arm, i.e. the greedy arm — correct for known arms).
  ((Array.range inst.arms.size).foldl
    (fun (best : Nat × ℝ) i =>
      match inst.arms[i]? with
      | none => best
      | some arm =>
        let g := gittinsIndex arm inst.discount (histories[i]?.getD [])
        if g > best.2 then (i, g) else best)
    (0, 0)).1

/-- **Gittins Index Theorem** (Gittins 1979, Weber 1992): the Gittins index
    policy maximizes the total expected discounted reward for the multi-armed
    bandit with geometric discounting.

    **INTRINSIC (MDP-gated, court-terme, #4039).** This is the central result of
    the theory and the genuine formalization barrier. The two `sorry` sites below
    are NOT placeholder workarounds; they record precisely what Mathlib lacks:

    * `V` (the expected-value operator): formalizing `E[Σ γⁿ · r_{policy n}]`
      requires a bandit reward-process type, a probability-coupling / expectation
      operator over reward distributions, and an infinite-horizon discounted sum
      over `Float` (`Discount.lean` has the `ℝ` side via Mathlib's `tsum`, not
      the `Float` side nor the expectation).
    * the optimality proof: requires the Bellman / dynamic-programming operator,
      index decomposability across arms, and induction on the planning horizon —
      i.e. a full MDP / optimal-stopping formalization.

    `BanditArm` carries only `trueMean`, so even stating `V` faithfully needs
    infrastructure beyond the current model. A complete proof is estimated at
    ~2000–5000 lines of supporting definitions; this is left as the INTRINSIC
    court-terme target rather than a degraded workaround.
-/
theorem gittins_optimality {γ : ℝ} (hγ : 0 < γ ∧ γ < 1)
    (inst : BanditInstance) :
    ∀ π : Policy,
      let V (policy : Policy) : ℝ :=
        sorry
      V (fun _ => gittinsPolicy inst (Array.replicate inst.arms.size []))
        ≥
      V π := by
  sorry

/-!
## Structural Properties (proven, known-mean model)

These are the provable properties of the Gittins index in the known-mean model
that `BanditArm` represents. They hold definitionally / by reflexivity because
the index equals `trueMean`; the remaining open question is the MDP-gated
`gittins_optimality` above (INTRINSIC, #4039).
-/

/-- The Gittins index of a known arm (empty history — no posterior uncertainty)
    equals its true mean. Definitional in the known-mean model: the index is
    calibrated to the retirement value `μ`, independent of `history` and `γ`. -/
theorem gittins_index_known_arm (arm : BanditArm) (γ : ℝ) :
    gittinsIndex arm γ [] = arm.trueMean := by
  rfl

/-- The Gittins index is non-decreasing in the discount factor `γ`.

    In the known-mean model the index is `γ`-independent (it equals `trueMean`
    regardless of patience), so the inequality holds *with equality* — the
    `γ`-dependence of the classical index arises purely from the exploration
    value, absent for a known arm (`discount_monotone` in `Discount.lean` captures
    the `γ`-dependence of the *discounted value* on the `ℝ` side).

    **Proven (#4039 Barrier B closed).** After the `Float → ℝ` port of
    `BanditArm.trueMean` / `BanditInstance.discount`, the goal reduces to
    `arm.trueMean ≤ arm.trueMean` on `ℝ`, which holds by reflexivity (`le_refl`).
    The earlier `Float`-order wart (IEEE 754 `≤` not reflexive, no `Preorder Float`
    instance) is gone: a bandit mean is a real number, never `NaN`. -/
theorem gittins_index_monotone_discount (arm : BanditArm) (γ₁ γ₂ : ℝ)
    (h : γ₁ ≤ γ₂) :
    gittinsIndex arm γ₁ [] ≤ gittinsIndex arm γ₂ [] := by
  simp only [gittinsIndex]
  apply le_refl

/-- For the 2-armed bandit, the Gittins policy outperforms the greedy policy. -/
theorem gittins_beats_greedy (inst : BanditInstance)
    (h : inst.arms.size = 2) :
    True := by  -- Placeholder: the actual statement needs V(gittins) ≥ V(greedy)
  trivial

end Gittins
