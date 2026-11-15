import Gittins.Basic_en
import Gittins.Discount_en

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
  machinery, which is absent from Mathlib. The value operator `V` is no longer a
  hole: `discountedValue` defines it over what the model actually carries
  (known means, hence a discounted sum **without expectation**), and it is that
  definition which makes the statement checkable instead of circular.
  **One** `sorry` site remains — the optimality proof — recorded honestly as the
  INTRINSIC barrier, not as a placeholder workaround (see #4039).
-/

namespace Gittins_en

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

/-- The mean reward of the arm that policy `π` plays at step `n`, and `0` when
    that index names no arm of the instance.

    This is the only reward this model can name: `BanditArm` carries only
    `trueMean`, so there is here neither a distribution to sample nor an
    expectation to take. -/
noncomputable def policyMeanAt (inst : BanditInstance) (π : Policy) (n : ℕ) : ℝ :=
  match inst.arms[π n]? with
  | some arm => arm.trueMean
  | none => 0

/-- **Discounted value of a policy** in the known-mean model:
    `V π = Σₙ γⁿ · μ(π n)`.

    This is a `tsum` over `ℝ` and **not an expectation**: the setting `BanditArm`
    represents is that of arms with known means, where each step's reward equals
    its true mean, with no randomness. Writing an `E[…]` here would misrepresent
    what the type carries; the probabilistic version (Beta–Bernoulli posterior,
    exploration term) is the INTRINSIC barrier documented below — it is not this
    definition, which is precisely why the statement below is restricted to this
    setting instead of promising the general theorem.

    Under `0 < γ < 1` and bounded means the series converges;
    `present_value_constant` is the constant-reward case. -/
noncomputable def discountedValue (inst : BanditInstance) (π : Policy) : ℝ :=
  ∑' n : ℕ, inst.discount ^ n * policyMeanAt inst π n

/-- **Gittins Index Theorem, in the setting this lake formalizes**
    (Gittins 1979, Weber 1992 for the general statement): with known means, the
    Gittins index policy maximizes the discounted value `discountedValue` over
    all policies.

    **What this statement does not say, and does not claim to say.** The Gittins
    theorem concerns *uncertain* arms, where the index arbitrates exploration
    against exploitation — that is where it differs from the greedy policy. Here
    `gittinsIndex` equals `trueMean` (`gittins_index_known_arm`) and the index
    policy **coincides** with the greedy one (`gittinsPolicy_eq_greedyPolicy`), so
    the statement is the optimality of the greedy policy under known means, and it
    is true as such. The uncertain setting — hence the theorem in its real scope —
    remains the INTRINSIC barrier below. Writing the converse (passing this case
    off as the general theorem) would be exactly the degradation this file
    refuses.

    **INTRINSIC (MDP-gated, court-terme, #4039) — one `sorry` site remains, the
    proof.** It requires the Bellman operator / dynamic programming, index
    decomposability across arms, and induction on the planning horizon — that is,
    a complete MDP / optimal-stopping formalization. The statement itself is no
    longer circular: `discountedValue` gives it a meaning independent of what is
    being proved. -/
theorem gittins_optimality (inst : BanditInstance)
    (hγ_pos : 0 < inst.discount) (hγ_lt : inst.discount < 1)
    (hmean : ∀ arm ∈ inst.arms, 0 ≤ arm.trueMean) :
    ∀ π : Policy,
      discountedValue inst (fun _ => gittinsPolicy inst (Array.replicate inst.arms.size []))
        ≥ discountedValue inst π := by
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

/-- Greedy (myopic) policy: always play the arm with the highest true mean.
    This is the same argmax as `gittinsPolicy` but read directly off `arm.trueMean`
    rather than through the Gittins index. -/
noncomputable def greedyPolicy (inst : BanditInstance) : Nat :=
  ((Array.range inst.arms.size).foldl
    (fun (best : Nat × ℝ) i =>
      match inst.arms[i]? with
      | none => best
      | some arm =>
        let g := arm.trueMean
        if g > best.2 then (i, g) else best)
    (0, 0)).1

/-- In the known-mean model, the Gittins policy **coincides** with the greedy
    policy, regardless of the observed history: the Gittins index equals `trueMean`
    (`gittins_index_known_arm`), so both argmaxes range over the same quantity. The
    proof is definitional (reduction to the identity of the two folds after unfolding
    `gittinsIndex`).

    This is precisely why the former "Gittins beats greedy" statement was vacuous
    here: the dominance of the Gittins policy over the greedy approach only appears
    in the uncertain-belief regime (Beta–Bernoulli posterior, exploration), which
    requires the optimal-stopping / Bellman machinery absent from Mathlib (INTRINSIC,
    `gittins_optimality` above, #4039). In the known-arm model, Gittins = greedy,
    full stop. -/
theorem gittinsPolicy_eq_greedyPolicy (inst : BanditInstance)
    (histories : Array RewardHistory) :
    gittinsPolicy inst histories = greedyPolicy inst := by
  unfold gittinsPolicy greedyPolicy gittinsIndex
  rfl

end Gittins_en
