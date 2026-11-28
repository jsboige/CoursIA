/-
  Groves mechanisms and the Clarke pivot — Lean companion
  =======================================================

  Generalisation of the `SocialChoice.MechanismDesign` certificate: whereas the
  `VCGCombinatorial` block hand-computes the Clarke-pivot payments on TWO
  witnesses (2 and 3 bidders) and hands every value to `decide`, this module
  proves the theorem that generates them — the **Groves theorem** (Groves,
  1973) and the individual rationality of the **Clarke pivot** (Clarke,
  1971) — on an ABSTRACT domain: any number of agents, any finite type space,
  any finite set of outcomes.

  Setting (quasi-linear, dominant strategies):

  * `v i (θ i) a` : valuation of agent `i` of type `θ i` for outcome `a` ;
  * `aStar θ` : allocation rule, assumed to maximise the **reported** welfare ;
  * Groves transfers : `p i θ = Σ_{j≠i} v j (θ j) (aStar θ) + g i θ`, where
    the term `g i θ` does not depend on `i`'s own report.

  Results proved:

  1. `groves_DSIC` — every Groves mechanism is **DSIC**: truthful reporting is
     a dominant strategy for each agent ;
  2. `clarke_DSIC` — the Clarke pivot (`g i θ = − max_a Σ_{j≠i} v j (θ j) a`)
     is a Groves instance, hence DSIC as well ;
  3. `clarke_IR` — under nonnegative valuations, the Clarke pivot is
     **individually rational**: participating yields at least 0 ;
  4. `badAlloc_violates_DSIC` — **negative witness**: without welfare
     maximality, the same transfer scheme stops being DSIC (truthful utility
     0, deviation utility 2).

  What this module does NOT prove (honest scope): the Bayesian version (BIC),
  revenue optimality (Myerson-Satterthwaite / revenue equivalence), budget
  balance, nor equilibrium selection. `aStar` is a **hypothesis** of the
  theorem, not a computation: the synthesis engine stays outside Lean
  (#22381 milestone 1, `amd_synthesis.py`) ; this module certifies the
  incentive scheme, not the instances the solver enumerates.

  References: T. Groves, "Incentives in Teams" (Econometrica, 1973) ;
  E. H. Clarke, "Multipart Pricing of Public Goods" (1971) ;
  Maschler, Solan & Zamir, *Game Theory*, ch. 10 (Vickrey-Clarke-Groves).

  See #22381 (milestone 2, the formal extension named by criterion 6),
  #12205 (Law II chain), #4980 (FR/EN i18n convention).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace SocialChoice.Groves_en

open Finset

variable {N A T : Type*} [Fintype N] [DecidableEq N]

/-! ## Setting: valuations, welfare, reported profile

  A **reported profile** `θ : N → T` maps each agent to the type it announces.
  `N` = agents, `T` = type space (a single, symmetric one), `A` = set of
  outcomes (allocation, public project, etc.). -/

/-- Social welfare of the reported profile `θ` at outcome `a`. -/
def welfare (v : N → T → A → ℤ) (θ : N → T) (a : A) : ℤ := ∑ j, v j (θ j) a

/-- Welfare of the agents **other than `i`** at the reported profile `θ`, outcome `a`. -/
def othersWelfare (v : N → T → A → ℤ) (θ : N → T) (a : A) (i : N) : ℤ :=
  ∑ j ∈ univ.erase i, v j (θ j) a

/-- **Groves** transfer: agent `i`'s share of the others' welfare at the chosen
    outcome, plus an additive term `g i θ` that must depend only on the
    **other** agents' reports (hypothesis `hg` of the theorem). -/
def grovesPayment (v : N → T → A → ℤ) (aStar : (N → T) → A) (g : N → (N → T) → ℤ)
    (θ : N → T) (i : N) : ℤ :=
  othersWelfare v θ (aStar θ) i + g i θ

/-- Payoff of agent `i`, of **true type** `t`, when the reported profile is
    `rep`. This is the quasi-linear utility: valuation of the outcome minus
    what the agent pays, i.e. here valuation plus the transfer received. -/
def payoff (v : N → T → A → ℤ) (aStar : (N → T) → A) (g : N → (N → T) → ℤ)
    (i : N) (t : T) (rep : N → T) : ℤ :=
  v i t (aStar rep) + grovesPayment v aStar g rep i

/-! ## Two structural lemmas

  The first is the only place where total welfare is split into "the others"
  plus "oneself" ; the second says the others' share is insensitive to one's
  own report. -/

/-- Total welfare splits into the others' share and one's own share. -/
lemma othersWelfare_add_own (v : N → T → A → ℤ) (θ : N → T) (a : A) (i : N) :
    othersWelfare v θ a i + v i (θ i) a = welfare v θ a := by
  unfold othersWelfare welfare
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The other agents' share does not depend on `i`'s report. -/
lemma othersWelfare_update (v : N → T → A → ℤ) (θ : N → T) (i : N) (t' : T) (a : A) :
    othersWelfare v (Function.update θ i t') a i = othersWelfare v θ a i := by
  unfold othersWelfare
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_erase] at hj
  rw [Function.update_apply, if_neg hj.1]

/-! ## The Groves theorem — every Groves mechanism is DSIC

  The argument fits in one line: agent `i`'s utility equals the total welfare
  of the true profile **plus** a constant independent of his report ; since
  `aStar` maximises welfare, deviating can only lower it. The computation
  below reproduces exactly that. -/

/-- **Groves theorem.** If `aStar` maximises reported welfare and the term
    `g i ·` does not depend on `i`'s report, then no agent gains by deviating
    unilaterally from truthful reporting. -/
theorem groves_DSIC
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (g : N → (N → T) → ℤ)
    (hg : ∀ (i : N) (θ θ' : N → T), (∀ j, j ≠ i → θ j = θ' j) → g i θ = g i θ')
    (i : N) (θ : N → T) (t' : T) :
    payoff v aStar g i (θ i) θ ≥ payoff v aStar g i (θ i) (Function.update θ i t') := by
  have hg' : g i (Function.update θ i t') = g i θ :=
    hg i _ θ (fun j hj => by rw [Function.update_apply, if_neg hj])
  have hothers := othersWelfare_update v θ i t' (aStar (Function.update θ i t'))
  have hstar := hStar θ (aStar (Function.update θ i t'))
  have e1 := othersWelfare_add_own v θ (aStar (Function.update θ i t')) i
  have e2 := othersWelfare_add_own v θ (aStar θ) i
  rw [← e1, ← e2] at hstar
  unfold payoff grovesPayment
  rw [hothers, hg']
  linarith

/-! ## The Clarke pivot — the others' share at its maximum

  The canonical choice of `g` is minus the others' maximal welfare: the agent
  pays exactly the externality he imposes. `A` must be nonempty (otherwise the
  maximum is meaningless) and finite (otherwise it is not attained). -/

variable [Fintype A] [Nonempty A]

/-- Maximal welfare of the agents other than `i`, at the reported profile `θ`.
    Attained: `A` is finite and nonempty. -/
noncomputable def othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) : ℤ :=
  (univ : Finset A).sup' Finset.univ_nonempty (fun a => othersWelfare v θ a i)

/-- **Clarke pivot** transfers: agent `i` receives minus the externality he
    imposes on the other agents. -/
noncomputable def clarkeTransfer (v : N → T → A → ℤ) : N → (N → T) → ℤ :=
  fun i θ => - othersMax v θ i

/-- The others' maximum does not depend on `i`'s report. -/
lemma othersMax_congr (v : N → T → A → ℤ) (i : N) {θ θ' : N → T}
    (h : ∀ j, j ≠ i → θ j = θ' j) : othersMax v θ i = othersMax v θ' i := by
  unfold othersMax
  have hfun : (fun a => othersWelfare v θ a i) = (fun a => othersWelfare v θ' a i) := by
    funext a
    unfold othersWelfare
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_erase] at hj
    rw [h j hj.1]
  rw [hfun]

/-- The others' maximum **dominates** any agent's share. -/
lemma othersWelfare_le_othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) (a : A) :
    othersWelfare v θ a i ≤ othersMax v θ i := by
  unfold othersMax
  exact Finset.le_sup' (fun a => othersWelfare v θ a i) (Finset.mem_univ a)

/-- The others' maximum is **attained** by some outcome. -/
lemma exists_othersMax (v : N → T → A → ℤ) (θ : N → T) (i : N) :
    ∃ a : A, othersMax v θ i = othersWelfare v θ a i := by
  unfold othersMax
  obtain ⟨a, -, ha⟩ :=
    Finset.exists_mem_eq_sup' (s := (univ : Finset A)) (H := Finset.univ_nonempty)
      (f := fun a => othersWelfare v θ a i)
  exact ⟨a, ha⟩

/-- **Clarke pivot: DSIC.** Direct instance of the Groves theorem. -/
theorem clarke_DSIC
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (i : N) (θ : N → T) (t' : T) :
    payoff v aStar (clarkeTransfer v) i (θ i) θ
      ≥ payoff v aStar (clarkeTransfer v) i (θ i) (Function.update θ i t') := by
  refine groves_DSIC v aStar hStar (clarkeTransfer v) ?_ i θ t'
  intro i θ θ' h
  unfold clarkeTransfer
  rw [othersMax_congr v i h]

/-- **Clarke pivot: individual rationality.** Under nonnegative valuations,
    participating yields at least 0: the agent never pays more than the chosen
    outcome brings him, since the others' maximum is bounded by the total
    welfare he himself attains. -/
theorem clarke_IR
    (v : N → T → A → ℤ) (aStar : (N → T) → A)
    (hStar : ∀ θ a, welfare v θ a ≤ welfare v θ (aStar θ))
    (hv : ∀ (i : N) (t : T) (a : A), 0 ≤ v i t a)
    (i : N) (θ : N → T) :
    0 ≤ payoff v aStar (clarkeTransfer v) i (θ i) θ := by
  obtain ⟨a0, ha0⟩ := exists_othersMax v θ i
  have hstar := hStar θ a0
  have e1 := othersWelfare_add_own v θ a0 i
  have e2 := othersWelfare_add_own v θ (aStar θ) i
  rw [← e1, ← e2] at hstar
  have hnonneg := hv i (θ i) a0
  unfold payoff grovesPayment clarkeTransfer
  rw [ha0]
  linarith

/-! ## Negative witness — welfare maximality is indispensable

  Two agents, Boolean types, Boolean outcome, valuation 1 when the type is
  `true` AND the outcome is `true`. The `badAlloc` rule ignores the second
  agent: it returns the outcome = `¬ (first agent's report)`. Transfers keep
  the Groves shape, but since `badAlloc` no longer maximises welfare, agent 0
  prefers to lie: truthful he gets 0, deviating he gets 2. -/

namespace Counterexample

/-- Valuation: 1 when both the type and the outcome are `true`, 0 otherwise. -/
def val (_i : Bool) (t : Bool) (a : Bool) : ℤ := if t && a then 1 else 0

/-- **Inefficient** allocation: the outcome is the negation of agent 0's report. -/
def badAlloc (θ : Bool → Bool) : Bool := !(θ false)

/-- Null additive transfer (isolating the allocation's effect). -/
def zeroTransfer (_ : Bool) (_ : Bool → Bool) : ℤ := 0

/-- On two agents, the others' share for agent `false` is the `true` term. -/
lemma othersWelfare_false (v : Bool → Bool → Bool → ℤ) (θ : Bool → Bool) (a : Bool) :
    othersWelfare v θ a false = v true (θ true) a := by
  unfold othersWelfare
  have h : (univ : Finset Bool).erase false = {true} := by decide
  rw [h, Finset.sum_singleton]

/-- On two agents, the others' share for agent `true` is the `false` term. -/
lemma othersWelfare_true (v : Bool → Bool → Bool → ℤ) (θ : Bool → Bool) (a : Bool) :
    othersWelfare v θ a true = v false (θ false) a := by
  unfold othersWelfare
  have h : (univ : Finset Bool).erase true = {false} := by decide
  rw [h, Finset.sum_singleton]

/-- `badAlloc` does not maximise welfare: at the profile where both agents have
    type `true`, it returns `false` whereas `true` would do strictly better.
    This is precisely the premise of the Groves theorem that fails. -/
theorem badAlloc_not_efficient :
    ¬ ∀ θ a, welfare val θ a ≤ welfare val θ (badAlloc θ) := by
  intro h
  have hbad : badAlloc (fun _ : Bool => true) = false := by simp [badAlloc]
  have hw1 : welfare val (fun _ : Bool => true) true = 2 := by
    unfold welfare
    have hsplit : (univ : Finset Bool) = insert true ({false} : Finset Bool) := by decide
    rw [hsplit, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [val]
  have hw0 : welfare val (fun _ : Bool => true) false = 0 := by
    unfold welfare
    have hsplit : (univ : Finset Bool) = insert true ({false} : Finset Bool) := by decide
    rw [hsplit, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [val]
  have h0 := h (fun _ => true) true
  rw [hbad, hw1, hw0] at h0
  omega

/-- **Negative witness**: without welfare maximality, Groves transfers are no
    longer DSIC. Agent 0, of true type `true`, gets 0 by reporting truthfully
    and 2 by deviating to `false`. -/
theorem badAlloc_violates_DSIC :
    ∃ (i : Bool) (θ : Bool → Bool) (t' : Bool),
      payoff val badAlloc zeroTransfer i (θ i) θ
        < payoff val badAlloc zeroTransfer i (θ i) (Function.update θ i t') := by
  refine ⟨false, fun _ => true, false, ?_⟩
  have htruth : payoff val badAlloc zeroTransfer false true (fun _ => true) = 0 := by
    rw [payoff, grovesPayment, othersWelfare_false]
    simp [val, badAlloc, zeroTransfer]
  have hdev :
      payoff val badAlloc zeroTransfer false true (Function.update (fun _ => true) false false) = 2 := by
    rw [payoff, grovesPayment, othersWelfare_false]
    simp [val, badAlloc, zeroTransfer, Function.update]
  rw [htruth, hdev]
  norm_num

end Counterexample

end SocialChoice.Groves_en
