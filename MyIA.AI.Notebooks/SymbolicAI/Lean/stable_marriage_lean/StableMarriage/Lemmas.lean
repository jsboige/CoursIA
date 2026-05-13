/-
  Stable Marriage - Key Lemmas for GS Algorithm Correctness
  ==========================================================

  Invariants preserved by each GS step:
  - Matching consistency (each matched pair is mutual)
  - Proposal monotonicity (proposed set only grows)
  - Men always proposed downward (to less-preferred women)
  - Terminating invariants (proposal count bound)

  Adapted from: https://github.com/mmaaz-git/stable-marriage-lean (v4.25.0)
  Simplified for total bijective preferences (no `acceptable` filter needed).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Common
import StableMarriage.Definitions
import StableMarriage.GSState

namespace StableMarriage

open Function Finset Classical

variable {n : Nat} [NeZero n]

/-! ## Consistent Partial Matching -/

/-- A partial matching is consistent: each match is mutual.
    If man m is matched to woman w, then woman w is matched to man m,
    and vice versa. -/
def GSConsistent (μ : GSMatching n) : Prop :=
  ∀ m w, μ.menMatch m = some w ↔ μ.womenMatch w = some m

namespace GSConsistent

variable {μ : GSMatching n}

lemma men_iff_women (h : GSConsistent μ) (m : Fin n) (w : Fin n) :
    μ.menMatch m = some w ↔ μ.womenMatch w = some m := h m w

lemma women_iff_men (h : GSConsistent μ) (w : Fin n) (m : Fin n) :
    μ.womenMatch w = some m ↔ μ.menMatch m = some w := (h m w).symm

/-- Initial matching is consistent (all none). -/
lemma initial : GSConsistent (GSMatching.initial (n := n)) := by
  intro m w
  simp [GSMatching.initial]

/-- Matching a free man and free woman preserves consistency. -/
lemma matchFree (h : GSConsistent μ) (m : Fin n) (w : Fin n)
    (hm : μ.menMatch m = none) (hw : μ.womenMatch w = none) :
    GSConsistent (μ.matchFree m w) := by
  intro m' w'
  simp only [GSMatching.matchFree, Function.update_apply]
  split_ifs
  · simp_all
  · have : μ.womenMatch w' ≠ some m := by
      intro heq; have := (h m w').mpr heq; simp_all
    simp_all [ne_comm]
  · have : μ.menMatch m' ≠ some w := by
      intro heq; have := (h m' w).mp heq; simp_all
    simp_all [ne_comm]
  · exact h m' w'

end GSConsistent

/-! ## Proposed Set Tracking -/

/-- The set of proposed pairs as a Finset. -/
noncomputable def proposedSet (prof : PrefProfile n) (σ : GSState prof) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun mw => σ.proposed mw.1 mw.2)

/-- Number of proposed pairs. -/
noncomputable def proposedCount (prof : PrefProfile n) (σ : GSState prof) : Nat :=
  (proposedSet prof σ).card

namespace proposedSet

variable (prof : PrefProfile n) {σ : GSState prof}

lemma mem_iff (mw : Fin n × Fin n) :
    mw ∈ proposedSet prof σ ↔ σ.proposed mw.1 mw.2 := by
  simp [proposedSet]

/-- gsStepWith inserts exactly one new pair into the proposed set. -/
lemma stepWith_insert (σ : GSState prof) (m w : Fin n) :
    proposedSet prof (gsStepWith prof σ m w) =
      insert (m, w) (proposedSet prof σ) := by
  classical
  ext ⟨m', w'⟩
  simp only [mem_iff, mem_insert, Prod.mk.injEq]
  unfold gsStepWith
  split
  · simp; tauto
  · split <;> simp <;> tauto

end proposedSet

namespace proposedCount

variable (prof : PrefProfile n) {σ : GSState prof}

/-- Initial state has zero proposals. -/
lemma initial : proposedCount prof (gsInitial prof) = 0 := by
  classical
  simp [proposedCount, proposedSet, gsInitial]

/-- StepWith increases count by one for a new proposal. -/
lemma stepWith (σ : GSState prof) (m w : Fin n) (hnew : ¬ σ.proposed m w) :
    proposedCount prof (gsStepWith prof σ m w) = proposedCount prof σ + 1 := by
  classical
  have hmem : (m, w) ∉ proposedSet prof σ := by
    simp [proposedSet]
    exact hnew
  simp only [proposedCount, proposedSet.stepWith_insert]
  exact card_insert_of_notMem hmem

end proposedCount

/-! ## Men Proposed Downward Invariant -/

/-- In the GS algorithm, men propose in order of decreasing preference.
    After k steps, all proposals by man m were to his top-k candidates.
    Since preferences are total bijections, every woman is a valid candidate. -/
def menProposedDownward (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ m w w', σ.proposed m w → prof.menPref m w' < prof.menPref m w →
    σ.proposed m w'

/-! ## Women Best Match Invariant -/

/-- Each woman's current match is her best proposal so far. -/
def womenBestState (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ w m m', σ.matching.womenMatch w = some m → σ.proposed m' w →
    prof.womenPref w m ≤ prof.womenPref w m'

namespace womenBestState

variable (prof : PrefProfile n) {σ : GSState prof}

/-- Initial state trivially satisfies womenBest (no matches). -/
lemma initial : womenBestState prof (gsInitial prof) := by
  unfold womenBestState
  intro w m m' hmatch _
  unfold gsInitial GSMatching.initial at hmatch
  simp at hmatch

end womenBestState

/-! ## Men Matched Implies Proposed -/

/-- Every matched man has proposed to his current partner. -/
def menMatchedProposed (prof : PrefProfile n) (σ : GSState prof) : Prop :=
  ∀ m w, σ.matching.menMatch m = some w → σ.proposed m w

namespace menMatchedProposed

variable (prof : PrefProfile n) {σ : GSState prof}

/-- Initial state trivially satisfies (no matches). -/
lemma initial : menMatchedProposed prof (gsInitial prof) := by
  unfold menMatchedProposed
  intro m w hmatch
  unfold gsInitial at hmatch
  unfold GSMatching.initial at hmatch
  simp at hmatch

end menMatchedProposed

/-! ## Consistency Preservation by GS Steps -/

namespace GSConsistent

variable (prof : PrefProfile n) {σ : GSState prof}

/-- swapMatch preserves consistency when woman w prefers m over mOld. -/
lemma swapMatch (h : GSConsistent σ.matching) (m mOld w : Fin n)
    (hm : σ.matching.menMatch m = none)
    (hw : σ.matching.womenMatch w = some mOld)
    (hmOld : σ.matching.menMatch mOld = some w) :
    GSConsistent (σ.matching.swapMatch m mOld w) := by
  sorry

/-- gsStepWith preserves matching consistency. -/
lemma stepWith (h : GSConsistent σ.matching) (m w : Fin n)
    (hproposed : ¬ σ.proposed m w) :
    GSConsistent (gsStepWith prof σ m w).matching := by
  sorry

/-- gsStep preserves matching consistency. -/
lemma step (h : GSConsistent σ.matching) (hfree : ∃ m, gsIsFree prof σ m) :
    GSConsistent (gsStep prof σ).matching := by
  sorry

/-- gsRunSteps preserves matching consistency. -/
lemma runSteps (k : Nat) :
    GSConsistent (gsRunSteps prof k).matching := by
  sorry

end GSConsistent

/-! ## Termination: Proposal Count Bound -/

namespace proposedCount

variable (prof : PrefProfile n) {σ : GSState prof}

/-- A step for a free man increases the proposal count. -/
lemma step_of_free (σ : GSState prof) (m : Fin n)
    (hf : gsIsFree prof σ m) :
    proposedCount prof (gsStep prof σ) = proposedCount prof σ + 1 := by
  sorry

/-- If a free man exists, proposal count is below the bound. -/
lemma lt_bound_of_free (σ : GSState prof) (k : Nat)
    (hk : proposedCount prof σ < gsProposalBound n)
    (hf : ∃ m, gsIsFree prof σ m) :
    proposedCount prof (gsRunSteps prof k) <
      gsProposalBound n := by
  sorry

/-- If the algorithm hasn't terminated after k steps, count equals k. -/
lemma runSteps_eq_of_not_terminated (k : Nat)
    (hterm : ¬ gsTerminated prof (gsRunSteps prof k)) :
    proposedCount prof (gsRunSteps prof k) = k := by
  sorry

end proposedCount

/-! ## Step Identity When Terminated -/

/-- If the state is terminated, gsStep is identity. -/
lemma gsStep_eq_of_terminated (prof : PrefProfile n) (σ : GSState prof)
    (h : gsTerminated prof σ) :
    gsStep prof σ = σ := by
  sorry

/-- If the state is terminated at step k, all subsequent steps are identity. -/
lemma gsRunSteps_eq_of_terminated (prof : PrefProfile n) (k j : Nat) (hkj : k ≤ j)
    (h : gsTerminated prof (gsRunSteps prof k)) :
    gsRunSteps prof j = gsRunSteps prof k := by
  sorry

/-! ## Invariant: Men Proposed Downward (step preservation) -/

namespace menProposedDownward

variable (prof : PrefProfile n) {σ : GSState prof}

/-- gsStep preserves the menProposedDownward invariant. -/
lemma step (h : menProposedDownward prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    menProposedDownward prof (gsStep prof σ) := by
  sorry

/-- gsRunSteps preserves the menProposedDownward invariant. -/
lemma runSteps (k : Nat) :
    menProposedDownward prof (gsRunSteps prof k) := by
  sorry

end menProposedDownward

/-! ## Invariant: Men Matched Implies Proposed (step preservation) -/

namespace menMatchedProposed

variable (prof : PrefProfile n) {σ : GSState prof}

/-- gsStepWith preserves menMatchedProposed. -/
lemma stepWith (h : menMatchedProposed prof σ) (m w : Fin n) :
    menMatchedProposed prof (gsStepWith prof σ m w) := by
  sorry

/-- gsStep preserves menMatchedProposed. -/
lemma step (h : menMatchedProposed prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    menMatchedProposed prof (gsStep prof σ) := by
  sorry

/-- gsRunSteps preserves menMatchedProposed. -/
lemma runSteps (k : Nat) :
    menMatchedProposed prof (gsRunSteps prof k) := by
  sorry

end menMatchedProposed

/-! ## Invariant: Women Best State (step preservation) -/

namespace womenBestState

variable (prof : PrefProfile n) {σ : GSState prof}

/-- gsStep preserves womenBestState. -/
lemma step (h : womenBestState prof σ)
    (hfree : ∃ m, gsIsFree prof σ m) :
    womenBestState prof (gsStep prof σ) := by
  sorry

/-- gsRunSteps preserves womenBestState. -/
lemma runSteps (k : Nat) :
    womenBestState prof (gsRunSteps prof k) := by
  sorry

end womenBestState

end StableMarriage
