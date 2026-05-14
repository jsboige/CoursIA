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

/-- swapMatch preserves consistency when woman w prefers m over mOld.
    Pattern follows matchFree proof: split_ifs + have for consistency chains. -/
lemma swapMatch (h : GSConsistent σ.matching) (m mOld w : Fin n)
    (hm : σ.matching.menMatch m = none)
    (hw : σ.matching.womenMatch w = some mOld)
    (hmOld : σ.matching.menMatch mOld = some w) :
    GSConsistent (σ.matching.swapMatch m mOld w) := by
  have hne : m ≠ mOld := by intro heq; subst heq; simp_all
  intro m' w'
  simp only [GSMatching.swapMatch, Function.update_apply]
  -- outermost if: m' = mOld (from outer update)
  -- then inner if: m' = m (from inner update)
  -- RHS if: w' = w
  split_ifs with h_mOld h_ww h_m h_nw h_nm
  · -- m' = mOld, w' = w: both sides False by hne
    simp_all
  · -- m' = mOld, w' ≠ w: need μ.womenMatch w' ≠ some mOld
    have : σ.matching.womenMatch w' ≠ some mOld := by
      intro heq; have := (h mOld w').mpr heq; simp_all
    simp_all
  · -- m' ≠ mOld, m' = m, w' = w: both sides True
    simp_all
  · -- m' ≠ mOld, m' = m, w' ≠ w: need μ.womenMatch w' ≠ some m
    have hnw' : w ≠ w' := ne_comm.mp ‹¬w' = w›
    have : σ.matching.womenMatch w' ≠ some m := by
      intro heq; have := (h m w').mpr heq; simp_all
    simp_all
  · -- m' ≠ mOld, m' ≠ m, w' = w: need μ.menMatch m' ≠ some w
    have hnm' : m ≠ m' := ne_comm.mp ‹¬m' = m›
    have : σ.matching.menMatch m' ≠ some w := by
      intro heq; have := (h m' w).mp heq; simp_all
    simp_all
  · -- m' ≠ mOld, m' ≠ m, w' ≠ w: direct consistency
    exact h m' w'

/-- gsStepWith preserves matching consistency. -/
lemma stepWith (h : GSConsistent σ.matching) (m w : Fin n)
    (hm : σ.matching.menMatch m = none)
    (_hproposed : ¬ σ.proposed m w) :
    GSConsistent (gsStepWith prof σ m w).matching := by
  unfold gsStepWith
  split
  · -- womenMatch w = none: matchFree case
    exact matchFree h m w hm ‹_›
  · -- womenMatch w = some mOld
    split
    · -- woman prefers m over mOld: swapMatch case
      next mOld hwm hwlt =>
        have hmOld : σ.matching.menMatch mOld = some w := (h mOld w).mpr hwm
        exact swapMatch prof h m mOld w hm hwm hmOld
    · -- woman does NOT prefer m: matching unchanged
      exact h

/-- gsStep preserves matching consistency. -/
lemma step (h : GSConsistent σ.matching) (hfree : ∃ m, gsIsFree prof σ m) :
    GSConsistent (gsStep prof σ).matching := by
  unfold gsStep
  rw [dif_pos hfree]
  let m := Classical.choose hfree
  have hm : gsIsFree prof σ m := Classical.choose_spec hfree
  let w := gsChooseMax prof σ m hm.2
  have hw : ¬ σ.proposed m w := by
    have := gsChooseMax_mem prof σ m hm.2
    simp [gsCandidates] at this
    exact this
  exact stepWith prof h m w hm.1 hw

/-- gsRunSteps preserves matching consistency. -/
lemma runSteps (k : Nat) :
    GSConsistent (gsRunSteps prof k).matching := by
  induction k with
  | zero => exact initial
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end GSConsistent

/-! ## Termination: Proposal Count Bound -/

namespace proposedCount

variable (prof : PrefProfile n) {σ : GSState prof}

/-- A step for a free man increases the proposal count. -/
lemma step_of_free (σ : GSState prof) (m : Fin n)
    (hf : gsIsFree prof σ m) :
    proposedCount prof (gsStep prof σ) = proposedCount prof σ + 1 := by
  unfold gsStep
  rw [dif_pos ⟨m, hf⟩]
  let m' := Classical.choose ⟨m, hf⟩
  have hm' : gsIsFree prof σ m' := Classical.choose_spec ⟨m, hf⟩
  let w := gsChooseMax prof σ m' hm'.2
  have hw : ¬ σ.proposed m' w := by
    have := gsChooseMax_mem prof σ m' hm'.2
    simp [gsCandidates] at this
    exact this
  exact stepWith prof σ m' w hw

/-- Proposal count never exceeds n² for any state. -/
lemma le_bound (σ : GSState prof) :
    proposedCount prof σ ≤ gsProposalBound n := by
  classical
  unfold proposedCount proposedSet gsProposalBound
  calc (Finset.univ.filter fun mw => σ.proposed mw.1 mw.2).card
      ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = n * n := by
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- Proposal count at step k never exceeds the bound. -/
lemma runSteps_le_bound (k : Nat) :
    proposedCount prof (gsRunSteps prof k) ≤ gsProposalBound n :=
  le_bound prof _

/-- If a free man exists, one more step keeps count at or below bound. -/
lemma step_preserves_le_bound {_σ : GSState prof}
    (_h : proposedCount prof _σ ≤ gsProposalBound n) :
    proposedCount prof (gsStep prof _σ) ≤ gsProposalBound n :=
    le_bound prof _

/-- If the algorithm hasn't terminated after k steps, count equals k. -/
lemma runSteps_eq_of_not_terminated (k : Nat)
    (hterm : ¬ gsTerminated prof (gsRunSteps prof k)) :
    proposedCount prof (gsRunSteps prof k) = k := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    have hnk : ¬ gsTerminated prof (gsRunSteps prof k') := by
      intro hk_term
      unfold gsTerminated at hk_term hterm
      simp only [gsRunSteps] at hterm
      unfold gsStep at hterm
      rw [dif_neg hk_term] at hterm
      exact hterm hk_term
    have ihk := ih hnk
    have hf : ∃ m, gsIsFree prof (gsRunSteps prof k') m := not_not.mp hnk
    rw [step_of_free prof (gsRunSteps prof k') (Classical.choose hf)
        (Classical.choose_spec hf), ihk]

end proposedCount

/-! ## Step Identity When Terminated -/

/-- If the state is terminated, gsStep is identity. -/
lemma gsStep_eq_of_terminated (prof : PrefProfile n) (σ : GSState prof)
    (h : gsTerminated prof σ) :
    gsStep prof σ = σ := by
  unfold gsStep gsTerminated at *
  split
  · contradiction
  · rfl

/-- If the state is terminated at step k, all subsequent steps are identity. -/
lemma gsRunSteps_eq_of_terminated (prof : PrefProfile n) (k j : Nat) (hkj : k ≤ j)
    (h : gsTerminated prof (gsRunSteps prof k)) :
    gsRunSteps prof j = gsRunSteps prof k := by
  induction j generalizing k with
  | zero =>
    have : k = 0 := Nat.eq_zero_of_le_zero hkj
    subst this; rfl
  | succ j' ih =>
    simp only [gsRunSteps]
    cases eq_or_lt_of_le hkj with
    | inl heq => subst heq; rfl
    | inr hlt =>
      rw [ih k (Nat.le_of_lt_succ hlt) h]
      exact gsStep_eq_of_terminated prof _ h

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
  induction k with
  | zero =>
    simp only [gsRunSteps]
    intro m w w' hw hlt
    unfold gsInitial GSMatching.initial at hw
    simp at hw
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

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
  unfold gsStep
  rw [dif_pos hfree]
  let m := Classical.choose hfree
  have hm : gsIsFree prof σ m := Classical.choose_spec hfree
  let w := gsChooseMax prof σ m hm.2
  exact stepWith prof h m w

/-- gsRunSteps preserves menMatchedProposed. -/
lemma runSteps (k : Nat) :
    menMatchedProposed prof (gsRunSteps prof k) := by
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

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
  induction k with
  | zero =>
    simp only [gsRunSteps]
    exact initial prof
  | succ k' ih =>
    simp only [gsRunSteps]
    by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
    · exact step prof ih h
    · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
        unfold gsStep; simp [h]
      rw [hid]; exact ih

end womenBestState

end StableMarriage
