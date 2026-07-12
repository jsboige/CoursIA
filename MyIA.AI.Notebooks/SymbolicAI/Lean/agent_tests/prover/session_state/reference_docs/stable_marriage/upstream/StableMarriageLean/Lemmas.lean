import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import StableMarriageLean.GaleShapley

namespace StableMarriageLean

noncomputable section
open Classical

-- If an agent prefers a match, that match is acceptable.
lemma prefersOpt_left_acceptable {Agent Partner : Type*}
    (p : Preferences Agent Partner) (a : Agent) (o1 : Partner) (o2 : Option Partner) :
    prefersOpt p a (some o1) o2 → p.acceptable a o1 := by
  cases o2 with
  | none =>
      intro h
      simpa [prefersOpt] using h
  | some o2 =>
      intro h
      by_cases hacc : p.acceptable a o1
      · exact hacc
      · simp [prefersOpt, hacc] at h

-- Strict preferences are asymmetric.
lemma prefers_asymm {Agent Partner : Type*} (p : Preferences Agent Partner)
    (a : Agent) (o1 o2 : Partner) :
    p.prefers a o1 o2 → ¬ p.prefers a o2 o1 := by
  intro h12 h21
  have h := p.prefers_trans a o1 o2 o1 h12 h21
  exact (p.prefers_irrefl a o1) h

-- PrefersOpt is asymmetric on explicit options.
lemma prefersOpt_asymm {Agent Partner : Type*} (p : Preferences Agent Partner)
    (a : Agent) (o1 o2 : Partner) :
    prefersOpt p a (some o1) (some o2) → ¬ prefersOpt p a (some o2) (some o1) := by
  intro h12 h21
  by_cases hacc1 : p.acceptable a o1
  · by_cases hacc2 : p.acceptable a o2
    · have h12' : p.prefers a o1 o2 := by
        simpa [prefersOpt, hacc1, hacc2] using h12
      have h21' : p.prefers a o2 o1 := by
        simpa [prefersOpt, hacc2, hacc1] using h21
      exact (prefers_asymm p a o1 o2 h12') h21'
    ·
      simp [prefersOpt, hacc2] at h21
  ·
    simp [prefersOpt, hacc1] at h12

-- With acceptable partners, prefersOpt matches the base preference relation.
lemma prefersOpt_some_some_iff {Agent Partner : Type*} (p : Preferences Agent Partner)
    (a : Agent) (o1 o2 : Partner) (h1 : p.acceptable a o1) (h2 : p.acceptable a o2) :
    prefersOpt p a (some o1) (some o2) ↔ p.prefers a o1 o2 := by
  simp [prefersOpt, h1, h2]

-- Two matchings are equal when both match maps agree.
lemma Matching.ext {P : Problem} {μ ν : Matching P}
    (hmen : μ.menMatches = ν.menMatches) (hwomen : μ.womenMatches = ν.womenMatches) :
    μ = ν := by
  cases μ
  cases ν
  cases hmen
  cases hwomen
  rfl

-- The set of proposed pairs in a state.
def proposedSet (P : Problem) (σ : GSState P) : Finset (P.Men × P.Women) := by
  classical
  letI := P.menFintype
  letI := P.womenFintype
  letI : Fintype (P.Men × P.Women) := inferInstance
  exact Finset.univ.filter (fun mw => σ.proposed mw.1 mw.2)

-- The number of proposed pairs in a state.
def proposedCount (P : Problem) (σ : GSState P) : Nat :=
  (proposedSet P σ).card

-- Membership in the proposed set is just the proposal predicate.
lemma mem_proposedSet
    (P : Problem) (σ : GSState P) (mw : P.Men × P.Women) :
    mw ∈ proposedSet P σ ↔ σ.proposed mw.1 mw.2 := by
  classical
  simp [proposedSet]

-- The proposed predicate after a stepWith update.
lemma stepWith_proposed
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women) :
    (GSState.stepWith P σ m w).proposed =
      fun m' w' => σ.proposed m' w' ∨ (m' = m ∧ w' = w) := by
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · simp [GSState.stepWith, hw, hpref]
      · simp [GSState.stepWith, hw, hpref]
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · simp [GSState.stepWith, hw, hpref]
      · simp [GSState.stepWith, hw, hpref]

-- A stepWith proposal inserts exactly one new pair into the proposed set.
lemma proposedSet_stepWith
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women) :
    proposedSet P (GSState.stepWith P σ m w) =
      insert (m, w) (proposedSet P σ) := by
  classical
  ext mw
  cases mw with
  | mk m' w' =>
      simp [proposedSet, stepWith_proposed, or_comm]

-- If (m, w) was not proposed, stepWith increases the count by one.
lemma proposedCount_stepWith
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hnew : ¬ σ.proposed m w) :
    proposedCount P (GSState.stepWith P σ m w) = proposedCount P σ + 1 := by
  classical
  have hmem : (m, w) ∉ proposedSet P σ := by
    simp [proposedSet, hnew]
  simpa [proposedCount, proposedSet_stepWith] using
    (Finset.card_insert_of_notMem (a := (m, w)) (s := proposedSet P σ) hmem)

-- The initial state has zero proposals.
lemma proposedCount_initial (P : Problem) :
    proposedCount P (GSState.initial P) = 0 := by
  classical
  simp [proposedCount, proposedSet, GSState.initial]

-- All men matched in a state are acceptable to those men.
def menAcceptableState (P : Problem) (σ : GSState P) : Prop :=
  ∀ m w, σ.matching.menMatches m = some w → P.menPrefs.acceptable m w

-- All women matched in a state are acceptable to those women.
def womenAcceptableState (P : Problem) (σ : GSState P) : Prop :=
  ∀ w m, σ.matching.womenMatches w = some m → P.womenPrefs.acceptable w m

-- The initial state is acceptable for men.
lemma initial_menAcceptable (P : Problem) : menAcceptableState P (GSState.initial P) := by
  intro m w hmatch
  simp [GSState.initial] at hmatch

-- The initial state is acceptable for women.
lemma initial_womenAcceptable (P : Problem) : womenAcceptableState P (GSState.initial P) := by
  intro w m hmatch
  simp [GSState.initial] at hmatch

-- Rejecting a proposal to a free woman leaves the matching unchanged.
lemma stepWith_matching_eq_of_reject_none
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hw : σ.matching.womenMatches w = none)
    (hpref : ¬ prefersOpt P.womenPrefs w (some m) none) :
    (GSState.stepWith P σ m w).matching = σ.matching := by
  unfold GSState.stepWith
  have hacc : ¬ P.womenPrefs.acceptable w m := by
    simpa [prefersOpt] using hpref
  rw [hw]
  simp [prefersOpt, hacc]

-- Rejecting a proposal to a matched woman leaves the matching unchanged.
lemma stepWith_matching_eq_of_reject_some
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women) (mOld : P.Men)
    (hw : σ.matching.womenMatches w = some mOld)
    (hpref : ¬ prefersOpt P.womenPrefs w (some m) (some mOld)) :
    (GSState.stepWith P σ m w).matching = σ.matching := by
  unfold GSState.stepWith
  rw [hw]
  simp [if_neg hpref]

-- StepWith preserves men's acceptability when the proposer finds the woman acceptable.
lemma menAcceptable_stepWith
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hacc : P.menPrefs.acceptable m w) (hmen : menAcceptableState P σ) :
    menAcceptableState P (GSState.stepWith P σ m w) := by
  classical
  intro m' w' hmatch
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · by_cases hm : m' = m
        · subst hm
          have hmatch' :
              (Matching.matchUnmatched P σ.matching m' w).menMatches m' = some w' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have : w' = w := by
            simpa [Matching.matchUnmatched, eq_comm] using hmatch'
          subst this
          exact hacc
        · have hmatch' : σ.matching.menMatches m' = some w' := by
            have hmatch' :
                (Matching.matchUnmatched P σ.matching m w).menMatches m' = some w' := by
              simpa [GSState.stepWith, hw, hpref] using hmatch
            simpa [Matching.matchUnmatched, hm] using hmatch'
          exact hmen _ _ hmatch'
      ·
        have hmatch' : σ.matching.menMatches m' = some w' := by
          simpa [stepWith_matching_eq_of_reject_none P σ m w hw hpref] using hmatch
        exact hmen _ _ hmatch'
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · by_cases hm : m' = m
        · subst hm
          have hmatch' :
              (Matching.swapMatch P σ.matching m' mOld w).menMatches m' = some w' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          by_cases hmOld : mOld = m'
          ·
            have hmatch'' := hmatch'
            simp [Matching.swapMatch, hmOld] at hmatch''
          · have : w' = w := by
              have hmOld' : m' ≠ mOld := by
                simpa [eq_comm] using hmOld
              simpa [Matching.swapMatch, hmOld', eq_comm] using hmatch'
            subst this
            exact hacc
        · by_cases hmOld : m' = mOld
          · subst hmOld
            have hmatch' :
                (Matching.swapMatch P σ.matching m m' w).menMatches m' = some w' := by
              simpa [GSState.stepWith, hw, hpref] using hmatch
            have hmatch'' := hmatch'
            simp [Matching.swapMatch] at hmatch''
          · have hmatch' : σ.matching.menMatches m' = some w' := by
              have hmatch' :
                  (Matching.swapMatch P σ.matching m mOld w).menMatches m' = some w' := by
                simpa [GSState.stepWith, hw, hpref] using hmatch
              simpa [Matching.swapMatch, hm, hmOld] using hmatch'
            exact hmen _ _ hmatch'
      ·
        have hmatch' : σ.matching.menMatches m' = some w' := by
          simpa [stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref] using hmatch
        exact hmen _ _ hmatch'

-- StepWith preserves women's acceptability.
lemma womenAcceptable_stepWith
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hwomen : womenAcceptableState P σ) :
    womenAcceptableState P (GSState.stepWith P σ m w) := by
  classical
  intro w' m' hmatch
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · by_cases hw' : w' = w
        · subst hw'
          have hmatch' :
              (Matching.matchUnmatched P σ.matching m w').womenMatches w' = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have : m' = m := by
            simpa [Matching.matchUnmatched, eq_comm] using hmatch'
          subst this
          exact prefersOpt_left_acceptable (p := P.womenPrefs) (a := w') (o1 := m')
            (o2 := none) hpref
        ·
          have hmatch' :
              (Matching.matchUnmatched P σ.matching m w).womenMatches w' = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have hmatch'' : σ.matching.womenMatches w' = some m' := by
            simpa [Matching.matchUnmatched, hw'] using hmatch'
          exact hwomen _ _ hmatch''
      ·
        have hmatch' : σ.matching.womenMatches w' = some m' := by
          simpa [stepWith_matching_eq_of_reject_none P σ m w hw hpref] using hmatch
        exact hwomen _ _ hmatch'
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · by_cases hw' : w' = w
        · subst hw'
          have hmatch' :
              (Matching.swapMatch P σ.matching m mOld w').womenMatches w' = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have : m' = m := by
            simpa [Matching.swapMatch, eq_comm] using hmatch'
          subst this
          exact prefersOpt_left_acceptable (p := P.womenPrefs) (a := w') (o1 := m')
            (o2 := some mOld) hpref
        ·
          have hmatch' :
              (Matching.swapMatch P σ.matching m mOld w).womenMatches w' = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have hmatch'' : σ.matching.womenMatches w' = some m' := by
            simpa [Matching.swapMatch, hw'] using hmatch'
          exact hwomen _ _ hmatch''
      ·
        have hmatch' : σ.matching.womenMatches w' = some m' := by
          simpa [stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref] using hmatch
        exact hwomen _ _ hmatch'

-- Updating a free pair to match preserves consistency.
lemma consistent_matchUnmatched
    (P : Problem) (μ : Matching P) (m : P.Men) (w : P.Women)
    (hcons : consistent P μ) (hm : μ.menMatches m = none) (hw : μ.womenMatches w = none) :
    consistent P (Matching.matchUnmatched P μ m w) := by
  intro m' w'
  by_cases hm' : m' = m
  · by_cases hw' : w' = w
    · simp [Matching.matchUnmatched, hm', hw']
    · have hw'' : w ≠ w' := by simpa [eq_comm] using hw'
      have hno : μ.womenMatches w' ≠ some m := by
        intro hmw
        have h := (hcons m w').2 hmw
        simp [hm] at h
      simp [Matching.matchUnmatched, hm', hw', hw'', hno]
  · by_cases hw' : w' = w
    · have hm'' : m ≠ m' := by simpa [eq_comm] using hm'
      have hno : μ.menMatches m' ≠ some w := by
        intro hmw
        have h := (hcons m' w).1 hmw
        simp [hw] at h
      simp [Matching.matchUnmatched, hm', hw', hm'', hno]
    · simpa [Matching.matchUnmatched, hm', hw'] using (hcons m' w')

-- Swapping a woman's partner preserves consistency.
lemma consistent_swapMatch
    (P : Problem) (μ : Matching P) (m mOld : P.Men) (w : P.Women)
    (hcons : consistent P μ) (hm : μ.menMatches m = none)
    (hw : μ.womenMatches w = some mOld) :
    consistent P (Matching.swapMatch P μ m mOld w) := by
  have hmne : m ≠ mOld := by
    intro hmeq
    subst hmeq
    have h := (hcons m w).2 hw
    simp [hm] at h
  have hOld : μ.menMatches mOld = some w := (hcons mOld w).2 hw
  intro m' w'
  by_cases hm' : m' = m
  · by_cases hw' : w' = w
    · simp [Matching.swapMatch, hm', hw', hmne]
    · have hw'' : w ≠ w' := by simpa [eq_comm] using hw'
      have hno : μ.womenMatches w' ≠ some m := by
        intro hmw
        have h := (hcons m w').2 hmw
        simp [hm] at h
      simp [Matching.swapMatch, hm', hw', hw'', hno, hmne]
  · by_cases hOldm : m' = mOld
    · by_cases hw' : w' = w
      · simp [Matching.swapMatch, hOldm, hw', hmne]
      · have hw'' : w ≠ w' := by simpa [eq_comm] using hw'
        have hno : μ.womenMatches w' ≠ some mOld := by
          intro hmw
          have h1 : μ.menMatches mOld = some w' := (hcons mOld w').2 hmw
          have h2 : μ.menMatches mOld = some w := hOld
          have hEq : some w' = some w := by simpa [h1] using h2
          cases hEq
          exact hw'' rfl
        simp [Matching.swapMatch, hOldm, hw', hno]
    · by_cases hw' : w' = w
      · have hm'' : m ≠ m' := by simpa [eq_comm] using hm'
        have hno : μ.menMatches m' ≠ some w := by
          intro hmw
          have := (hcons m' w).1 hmw
          have : mOld = m' := by simpa [hw] using this
          exact hOldm this.symm
        simp [Matching.swapMatch, hm', hOldm, hw', hm'', hno]
      · simpa [Matching.swapMatch, hm', hOldm, hw'] using (hcons m' w')

-- A concrete proposal step preserves consistency.
lemma stepWith_consistent
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hcons : consistent P σ.matching) (hm : σ.matching.menMatches m = none) :
    consistent P (GSState.stepWith P σ m w).matching := by
  classical
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · simp [GSState.stepWith, hw, hpref, consistent_matchUnmatched, hcons, hm]
      ·
        have hEq := stepWith_matching_eq_of_reject_none P σ m w hw hpref
        simpa [hEq] using hcons
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · simp [GSState.stepWith, hw, hpref, consistent_swapMatch, hcons, hm]
      ·
        have hEq := stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref
        simpa [hEq] using hcons

-- A generic step preserves consistency.
lemma step_consistent
    (P : Problem) (σ : GSState P) (hcons : consistent P σ.matching) :
    consistent P (GSState.step P σ).matching := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := _root_.StableMarriageLean.chooseMaxCandidate P σ m hm.2
    simpa [GSState.step, hfree, m, w] using
      (stepWith_consistent P σ m w hcons hm.1)
  · simpa [GSState.step, hfree] using hcons

-- A generic step preserves men's acceptability.
lemma step_menAcceptable
    (P : Problem) (σ : GSState P) (hmen : menAcceptableState P σ) :
    menAcceptableState P (GSState.step P σ) := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := _root_.StableMarriageLean.chooseMaxCandidate P σ m hm.2
    have hwmem : w ∈ candidateWomen P σ m :=
      _root_.StableMarriageLean.chooseMaxCandidate_mem P σ m hm.2
    have hacc : P.menPrefs.acceptable m w := by
      have hmem : P.menPrefs.acceptable m w ∧ ¬ σ.proposed m w := by
        simpa [candidateWomen] using hwmem
      exact hmem.1
    simpa [GSState.step, hfree, m, w] using
      (menAcceptable_stepWith P σ m w hacc hmen)
  · simpa [GSState.step, hfree] using hmen

-- A generic step preserves women's acceptability.
lemma step_womenAcceptable
    (P : Problem) (σ : GSState P) (hwomen : womenAcceptableState P σ) :
    womenAcceptableState P (GSState.step P σ) := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := _root_.StableMarriageLean.chooseMaxCandidate P σ m hm.2
    simpa [GSState.step, hfree, m, w] using
      (womenAcceptable_stepWith P σ m w hwomen)
  · simpa [GSState.step, hfree] using hwomen

-- The initial matching is consistent.
lemma initial_consistent (P : Problem) : consistent P (GSState.initial P).matching := by
  intro m w
  simp [GSState.initial]

-- All iterated steps preserve consistency.
lemma runSteps_consistent (P : Problem) (n : Nat) :
    consistent P (GSState.runSteps P n).matching := by
  induction n with
  | zero =>
      simpa using initial_consistent P
  | succ n ih =>
      simpa [GSState.runSteps] using step_consistent P _ ih

-- All iterated steps preserve men's acceptability.
lemma runSteps_menAcceptable (P : Problem) (n : Nat) :
    menAcceptableState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa using initial_menAcceptable P
  | succ n ih =>
      simpa [GSState.runSteps] using step_menAcceptable P _ ih

-- All iterated steps preserve women's acceptability.
lemma runSteps_womenAcceptable (P : Problem) (n : Nat) :
    womenAcceptableState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa using initial_womenAcceptable P
  | succ n ih =>
      simpa [GSState.runSteps] using step_womenAcceptable P _ ih

-- Proposed pairs are downward-closed under men's preferences.
def menProposedDownwardState (P : Problem) (σ : GSState P) : Prop :=
  ∀ m w w', σ.proposed m w → P.menPrefs.prefers m w' w → σ.proposed m w'

-- The initial state is downward-closed (no proposals).
lemma initial_menProposedDownward (P : Problem) :
    menProposedDownwardState P (GSState.initial P) := by
  intro m w w' hprop
  simp [GSState.initial] at hprop

-- A generic step preserves downward-closure of proposals.
lemma step_menProposedDownward
    (P : Problem) (σ : GSState P) (hdown : menProposedDownwardState P σ) :
    menProposedDownwardState P (GSState.step P σ) := by
  classical
  -- Split on whether there is a free man who can still propose.
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    intro m' w' w'' hprop hpref
    have hprop' :
        σ.proposed m' w' ∨ (m' = m ∧ w' = w) := by
      simpa [GSState.step, hfree, m, w, stepWith_proposed] using hprop
    cases hprop' with
    | inl hpropOld =>
        have hpropOld' := hdown _ _ _ hpropOld hpref
        simp [GSState.step, hfree, stepWith_proposed, hpropOld']
    | inr hnew =>
        rcases hnew with ⟨hm', hw'⟩
        subst hm'
        subst hw'
        have hpropOld' : σ.proposed m w'' := by
          by_contra hnot
          have hacc : P.menPrefs.acceptable m w'' :=
            P.menPrefs.prefers_acceptable_left m _ _ hpref
          have hmem : w'' ∈ candidateWomen P σ m := by
            simp [candidateWomen, hacc, hnot]
          exact (chooseMaxCandidate_no_better P σ m hm.2 _ hmem hpref)
        simp [GSState.step, hfree, stepWith_proposed, hpropOld']
  ·
    simpa [GSState.step, hfree] using hdown

-- Running steps preserves downward-closure of proposals.
lemma runSteps_menProposedDownward (P : Problem) (n : Nat) :
    menProposedDownwardState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa [GSState.runSteps] using initial_menProposedDownward P
  | succ n ih =>
      simpa [GSState.runSteps] using step_menProposedDownward P _ ih

-- Every matched man has already proposed to his match.
def menMatchedProposedState (P : Problem) (σ : GSState P) : Prop :=
  ∀ m w, σ.matching.menMatches m = some w → σ.proposed m w

-- The initial state has no matched pairs.
lemma initial_menMatchedProposed (P : Problem) :
    menMatchedProposedState P (GSState.initial P) := by
  intro m w hmatch
  simp [GSState.initial] at hmatch

-- StepWith preserves the property that matches are proposed.
lemma stepWith_menMatchedProposed
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hprop : menMatchedProposedState P σ) :
    menMatchedProposedState P (GSState.stepWith P σ m w) := by
  classical
  intro m' w' hmatch
  -- Track whether the recipient woman is currently matched.
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · by_cases hm : m' = m
        · cases hm
          have hmatch' :
              (Matching.matchUnmatched P σ.matching m w).menMatches m = some w' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have : w' = w := by
            simpa [Matching.matchUnmatched, eq_comm] using hmatch'
          subst this
          simp [stepWith_proposed]
        · have hmatch' : σ.matching.menMatches m' = some w' := by
            have hmatch' :
                (Matching.matchUnmatched P σ.matching m w).menMatches m' = some w' := by
              simpa [GSState.stepWith, hw, hpref] using hmatch
            simpa [Matching.matchUnmatched, hm] using hmatch'
          have hprop' := hprop _ _ hmatch'
          simp [stepWith_proposed, hprop']
      ·
        have hmatch' : σ.matching.menMatches m' = some w' := by
          simpa [stepWith_matching_eq_of_reject_none P σ m w hw hpref] using hmatch
        have hprop' := hprop _ _ hmatch'
        simp [stepWith_proposed, hprop']
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · by_cases hm : m' = m
        · cases hm
          have hmatch' :
              (Matching.swapMatch P σ.matching m mOld w).menMatches m = some w' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          by_cases hmOld : mOld = m
          · cases hmOld
            have : (none : Option P.Women) = some w' := by
              have hmatch'' := hmatch'
              simp [Matching.swapMatch] at hmatch''
            cases this
          · have : w' = w := by
              have hmOld' : m ≠ mOld := by
                simpa [eq_comm] using hmOld
              simpa [Matching.swapMatch, hmOld', eq_comm] using hmatch'
            subst this
            simp [stepWith_proposed]
        · by_cases hmOld : m' = mOld
          · subst hmOld
            have : (none : Option P.Women) = some w' := by
              have hmatch' :
                  (Matching.swapMatch P σ.matching m m' w).menMatches m' = some w' := by
                simpa [GSState.stepWith, hw, hpref] using hmatch
              have hmatch'' := hmatch'
              simp [Matching.swapMatch] at hmatch''
            cases this
          · have hmatch' : σ.matching.menMatches m' = some w' := by
              have hmatch' :
                  (Matching.swapMatch P σ.matching m mOld w).menMatches m' = some w' := by
                simpa [GSState.stepWith, hw, hpref] using hmatch
              simpa [Matching.swapMatch, hm, hmOld] using hmatch'
            have hprop' := hprop _ _ hmatch'
            simp [stepWith_proposed, hprop']
      ·
        have hmatch' : σ.matching.menMatches m' = some w' := by
          simpa [stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref] using hmatch
        have hprop' := hprop _ _ hmatch'
        simp [stepWith_proposed, hprop']

-- A generic step preserves the property that matches are proposed.
lemma step_menMatchedProposed
    (P : Problem) (σ : GSState P) (hprop : menMatchedProposedState P σ) :
    menMatchedProposedState P (GSState.step P σ) := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    simpa [GSState.step, hfree, m, w] using
      (stepWith_menMatchedProposed P σ m w hprop)
  · simpa [GSState.step, hfree] using hprop

-- Running steps preserves the property that matches are proposed.
lemma runSteps_menMatchedProposed (P : Problem) (n : Nat) :
    menMatchedProposedState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa [GSState.runSteps] using initial_menMatchedProposed P
  | succ n ih =>
      simpa [GSState.runSteps] using step_menMatchedProposed P _ ih

-- If a woman is unmatched, then any man who has proposed to her is unacceptable.
def womenUnmatchedRejectState (P : Problem) (σ : GSState P) : Prop :=
  ∀ w m, σ.matching.womenMatches w = none → σ.proposed m w → ¬ P.womenPrefs.acceptable w m

-- The initial state has no acceptable proposers for unmatched women.
lemma initial_womenUnmatchedReject (P : Problem) : womenUnmatchedRejectState P (GSState.initial P) := by
  intro w m hmatch hprop
  simp [GSState.initial] at hprop

-- StepWith preserves the unmatched-rejection property.
lemma stepWith_womenUnmatchedReject
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hrej : womenUnmatchedRejectState P σ) :
    womenUnmatchedRejectState P (GSState.stepWith P σ m w) := by
  classical
  intro w' m' hmatch hprop
  -- Track the current match status of the recipient woman.
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · by_cases hw' : w' = w
        · cases hw'
          have : (GSState.stepWith P σ m w).matching.womenMatches w ≠ none := by
            simp [GSState.stepWith, hw, hpref, Matching.matchUnmatched]
          exact (this hmatch).elim
        ·
          have hmatch' : σ.matching.womenMatches w' = none := by
            simpa [GSState.stepWith, hw, hpref, Matching.matchUnmatched, hw'] using hmatch
          have hprop' : σ.proposed m' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hrej _ _ hmatch' hprop'
      · by_cases hw' : w' = w
        · cases hw'
          have hacc : ¬ P.womenPrefs.acceptable w m := by
            simpa [prefersOpt] using hpref
          have hprop' :
              σ.proposed m' w ∨ (m' = m ∧ w = w) := by
            simpa [stepWith_proposed] using hprop
          cases hprop' with
          | inl hpropOld =>
              exact hrej _ _ hw hpropOld
          | inr hnew =>
              rcases hnew with ⟨hm', _⟩
              cases hm'
              exact hacc
        ·
          have hmatch' : σ.matching.womenMatches w' = none := by
            simpa [GSState.stepWith, hw, hpref, Matching.matchUnmatched, hw'] using hmatch
          have hprop' : σ.proposed m' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hrej _ _ hmatch' hprop'
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · by_cases hw' : w' = w
        · cases hw'
          have : (GSState.stepWith P σ m w).matching.womenMatches w ≠ none := by
            simp [GSState.stepWith, hw, hpref, Matching.swapMatch]
          exact (this hmatch).elim
        ·
          have hmatch' : σ.matching.womenMatches w' = none := by
            simpa [GSState.stepWith, hw, hpref, Matching.swapMatch, hw'] using hmatch
          have hprop' : σ.proposed m' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hrej _ _ hmatch' hprop'
      · by_cases hw' : w' = w
        · cases hw'
          have : (GSState.stepWith P σ m w).matching.womenMatches w ≠ none := by
            simp [GSState.stepWith, hw, hpref]
          exact (this hmatch).elim
        ·
          have hmatch' : σ.matching.womenMatches w' = none := by
            simpa [GSState.stepWith, hw, hpref, Matching.swapMatch, hw'] using hmatch
          have hprop' : σ.proposed m' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hrej _ _ hmatch' hprop'

-- A generic step preserves unmatched-rejection.
lemma step_womenUnmatchedReject
    (P : Problem) (σ : GSState P) (hrej : womenUnmatchedRejectState P σ) :
    womenUnmatchedRejectState P (GSState.step P σ) := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    simpa [GSState.step, hfree, m, w] using
      (stepWith_womenUnmatchedReject P σ m w hrej)
  · simpa [GSState.step, hfree] using hrej

-- Running steps preserves unmatched-rejection.
lemma runSteps_womenUnmatchedReject (P : Problem) (n : Nat) :
    womenUnmatchedRejectState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa [GSState.runSteps] using initial_womenUnmatchedReject P
  | succ n ih =>
      simpa [GSState.runSteps] using step_womenUnmatchedReject P _ ih

-- A woman's current match is at least as preferred as any proposer.
def womenBestState (P : Problem) (σ : GSState P) : Prop :=
  ∀ w m m',
    σ.matching.womenMatches w = some m →
    σ.proposed m' w →
    m' ≠ m →
    prefersOpt P.womenPrefs w (some m) (some m')

-- The initial state satisfies the women's best-match property.
lemma initial_womenBest (P : Problem) : womenBestState P (GSState.initial P) := by
  intro w m m' hmatch
  simp [GSState.initial] at hmatch

-- StepWith preserves the women's best-match property.
lemma stepWith_womenBest
    (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women)
    (hwomen : womenAcceptableState P σ)
    (hrej : womenUnmatchedRejectState P σ)
    (hbest : womenBestState P σ) :
    womenBestState P (GSState.stepWith P σ m w) := by
  classical
  intro w' m' m'' hmatch hprop hne
  -- Split on whether the recipient woman is currently matched.
  cases hw : σ.matching.womenMatches w with
  | none =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) none
      · by_cases hw' : w' = w
        · cases hw'
          have hmatch' :
              (Matching.matchUnmatched P σ.matching m w).womenMatches w = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have hm' : m' = m := by
            simpa [Matching.matchUnmatched, eq_comm] using hmatch'
          cases hm'
          have hprop' :
              σ.proposed m'' w ∨ (m'' = m ∧ w = w) := by
            simpa [stepWith_proposed] using hprop
          cases hprop' with
          | inl hpropOld =>
              have haccm : P.womenPrefs.acceptable w m := by
                exact prefersOpt_left_acceptable (p := P.womenPrefs) (a := w) (o1 := m) (o2 := none) hpref
              have hacc'' : ¬ P.womenPrefs.acceptable w m'' := by
                exact hrej _ _ hw hpropOld
              simp [prefersOpt, haccm, hacc'']
          | inr hnew =>
              rcases hnew with ⟨hm'', _⟩
              cases hm''
              exact (hne rfl).elim
        ·
          have hmatch' : σ.matching.womenMatches w' = some m' := by
            have hmatch' :
                (Matching.matchUnmatched P σ.matching m w).womenMatches w' = some m' := by
              simpa [GSState.stepWith, hw, hpref] using hmatch
            simpa [Matching.matchUnmatched, hw'] using hmatch'
          have hprop' : σ.proposed m'' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hbest _ _ _ hmatch' hprop' hne
      ·
        by_cases hw' : w' = w
        · cases hw'
          have hmatch' : σ.matching.womenMatches w = some m' := by
            simpa [stepWith_matching_eq_of_reject_none P σ m w hw hpref] using hmatch
          simp [hw] at hmatch'
        ·
          have hmatch' : σ.matching.womenMatches w' = some m' := by
            simpa [stepWith_matching_eq_of_reject_none P σ m w hw hpref] using hmatch
          have hprop' : σ.proposed m'' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hbest _ _ _ hmatch' hprop' hne
  | some mOld =>
      by_cases hpref : prefersOpt P.womenPrefs w (some m) (some mOld)
      · by_cases hw' : w' = w
        · cases hw'
          have hmatch' :
              (Matching.swapMatch P σ.matching m mOld w).womenMatches w = some m' := by
            simpa [GSState.stepWith, hw, hpref] using hmatch
          have hm' : m' = m := by
            simpa [Matching.swapMatch, eq_comm] using hmatch'
          cases hm'
          have hprop' :
              σ.proposed m'' w ∨ (m'' = m ∧ w = w) := by
            simpa [stepWith_proposed] using hprop
          cases hprop' with
          | inl hpropOld =>
              by_cases hEq : m'' = mOld
              · subst hEq
                simpa using hpref
              · by_cases hacc'' : P.womenPrefs.acceptable w m''
                · have haccm : P.womenPrefs.acceptable w m := by
                    exact prefersOpt_left_acceptable (p := P.womenPrefs) (a := w) (o1 := m) (o2 := some mOld) hpref
                  have haccOld : P.womenPrefs.acceptable w mOld := by
                    exact hwomen _ _ hw
                  have hpref' : P.womenPrefs.prefers w m mOld := by
                    simpa [prefersOpt, haccm, haccOld] using hpref
                  have hbestOld : P.womenPrefs.prefers w mOld m'' := by
                    have := hbest _ _ _ hw hpropOld hEq
                    simpa [prefersOpt, haccOld, hacc''] using this
                  have htrans := P.womenPrefs.prefers_trans w m mOld m'' hpref' hbestOld
                  simpa [prefersOpt, haccm, hacc''] using htrans
                ·
                  have haccm : P.womenPrefs.acceptable w m := by
                    exact prefersOpt_left_acceptable (p := P.womenPrefs) (a := w) (o1 := m) (o2 := some mOld) hpref
                  simp [prefersOpt, haccm, hacc'']
          | inr hnew =>
              rcases hnew with ⟨hm'', _⟩
              cases hm''
              exact (hne rfl).elim
        ·
          have hmatch' : σ.matching.womenMatches w' = some m' := by
            have hmatch' :
                (Matching.swapMatch P σ.matching m mOld w).womenMatches w' = some m' := by
              simpa [GSState.stepWith, hw, hpref] using hmatch
            simpa [Matching.swapMatch, hw'] using hmatch'
          have hprop' : σ.proposed m'' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hbest _ _ _ hmatch' hprop' hne
      ·
        by_cases hw' : w' = w
        · cases hw'
          have hmatch' : σ.matching.womenMatches w = some m' := by
            simpa [stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref] using hmatch
          have hm' : mOld = m' := by
            simpa [hw] using hmatch'
          cases hm'
          have hprop' :
              σ.proposed m'' w ∨ (m'' = m ∧ w = w) := by
            simpa [stepWith_proposed] using hprop
          cases hprop' with
          | inl hpropOld =>
              exact hbest _ _ _ hw hpropOld hne
          | inr hnew =>
              rcases hnew with ⟨hm'', _⟩
              cases hm''
              have haccOld : P.womenPrefs.acceptable w m' := hwomen _ _ hw
              by_cases haccm : P.womenPrefs.acceptable w m
              · have hneq : m' ≠ m := by
                  intro hEq
                  subst hEq
                  exact hne rfl
                have htot :=
                  P.womenPrefs.prefers_total w m' m haccOld haccm hneq
                cases htot with
                | inl hprefOld =>
                    simpa [prefersOpt, haccOld, haccm] using hprefOld
                | inr hprefNew =>
                    have : prefersOpt P.womenPrefs w (some m) (some m') := by
                      simpa [prefersOpt, haccm, haccOld] using hprefNew
                    exact (hpref this).elim
              ·
                simp [prefersOpt, haccOld, haccm]
        ·
          have hmatch' : σ.matching.womenMatches w' = some m' := by
            simpa [stepWith_matching_eq_of_reject_some P σ m w mOld hw hpref] using hmatch
          have hprop' : σ.proposed m'' w' := by
            simpa [stepWith_proposed, hw'] using hprop
          exact hbest _ _ _ hmatch' hprop' hne

-- A generic step preserves the women's best-match property.
lemma step_womenBest
    (P : Problem) (σ : GSState P)
    (hwomen : womenAcceptableState P σ)
    (hrej : womenUnmatchedRejectState P σ)
    (hbest : womenBestState P σ) :
    womenBestState P (GSState.step P σ) := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    simpa [GSState.step, hfree, m, w] using
      (stepWith_womenBest P σ m w hwomen hrej hbest)
  · simpa [GSState.step, hfree] using hbest

-- Running steps preserves the women's best-match property.
lemma runSteps_womenBest (P : Problem) (n : Nat) :
    womenBestState P (GSState.runSteps P n) := by
  induction n with
  | zero =>
      simpa [GSState.runSteps] using initial_womenBest P
  | succ n ih =>
      have hwomen := runSteps_womenAcceptable P n
      have hrej := runSteps_womenUnmatchedReject P n
      simpa [GSState.runSteps] using step_womenBest P _ hwomen hrej ih

-- If a free man exists, the next step adds a new proposal.
lemma proposedCount_step_of_free
    (P : Problem) (σ : GSState P) (hfree : ∃ m, isFree P σ m) :
    proposedCount P (GSState.step P σ) = proposedCount P σ + 1 := by
  classical
  let m := Classical.choose hfree
  have hm : isFree P σ m := Classical.choose_spec hfree
  let w := _root_.StableMarriageLean.chooseMaxCandidate P σ m hm.2
  have hwmem : w ∈ candidateWomen P σ m :=
    _root_.StableMarriageLean.chooseMaxCandidate_mem P σ m hm.2
  have hnew : ¬ σ.proposed m w := by
    have hmem : P.menPrefs.acceptable m w ∧ ¬ σ.proposed m w := by
      simpa [candidateWomen] using hwmem
    exact hmem.2
  simpa [GSState.step, hfree, m, w] using
    (proposedCount_stepWith P σ m w hnew)

-- If a free man exists, not all pairs have been proposed.
lemma proposedCount_lt_bound_of_free
    (P : Problem) (σ : GSState P) (hfree : ∃ m, isFree P σ m) :
    proposedCount P σ < proposalBound P := by
  classical
  letI := P.menFintype
  letI := P.womenFintype
  letI : Fintype (P.Men × P.Women) := inferInstance
  let m := Classical.choose hfree
  have hm : isFree P σ m := Classical.choose_spec hfree
  let w := _root_.StableMarriageLean.chooseMaxCandidate P σ m hm.2
  have hwmem : w ∈ candidateWomen P σ m :=
    _root_.StableMarriageLean.chooseMaxCandidate_mem P σ m hm.2
  have hnew : ¬ σ.proposed m w := by
    have hmem : P.menPrefs.acceptable m w ∧ ¬ σ.proposed m w := by
      simpa [candidateWomen] using hwmem
    exact hmem.2
  have hnotmem : (m, w) ∉ proposedSet P σ := by
    simp [proposedSet, hnew]
  have hssub : proposedSet P σ ⊂ (Finset.univ : Finset (P.Men × P.Women)) := by
    have hsubset :
        proposedSet P σ ⊆ (Finset.univ : Finset (P.Men × P.Women)) := by
      intro x hx
      simp
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    refine ⟨(m, w), ?_, hnotmem⟩
    simp
  have hcard :
      (proposedSet P σ).card <
        (Finset.univ : Finset (P.Men × P.Women)).card :=
    Finset.card_lt_card hssub
  simpa [proposedCount, proposalBound, Fintype.card_prod] using hcard

-- If a state is terminated, stepping does nothing.
lemma step_eq_of_terminated
    (P : Problem) (σ : GSState P) (h : terminated P σ) :
    GSState.step P σ = σ := by
  classical
  have hfree : ¬ ∃ m, isFree P σ m := by
    simpa [terminated] using h
  by_cases hfree' : ∃ m, isFree P σ m
  · exact (False.elim (hfree hfree'))
  · simp [GSState.step, hfree']

-- Once terminated, additional steps do not change the state.
lemma runSteps_eq_of_terminated
    (P : Problem) (n k : Nat)
    (h : terminated P (GSState.runSteps P n)) :
    GSState.runSteps P (n + k) = GSState.runSteps P n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hterm : terminated P (GSState.runSteps P (n + k)) := by
        simpa [ih] using h
      calc
        GSState.runSteps P (n + Nat.succ k) =
            GSState.step P (GSState.runSteps P (n + k)) := by
              simp [GSState.runSteps]
        _ = GSState.runSteps P (n + k) := by
              simpa using step_eq_of_terminated P _ hterm
        _ = GSState.runSteps P n := ih

-- If a runSteps state is not terminated, then the proposal count equals the step number.
lemma proposedCount_runSteps_eq_of_not_terminated
    (P : Problem) (n : Nat) :
    ¬ terminated P (GSState.runSteps P n) →
      proposedCount P (GSState.runSteps P n) = n := by
  classical
  induction n with
  | zero =>
      intro _
      simpa [GSState.runSteps] using proposedCount_initial P
  | succ n ih =>
      intro hnot
      have hnot' : ¬ terminated P (GSState.runSteps P n) := by
        intro hterm
        have hEq := runSteps_eq_of_terminated P n 1 hterm
        have : terminated P (GSState.runSteps P (n + 1)) := by
          simpa [hEq] using hterm
        exact hnot this
      have hfree : ∃ m, isFree P (GSState.runSteps P n) m := by
        by_contra hfree
        exact hnot' (by simpa [terminated] using hfree)
      calc
        proposedCount P (GSState.runSteps P (n + 1)) =
            proposedCount P (GSState.runSteps P n) + 1 := by
              simpa [GSState.runSteps] using
                proposedCount_step_of_free P _ hfree
        _ = n + 1 := by
              simp [ih hnot']

end

end StableMarriageLean
