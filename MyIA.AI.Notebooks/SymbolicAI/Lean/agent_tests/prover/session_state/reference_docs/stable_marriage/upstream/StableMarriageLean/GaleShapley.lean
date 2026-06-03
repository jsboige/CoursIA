import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite
import StableMarriageLean.Basic

namespace StableMarriageLean

noncomputable section
open Classical

-- A Gale-Shapley state: a current matching plus the proposals already made.
structure GSState (P : Problem) where
  matching : Matching P
  proposed : P.Men → P.Women → Prop

-- Initial state: everyone unmatched and no proposals made.
def GSState.initial (P : Problem) : GSState P :=
  { matching :=
      { menMatches := fun _ => none
        womenMatches := fun _ => none },
    proposed := fun _ _ => False }

-- Women a man can still propose to (acceptable and not yet proposed).
def candidateWomen (P : Problem) (σ : GSState P) (m : P.Men) : Finset P.Women := by
  classical
  letI := P.womenFintype
  exact Finset.univ.filter (fun w => P.menPrefs.acceptable m w ∧ ¬ σ.proposed m w)

-- A free man who still has someone to propose to.
def isFree (P : Problem) (σ : GSState P) (m : P.Men) : Prop :=
  σ.matching.menMatches m = none ∧ (candidateWomen P σ m).Nonempty

-- A state is terminated if no man is free with someone left to propose to.
def terminated (P : Problem) (σ : GSState P) : Prop :=
  ¬ ∃ m, isFree P σ m

-- Choose an element from a nonempty finset.
def chooseFromFinset {α : Type*} (s : Finset α) (h : s.Nonempty) : α :=
  Classical.choose h

lemma chooseFromFinset_mem {α : Type*} (s : Finset α) (h : s.Nonempty) :
    chooseFromFinset s h ∈ s :=
  Classical.choose_spec h

-- Men compare women by "at least as preferred as": equality or strict preference.
def menPrefLE (P : Problem) (m : P.Men) (w1 w2 : P.Women) : Prop :=
  w1 = w2 ∨ P.menPrefs.prefers m w2 w1

-- The men-preference preorder is transitive.
lemma menPrefLE_trans (P : Problem) (m : P.Men) :
    IsTrans P.Women (menPrefLE P m) := by
  refine ⟨?_⟩
  intro a b c hab hbc
  cases hab with
  | inl hab =>
      subst hab
      exact hbc
  | inr hab =>
      cases hbc with
      | inl hbc =>
          subst hbc
          exact Or.inr hab
      | inr hbc =>
          exact Or.inr (P.menPrefs.prefers_trans m _ _ _ hbc hab)

-- Choose a maximal (most preferred) woman from the remaining candidates.
def chooseMaxCandidate (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) : P.Women := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  exact Classical.choose ((candidateWomen P σ m).exists_maximal h)

lemma chooseMaxCandidate_mem (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) :
    chooseMaxCandidate P σ m h ∈ candidateWomen P σ m := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  simpa using (Classical.choose_spec ((candidateWomen P σ m).exists_maximal h)).1

lemma chooseMaxCandidate_no_better (P : Problem) (σ : GSState P) (m : P.Men)
    (h : (candidateWomen P σ m).Nonempty) :
    ∀ w' ∈ candidateWomen P σ m,
      ¬ P.menPrefs.prefers m w' (chooseMaxCandidate P σ m h) := by
  classical
  letI : LE P.Women := ⟨menPrefLE P m⟩
  haveI : IsTrans P.Women (· ≤ ·) := menPrefLE_trans P m
  have hmax :
      Maximal (· ∈ candidateWomen P σ m) (chooseMaxCandidate P σ m h) := by
    simpa using (Classical.choose_spec ((candidateWomen P σ m).exists_maximal h))
  intro w' hw' hpref
  have hle : menPrefLE P m (chooseMaxCandidate P σ m h) w' := Or.inr hpref
  have hle' := hmax.2 hw' hle
  cases hle' with
  | inl hEq =>
      subst hEq
      exact (P.menPrefs.prefers_irrefl m _) hpref
  | inr hpref' =>
      have := P.menPrefs.prefers_trans m _ _ _ hpref' hpref
      exact (P.menPrefs.prefers_irrefl m _) this

-- Match m with w when w is currently unmatched.
def Matching.matchUnmatched
    (P : Problem) (μ : Matching P) (m : P.Men) (w : P.Women) : Matching P := by
  classical
  exact
    { menMatches := Function.update μ.menMatches m (some w)
      womenMatches := Function.update μ.womenMatches w (some m) }

-- Swap m in for mOld when w prefers m to mOld.
def Matching.swapMatch
    (P : Problem) (μ : Matching P) (m mOld : P.Men) (w : P.Women) :
    Matching P := by
  classical
  exact
    { menMatches := Function.update (Function.update μ.menMatches m (some w)) mOld none
      womenMatches := Function.update μ.womenMatches w (some m) }

-- One proposal step with an explicit proposer and recipient.
def GSState.stepWith (P : Problem) (σ : GSState P) (m : P.Men) (w : P.Women) : GSState P :=
  let proposed' : P.Men → P.Women → Prop :=
    fun m' w' => σ.proposed m' w' ∨ (m' = m ∧ w' = w)
  match σ.matching.womenMatches w with
  | none =>
      if prefersOpt P.womenPrefs w (some m) none then
        { matching := Matching.matchUnmatched P σ.matching m w
          proposed := proposed' }
      else
        { matching := σ.matching
          proposed := proposed' }
  | some mOld =>
      if prefersOpt P.womenPrefs w (some m) (some mOld) then
        { matching := Matching.swapMatch P σ.matching m mOld w
          proposed := proposed' }
      else
        { matching := σ.matching
          proposed := proposed' }

-- One proposal step of the Gale-Shapley algorithm.
def GSState.step (P : Problem) (σ : GSState P) : GSState P := by
  classical
  by_cases hfree : ∃ m, isFree P σ m
  · classical
    let m := Classical.choose hfree
    have hm : isFree P σ m := Classical.choose_spec hfree
    let w := chooseMaxCandidate P σ m hm.2
    exact GSState.stepWith P σ m w
  · exact σ

-- Iterate a fixed number of steps (bounded by number of proposals).
def GSState.runSteps (P : Problem) : Nat → GSState P
  | 0 => GSState.initial P
  | n + 1 => GSState.step P (GSState.runSteps P n)

-- Total number of possible proposals.
def proposalBound (P : Problem) : Nat := by
  classical
  letI := P.menFintype
  letI := P.womenFintype
  exact Fintype.card P.Men * Fintype.card P.Women

-- The Gale-Shapley matching after all proposals.
def galeShapley (P : Problem) : Matching P :=
  by
    classical
    exact (GSState.runSteps P (proposalBound P)).matching

end

end StableMarriageLean
