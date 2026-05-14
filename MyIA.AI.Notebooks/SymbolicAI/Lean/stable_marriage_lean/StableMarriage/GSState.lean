/-
  Stable Marriage - Gale-Shapley Algorithm State
  ================================================

  Intermediate state for the Gale-Shapley deferred acceptance algorithm.
  Uses Option-based partial matching during algorithm execution,
  converting to total bijective Matching at termination.

  Adapted from: https://github.com/mmaaz-git/stable-marriage-lean (v4.25.0)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite
import StableMarriage.Definitions

namespace StableMarriage

open Function Finset Classical

variable {n : Nat} [NeZero n]

/-- Partial matching during GS algorithm execution. -/
structure GSMatching (n : Nat) [NeZero n] where
  menMatch : Fin n → Option (Fin n)
  womenMatch : Fin n → Option (Fin n)

namespace GSMatching

def initial : GSMatching n where
  menMatch := fun _ => none
  womenMatch := fun _ => none

def matchFree (μ : GSMatching n) (m w : Fin n) : GSMatching n where
  menMatch := Function.update μ.menMatch m (some w)
  womenMatch := Function.update μ.womenMatch w (some m)

def swapMatch (μ : GSMatching n) (m mOld w : Fin n) : GSMatching n where
  menMatch := Function.update (Function.update μ.menMatch m (some w)) mOld none
  womenMatch := Function.update μ.womenMatch w (some m)

end GSMatching

/-- Intermediate state for the Gale-Shapley deferred acceptance algorithm. -/
structure GSState (prof : PrefProfile n) where
  matching : GSMatching n
  proposed : Fin n → Fin n → Prop

section GSDefs

variable (prof : PrefProfile n)

def gsInitial : GSState prof where
  matching := GSMatching.initial
  proposed := fun _ _ => False

noncomputable def gsCandidates (σ : GSState prof) (m : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => ¬ σ.proposed m w)

def gsIsFree (σ : GSState prof) (m : Fin n) : Prop :=
  σ.matching.menMatch m = none ∧ (gsCandidates prof σ m).Nonempty

def gsTerminated (σ : GSState prof) : Prop :=
  ¬ ∃ m, gsIsFree prof σ m

def gsMenPrefLE (m : Fin n) (w1 w2 : Fin n) : Prop :=
  w1 = w2 ∨ prof.menPref m w2 < prof.menPref m w1

noncomputable def gsChooseMax (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) : Fin n :=
  letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩
  haveI : IsTrans (Fin n) (· ≤ ·) :=
    ⟨fun a b c hab hbc => by
      cases hab with
      | inl hab => subst hab; exact hbc
      | inr hab =>
        cases hbc with
        | inl hbc => subst hbc; exact Or.inr hab
        | inr hbc => exact Or.inr (lt_trans hbc hab)⟩
  Classical.choose ((gsCandidates prof σ m).exists_maximal h)

noncomputable def gsStepWith (σ : GSState prof) (m w : Fin n) : GSState prof :=
  let proposed' : Fin n → Fin n → Prop :=
    fun m' w' => σ.proposed m' w' ∨ (m' = m ∧ w' = w)
  match _ : σ.matching.womenMatch w with
  | none =>
      { matching := σ.matching.matchFree m w
        proposed := proposed' }
  | some mOld =>
      if prof.womenPref w m < prof.womenPref w mOld then
        { matching := σ.matching.swapMatch m mOld w
          proposed := proposed' }
      else
        { matching := σ.matching
          proposed := proposed' }

noncomputable def gsStep (σ : GSState prof) : GSState prof :=
  if hfree : ∃ m, gsIsFree prof σ m then
    let m := Classical.choose hfree
    have hm : gsIsFree prof σ m := Classical.choose_spec hfree
    let w := gsChooseMax prof σ m hm.2
    gsStepWith prof σ m w
  else
    σ

end GSDefs

-- These defs use explicit prof parameter to avoid section variable duplication
noncomputable def gsRunSteps (prof : PrefProfile n) (k : Nat) : GSState prof :=
  match k with
  | 0 => gsInitial prof
  | k' + 1 => gsStep prof (gsRunSteps prof k')

def gsProposalBound (n : Nat) [NeZero n] : Nat := n * n

noncomputable def gsGaleShapley (prof : PrefProfile n) : GSMatching n :=
  (gsRunSteps prof (gsProposalBound n)).matching

/-! ## gsChooseMax helper lemmas -/

/-- The chosen maximal candidate is in the candidate set. -/
lemma gsChooseMax_mem (prof : PrefProfile n) (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) :
    gsChooseMax prof σ m h ∈ gsCandidates prof σ m := by
  unfold gsChooseMax
  letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩
  haveI : IsTrans (Fin n) (· ≤ ·) :=
    ⟨fun a b c hab hbc => by
      cases hab with
      | inl hab => subst hab; exact hbc
      | inr hab =>
        cases hbc with
        | inl hbc => subst hbc; exact Or.inr hab
        | inr hbc => exact Or.inr (lt_trans hbc hab)⟩
  obtain ⟨hmem, -⟩ := Classical.choose_spec (Finset.exists_maximal h)
  exact hmem

/-- No unproposed candidate is preferred over the chosen maximal one.
    Direct from maximality: ∀ y ∈ candidates, y ≤ choose. -/
lemma gsChooseMax_maximal (prof : PrefProfile n) (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) (w : Fin n)
    (hw : w ∈ gsCandidates prof σ m) :
    gsMenPrefLE prof m w (gsChooseMax prof σ m h) := by
  sorry

end StableMarriage
