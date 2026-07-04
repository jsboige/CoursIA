/-
  Mariage stable — État de l'algorithme de Gale-Shapley
  ======================================================

  État intermédiaire pour l'algorithme d'acceptation différée de Gale-Shapley.
  Utilise un couplage partiel basé sur `Option` pendant l'exécution de l'algorithme,
  converti en couplage bijectif total à la terminaison.

  Convention i18n (cf #4980) : en-têtes, sections, docstrings et commentaires
  intra-preuve en français ; noms de symboles Lean, énoncés de lemmes et
  tactiques préservés en anglais (compatibilité Mathlib).

  Adapté de : https://github.com/mmaaz-git/stable-marriage-lean (v4.25.0)
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite
import StableMarriage.Definitions

namespace StableMarriage

open Function Finset Classical

variable {n : Nat} [NeZero n]

/-- Couplage partiel pendant l'exécution de l'algorithme GS. -/
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

/-- État intermédiaire pour l'algorithme d'acceptation différée de Gale-Shapley. -/
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

-- Ces définitions utilisent le paramètre explicite `prof` pour éviter la duplication
-- des variables de section.
noncomputable def gsRunSteps (prof : PrefProfile n) (k : Nat) : GSState prof :=
  match k with
  | 0 => gsInitial prof
  | k' + 1 => gsStep prof (gsRunSteps prof k')

def gsProposalBound (n : Nat) [NeZero n] : Nat := n * n

noncomputable def gsGaleShapley (prof : PrefProfile n) : GSMatching n :=
  (gsRunSteps prof (gsProposalBound n)).matching

/-! ## Lemmes auxiliaires pour `gsChooseMax` -/

/-- La candidate maximale choisie appartient à l'ensemble des candidates. -/
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

/-- Aucune candidate non-proposée n'est préférée à la candidate maximale choisie.
    Directement depuis la maximalité : ∀ y ∈ candidates, y ≤ choose. -/
lemma gsChooseMax_maximal (prof : PrefProfile n) (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) (w : Fin n)
    (hw : w ∈ gsCandidates prof σ m) :
    gsMenPrefLE prof m w (gsChooseMax prof σ m h) := by
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
  set c := Classical.choose (Finset.exists_maximal h) with hc
  obtain ⟨-, hmax⟩ := Classical.choose_spec (Finset.exists_maximal h)
  have htri := Nat.lt_trichotomy (prof.menPref m w) (prof.menPref m c)
  rcases htri with (hlt | heq | hgt)
  · -- `choose` est préférée à `w` : `choose ≤ w`, donc `hmax` donne `w ≤ choose`
    have hle : c ≤ w := Or.inr hlt
    exact hmax hw hle
  · -- Préférence égale : l'injectivité donne `w = c`
    left
    exact (prof.menPref_bijective m).injective (Fin.ext heq)
  · -- `w` est préférée à `choose` : direct
    right
    exact hgt

end StableMarriage
