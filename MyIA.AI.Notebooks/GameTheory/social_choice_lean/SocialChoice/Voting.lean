/-
  Social Choice Theory - Voting Definitions
  ==========================================

  Port of chasenorman/Formalized-Voting to Lean 4
  Original: https://github.com/chasenorman/Formalized-Voting

  Adapted to our SocialChoice/Basic.lean framework:
  - Uses PrefOrder from Basic.lean instead of raw relations
  - Uses P (strict preference) and I (indifference) from Basic.lean
  - Compatible with Profile ι σ from Arrow.lean

  Key concepts:
  - Margin function for pairwise vote counting
  - Condorcet winner/loser and their criteria
  - Pareto efficiency and monotonicity for Social Choice Correspondences
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

import SocialChoice.Basic

namespace SocialChoice

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

/-! ## Margin Function -/

/-- The margin of x over y in a profile:
    |{voters strictly preferring x to y}| - |{voters strictly preferring y to x}|
    Positive margin means x beats y in pairwise comparison. -/
noncomputable def margin (prof : ι → PrefOrder σ) (x y : σ) : ℤ :=
  haveI : (i : ι) → Decidable (P (prof i).rel x y) := fun _ => Classical.dec _
  haveI : (i : ι) → Decidable (P (prof i).rel y x) := fun _ => Classical.dec _
  ((Finset.filter (fun i => P (prof i).rel x y) Finset.univ).card : ℤ) -
    ((Finset.filter (fun i => P (prof i).rel y x) Finset.univ).card : ℤ)

/-- Positive margin: x beats y in pairwise comparison -/
def margin_pos (prof : ι → PrefOrder σ) (x y : σ) : Prop :=
  0 < margin prof x y

/-! ## Condorcet Concepts -/

/-- A Condorcet winner: strictly beats every other alternative in pairwise comparison -/
def condorcet_winner (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, y ≠ x → margin_pos prof x y

/-- A Condorcet loser: strictly loses to every other alternative -/
def condorcet_loser (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ S.card ≥ 2 ∧ ∀ y ∈ S, y ≠ x → margin_pos prof y x

/-! ## Social Choice Correspondence -/

/-- A Social Choice Correspondence: maps profiles and alternative sets to chosen alternatives -/
def SCC (ι σ : Type*) [Fintype ι] [DecidableEq σ] :=
  (ι → PrefOrder σ) → Finset σ → Finset σ

/-! ## Voting Criteria -/

/-- Condorcet criterion: every Condorcet winner is selected -/
def condorcet_criterion (f : SCC ι σ) : Prop :=
  ∀ prof S x, condorcet_winner prof S x → x ∈ f prof S

/-- Condorcet loser criterion: no Condorcet loser is selected -/
def condorcet_loser_criterion (f : SCC ι σ) : Prop :=
  ∀ prof S x, condorcet_loser prof S x → x ∉ f prof S

/-- Pareto efficiency: if all voters prefer x to y, then y is not selected -/
def pareto_scc (f : SCC ι σ) : Prop :=
  ∀ prof S x y, x ∈ S → y ∈ S →
    (∀ i : ι, P (prof i).rel x y) → y ∉ f prof S

/-- Monotonicity: improving x's position preserves x's selection -/
def monotonicity (f : SCC ι σ) : Prop :=
  ∀ prof prof' S x,
    x ∈ f prof S → x ∈ S →
    (∀ i : ι, ∀ y ∈ S, P (prof i).rel x y → P (prof' i).rel x y) →
    (∀ i : ι, ∀ y ∈ S, ¬P (prof i).rel y x → ¬P (prof' i).rel y x) →
    x ∈ f prof' S

/-! ## Margin Properties -/

theorem margin_antisymm (prof : ι → PrefOrder σ) (x y : σ) :
    margin prof x y = - (margin prof y x) := by
  unfold margin
  ring

theorem margin_self (prof : ι → PrefOrder σ) (x : σ) :
    margin prof x x = 0 := by
  unfold margin
  haveI : (i : ι) → Decidable (P (prof i).rel x x) := fun _ => Classical.dec _
  have hN : ∀ i : ι, ¬P (prof i).rel x x := fun _ => false_of_P_self
  have h_empty : Finset.filter (fun i => P (prof i).rel x x) Finset.univ = ∅ := by
    ext i; simp [Finset.mem_filter]; exact fun hi => hN i hi
  simp

theorem margin_pos_iff_neg_rev (prof : ι → PrefOrder σ) {x y : σ} :
    margin_pos prof x y ↔ margin prof y x < 0 := by
  unfold margin_pos
  rw [margin_antisymm prof]
  omega

/-! ## Condorcet Properties -/

/-- The Condorcet winner is unique (when it exists) -/
theorem condorcet_winner_unique (prof : ι → PrefOrder σ) {S : Finset σ} {x y : σ}
    (hx : condorcet_winner prof S x) (hy : condorcet_winner prof S y) (hxy : x ≠ y) :
    False := by
  obtain ⟨hxs, hbeat⟩ := hx
  obtain ⟨hys, hbeat'⟩ := hy
  have h₁ := hbeat y hys hxy.symm
  have h₂ := hbeat' x hxs hxy
  unfold margin_pos at h₁ h₂
  have := margin_antisymm prof x y
  linarith

/-- A Condorcet winner cannot be a Condorcet loser -/
theorem condorcet_winner_not_loser (prof : ι → PrefOrder σ) {S : Finset σ} {x : σ}
    (hw : condorcet_winner prof S x) (hl : condorcet_loser prof S x) :
    False := by
  obtain ⟨hxs, hcard, hlose⟩ := hl
  obtain ⟨_, hbeat⟩ := hw
  obtain ⟨y, hyS, hxy⟩ := exists_second_distinct_mem (by omega : 2 ≤ S.card) hxs
  have h₁ := hbeat y hyS hxy
  have h₂ := hlose y hyS hxy
  unfold margin_pos at h₁ h₂
  have := margin_antisymm prof x y
  linarith

/-! ## Unanimity and Margin -/

/-- If all voters strictly prefer x to y, the margin is positive -/
theorem margin_pos_of_unanimous [Nonempty ι] (prof : ι → PrefOrder σ) {x y : σ}
    (h : ∀ i : ι, P (prof i).rel x y) : margin_pos prof x y := by
  unfold margin_pos
  -- Compute margin value: all voters prefer x to y, so margin = card ι > 0
  have hkey : margin prof x y = (Fintype.card ι : ℤ) := by
    unfold margin
    classical
    -- After classical, Decidable instances are uniform via Classical.dec
    -- The haveI in margin's definition and our context both resolve to Classical.dec
    have hNyx : ∀ i, ¬P (prof i).rel y x := fun i hi => (h i).2 hi.1
    have h_univ : (Finset.univ : Finset ι).filter (fun i => P (prof i).rel x y) = Finset.univ := by
      ext i; simp [Finset.mem_filter]; exact h i
    have h_empty : (Finset.univ : Finset ι).filter (fun i => P (prof i).rel y x) = ∅ := by
      ext i; simp [Finset.mem_filter]; exact fun hi => hNyx i hi
    simp [h_univ, h_empty, Finset.card_univ]
  rw [hkey]
  exact mod_cast (Finset.card_pos.mpr Finset.univ_nonempty)

end SocialChoice
