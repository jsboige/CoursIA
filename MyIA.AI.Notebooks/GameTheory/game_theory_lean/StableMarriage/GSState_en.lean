/-
  Stable Marriage - Gale-Shapley Algorithm State
  ==============================================

  English mirror of `StableMarriage/GSState.lean` (FR-first canonical).
  Intermediate state for the Gale-Shapley deferred acceptance algorithm.
  Uses a partial matching based on `Option` while the algorithm runs,
  converted into a total bijective matching at termination.

  i18n convention (cf #4980): headers, sections, docstrings and intra-proof
  comments are in English in this mirror; Lean symbol names, lemma statements
  and tactics are preserved in English (Mathlib compatibility).
  Convention observed: intra-lake imports stay on the FR canonical files.
  Not a destructive translation: manual translation FR-first-from-origin
  (no pre-Option A EN history for this file); Lean tactic code
  byte-identical, preserved verbatim; prose translated. Same pattern as
  c.238.2/#5362 (RepeatedGames), c.238.3/#5363 (Minimax), c.238.4/#5419 (Shapley).

  Adapté de / Adapted from: https://github.com/mmaaz-git/stable-marriage-lean (v4.25.0)

  See #4980. Part of #4208 (axe E).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Preorder.Finite
import StableMarriage.Definitions_en

namespace StableMarriage_en


open Function Finset Classical
open StableMarriage_en

variable {n : Nat} [NeZero n]

/-- Partial matching during the execution of the GS algorithm. -/
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

/-- Extracted transitivity proof for `gsMenPrefLE prof m` as a reusable instance
    (see #6140). Before extraction, the same `cases hab with ... | inr cases
    hbc with ...` proof was inlined 3 times (`gsChooseMax` / `gsChooseMax_mem`
    / `gsChooseMax_maximal`), forcing Lean to re-elaborate the same syntactic
    tree 3 times — Windows stack exhaustion during cold `lake -R build`
    (`0xC0000409` STATUS_STACK_BUFFER_OVERRUN in `lean.exe` on ai-01 §1
    pre-merge). The EN sibling owns its own byte-identical copy of this lemma
    (same extraction as FR canonical); the 3 `haveI := gsMenPref_trans prof m`
    sites reference it unqualified, mirroring the FR canonical self-reference. -/
lemma gsMenPref_trans (m : Fin n) : IsTrans (Fin n) (gsMenPrefLE prof m) :=
  ⟨fun a b c hab hbc => by
    cases hab with
    | inl hab => subst hab; exact hbc
    | inr hab =>
      cases hbc with
      | inl hbc => subst hbc; exact Or.inr hab
      | inr hbc => exact Or.inr (lt_trans hbc hab)⟩

/-- Best-ranked candidate among those `m` has not proposed to yet, chosen
    via `Finset.exists_maximal` under the custom order `gsMenPrefLE`.
    Subtlety (recorded in the prover traces, `agent_tests/prover/`):
    `Finset.exists_maximal` only yields **conditional** maximality
    (`∀ y ∈ s, x ≤ y → y ≤ x`), not `∀ y ∈ s, y ≤ x` — bridging to absolute
    maximality goes through trichotomy on the underlying `Nat` preference,
    see `gsChooseMax_maximal`. -/
noncomputable def gsChooseMax (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) : Fin n :=
  letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩
  haveI := gsMenPref_trans prof m
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

-- These definitions use the explicit `prof` parameter to avoid duplicating
-- the section variables.
noncomputable def gsRunSteps (prof : PrefProfile n) (k : Nat) : GSState prof :=
  match k with
  | 0 => gsInitial prof
  | k' + 1 => gsStep prof (gsRunSteps prof k')

def gsProposalBound (n : Nat) [NeZero n] : Nat := n * n

noncomputable def gsGaleShapley (prof : PrefProfile n) : GSMatching n :=
  (gsRunSteps prof (gsProposalBound n)).matching

/-! ## Auxiliary lemmas for `gsChooseMax` -/

/-- The chosen maximal candidate belongs to the set of candidates. -/
lemma gsChooseMax_mem (prof : PrefProfile n) (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) :
    gsChooseMax prof σ m h ∈ gsCandidates prof σ m := by
  unfold gsChooseMax
  letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩
  haveI := gsMenPref_trans prof m
  obtain ⟨hmem, -⟩ := Classical.choose_spec (Finset.exists_maximal h)
  exact hmem

/-- No unproposed candidate is preferred over the chosen maximal candidate.
    Closure by **trichotomy** (`Nat.lt_trichotomy`) on the underlying `Nat`
    preference: this is exactly the closure hint (`closure_hint`) recorded
    for this goal in the prover traces (`partial_progress` of
    `stable_marriage`), materialised here. -/
lemma gsChooseMax_maximal (prof : PrefProfile n) (σ : GSState prof) (m : Fin n)
    (h : (gsCandidates prof σ m).Nonempty) (w : Fin n)
    (hw : w ∈ gsCandidates prof σ m) :
    gsMenPrefLE prof m w (gsChooseMax prof σ m h) := by
  unfold gsChooseMax
  letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩
  haveI := gsMenPref_trans prof m
  set c := Classical.choose (Finset.exists_maximal h) with hc
  obtain ⟨-, hmax⟩ := Classical.choose_spec (Finset.exists_maximal h)
  have htri := Nat.lt_trichotomy (prof.menPref m w) (prof.menPref m c)
  rcases htri with (hlt | heq | hgt)
  · -- `choose` is preferred to `w`: `choose ≤ w`, hence `hmax` gives `w ≤ choose`
    have hle : c ≤ w := Or.inr hlt
    exact hmax hw hle
  · -- Equal preference: injectivity gives `w = c`
    left
    exact (prof.menPref_bijective m).injective (Fin.ext heq)
  · -- `w` is preferred to `choose`: direct
    right
    exact hgt

end StableMarriage_en
