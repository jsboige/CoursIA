-- ============================================================
-- AUTO-COPIED SNAPSHOT -- DO NOT EDIT HERE
-- Source: MyIA.AI.Notebooks/SymbolicAI/Lean/stable_marriage_lean/StableMarriage/
--   Definitions.lean + GSState.lean (concatenated)
-- Purpose: reference material for the multi-agent Lean prover (issue #1081 Part 2).
--   The prover agents read this to ground their guidance in the actual ported
--   definitions instead of starting blind. Regenerate by re-copying the source
--   files when they change. This file is NOT part of any Lake build.
-- ============================================================

-- ===== Definitions.lean =====

/-
  Stable Marriage - Definitions
  ==============================

  Core types and definitions for the stable marriage problem.
  We model n men and n women (both as Fin n), each with strict preference
  rankings over the opposite set.

  A matching is a bijection between men and women.
  A matching is stable iff no blocking pair exists.
-/

import Mathlib.Data.Finset.Basic

namespace StableMarriage

open Finset Function

variable {n : Nat} [NeZero n]

/-- A man is identified by Fin n -/
abbrev Man (n : Nat) := Fin n

/-- A woman is identified by Fin n -/
abbrev Woman (n : Nat) := Fin n

/--
A preference ordering for a person over the opposite set.
Represented as a function mapping each candidate to a rank (lower = preferred).
Strict preference means the ranking function is injective.
-/
structure PrefProfile (n : Nat) [NeZero n] where
  /-- Men's preferences: each man ranks all women -/
  menPref : Fin n → Fin n → Fin n
  /-- Women's preferences: each woman ranks all men -/
  womenPref : Fin n → Fin n → Fin n
  /-- Each man's ranking is a permutation (bijective) -/
  menPref_bijective : ∀ m, Bijective (menPref m)
  /-- Each woman's ranking is a permutation (bijective) -/
  womenPref_bijective : ∀ w, Bijective (womenPref w)

namespace PrefProfile

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/--
Man `m` prefers woman `w1` over woman `w2` iff w1 has a lower rank.
Since menPref m is a bijection Fin n → Fin n, lower = more preferred.
-/
def manPrefers (m : Fin n) (w1 w2 : Fin n) : Bool :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` prefers man `m1` over man `m2` iff m1 has a lower rank.
-/
def womanPrefers (w : Fin n) (m1 m2 : Fin n) : Bool :=
  prof.womenPref w m1 < prof.womenPref w m2

/--
Man `m` strictly prefers woman `w1` to woman `w2`.
Prop-valued version for theorem statements.
-/
def ManPrefers (m : Fin n) (w1 w2 : Fin n) : Prop :=
  prof.menPref m w1 < prof.menPref m w2

/--
Woman `w` strictly prefers man `m1` to man `m2`.
-/
def WomanPrefers (w : Fin n) (m1 m2 : Fin n) : Prop :=
  prof.womenPref w m1 < prof.womenPref w m2

end PrefProfile

/--
A matching is a bijection from men to women (perfect matching).
-/
structure Matching (n : Nat) [NeZero n] where
  /-- Map each man to his matched woman -/
  spouse : Fin n → Fin n
  /-- The matching is bijective (each woman matched to exactly one man) -/
  bijective : Bijective spouse

namespace Matching

variable {n : Nat} [NeZero n] (μ : Matching n)

/-- Get the inverse: which man is matched to woman w -/
noncomputable def inverse (w : Fin n) : Fin n :=
  (Equiv.ofBijective μ.spouse μ.bijective).symm w

end Matching

/--
A blocking pair for matching μ under preference profile prof:
a man m and woman w who both prefer each other to their current partners.
-/
def IsBlockingPair (prof : PrefProfile n) (μ : Matching n)
    (m : Fin n) (w : Fin n) : Prop :=
  prof.ManPrefers m w (μ.spouse m) ∧
  prof.WomanPrefers w m (μ.inverse w)

/--
A matching is stable iff no blocking pair exists.
-/
def IsStable (prof : PrefProfile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair prof μ m w

/--
A matching is man-optimal iff every man gets their best possible partner
among all stable matchings.
-/
def IsManOptimal (prof : PrefProfile n) (μ : Matching n) : Prop :=
  IsStable prof μ ∧
  ∀ μ' : Matching n, IsStable prof μ' →
    ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (μ'.spouse m)

end StableMarriage


-- ===== GSState.lean =====

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
  · -- choose preferred over w: choose ≤ w, so hmax gives w ≤ choose
    have hle : c ≤ w := Or.inr hlt
    exact hmax hw hle
  · -- equal preference: injectivity gives w = c
    left
    exact (prof.menPref_bijective m).injective (Fin.ext heq)
  · -- w preferred over choose: direct
    right
    exact hgt

end StableMarriage
