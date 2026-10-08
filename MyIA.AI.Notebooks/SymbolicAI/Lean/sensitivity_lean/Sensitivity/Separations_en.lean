import Sensitivity.Fourier_en
import Mathlib.Tactic.FinCases

/-!
# Sensitivity and block sensitivity: definitions and first separations

This file is an **additive** contribution to the `sensitivity_lean` lake
(Origami Epic #19898, fold 2, sub-grain #19908): it modifies no existing
statement of Huang's theorem. It defines the local sensitivity and local block
sensitivity of a Boolean function `F` on the hypercube `Q n`, establishes the
fundamental inequality `sensitivity ≤ blockSensitivity`, and produces an
**explicit strict separation** in dimension 4: the disjunction of two
conjunctions has a vertex with zero sensitivity but nonzero block sensitivity.

The quantities here are *local* (at a vertex `x`): this is the fine grain of
the literature (Nisan, Huang), and the substrate on which the
`ANALYSE-06-Sensibilite-2026` notebook builds the global variants.
-/

namespace Sensitivity_en

open Bool Finset Fintype

/-- Local sensitivity of `F` at `x`: the number of coordinates whose
(single-coordinate) flip changes the value of `F`. -/
def sensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun i => F (flip x i) ≠ F x).card

/-- Simultaneous flip of a **block** `S` of coordinates of `x`. -/
def flipBlock {n : ℕ} (x : Q n) (S : Finset (Fin n)) : Q n :=
  fun j => if j ∈ S then !(x j) else x j

/-- Local block sensitivity of `F` at `x`: the number of **nonempty** blocks of
coordinates whose simultaneous flip changes the value of `F`. The empty block
is excluded: it leaves `x` unchanged and would count for nothing. -/
def blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card

/-!
### Computation lemmas for `flipBlock`
-/

@[simp] lemma flipBlock_empty {n : ℕ} (x : Q n) : flipBlock x ∅ = x := by
  funext j
  simp [flipBlock]

/-- Flipping the singleton `{i}` is the same as flipping one coordinate. -/
lemma flipBlock_singleton {n : ℕ} (x : Q n) (i : Fin n) :
    flipBlock x {i} = flip x i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipBlock]
  · simp only [flipBlock, Finset.mem_singleton, if_neg h]
    exact (flip_apply_ne x i h).symm

/-!
### Trivial bounds
-/

/-- Local sensitivity is bounded by the dimension. -/
theorem sensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) : sensitivity F x ≤ n := by
  simp only [sensitivity]
  calc (Finset.univ.filter fun i => F (flip x i) ≠ F x).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Local block sensitivity is bounded by the number of blocks, `2 ^ n`. -/
theorem blockSensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) :
    blockSensitivity F x ≤ 2 ^ n := by
  simp only [blockSensitivity]
  calc (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card
      ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

/-!
### The fundamental inequality: every singleton is a block
-/

/-- `sensitivity ≤ blockSensitivity`: singletons are nonempty blocks, so every
sensitive neighbor is in particular a sensitive block. This is the trivial
direction of the gap between the two quantities; the sensitivity conjecture
(resolved by Huang) concerns the reverse direction. -/
theorem sensitivity_le_blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) :
    sensitivity F x ≤ blockSensitivity F x := by
  classical
  have hsub : ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n))) ⊆
      Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x := by
    intro S hS
    simp only [Finset.mem_image] at hS
    obtain ⟨i, hi, rfl⟩ := hS
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and] at hi ⊢
    exact ⟨Finset.singleton_nonempty i, by rw [flipBlock_singleton]; exact hi⟩
  have hinj : Set.InjOn (fun i => ({i} : Finset (Fin n)))
      (↑(Finset.univ.filter fun i => F (flip x i) ≠ F x) : Set (Fin n)) := by
    intro a _ b _ hab
    exact Finset.singleton_inj.1 hab
  simp only [sensitivity, blockSensitivity]
  calc (Finset.univ.filter fun i => F (flip x i) ≠ F x).card
      = ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
          fun i => ({i} : Finset (Fin n))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ.filter fun S : Finset (Fin n) => S.Nonempty ∧ F (flipBlock x S) ≠ F x).card :=
        Finset.card_le_card hsub

/-!
### An explicit strict separation in dimension 4

The disjunction of two conjunctions `(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)` has, at the
all-zero vertex, **zero** sensitivity (no single-coordinate flip turns it on)
but **nonzero** block sensitivity (flipping the block `{0, 1}` turns it on).
Block sensitivity can therefore strictly exceed sensitivity — as early as
dimension 4, on an example computable end to end.
-/

/-- Explicit dimension-4 example: a disjunction of two conjunctions. -/
def orOfAnds (x : Q 4) : Bool := (x 0 && x 1) || (x 2 && x 3)

/-- At the all-zero vertex, no single coordinate changes the value of
`orOfAnds`: the local sensitivity there is **zero**. -/
theorem orOfAnds_sensitivity_zero :
    sensitivity orOfAnds (fun _ => false) = 0 := by
  classical
  have key : ∀ i : Fin 4, orOfAnds (flip (fun _ => false) i) = false := by
    intro i
    fin_cases i <;> simp [orOfAnds, flip]
  have hset : (Finset.univ.filter
      fun i => orOfAnds (flip (fun _ => false) i) ≠ orOfAnds (fun _ => false)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _ h
    have h0 : orOfAnds (fun _ => false) = false := by simp [orOfAnds]
    rw [key i, h0] at h
    exact absurd rfl h
  simp only [sensitivity, hset, Finset.card_empty]

/-- Flipping the block `{0, 1}` at the all-zero vertex turns `orOfAnds` on:
the local block sensitivity there is **nonzero**. -/
theorem orOfAnds_blockSensitivity_pos :
    0 < blockSensitivity orOfAnds (fun _ => false) := by
  classical
  have hval : orOfAnds (flipBlock (fun _ => false) ({0, 1} : Finset (Fin 4))) = true := by
    simp [orOfAnds, flipBlock]
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ Finset.univ.filter
      fun S : Finset (Fin 4) => S.Nonempty ∧
        orOfAnds (flipBlock (fun _ => false) S) ≠ orOfAnds (fun _ => false) := by
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and]
    refine ⟨⟨0, by simp⟩, ?_⟩
    rw [hval]
    simp [orOfAnds]
  simp only [blockSensitivity]
  exact Finset.card_pos.2 ⟨_, hmem⟩

/-- **Strict separation**: `sensitivity < blockSensitivity`, achieved by the
`orOfAnds` example in dimension 4. -/
theorem orOfAnds_strict_separation :
    sensitivity orOfAnds (fun _ => false) < blockSensitivity orOfAnds (fun _ => false) := by
  rw [orOfAnds_sensitivity_zero]
  exact orOfAnds_blockSensitivity_pos

end Sensitivity_en
