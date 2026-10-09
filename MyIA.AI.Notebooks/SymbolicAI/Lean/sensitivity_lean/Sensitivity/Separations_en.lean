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

Block sensitivity follows the **standard definition** (Nisan–Szegedy): the
**maximum, over families of nonempty, sensitive, pairwise disjoint blocks, of
the cardinal of the family** — not the count of all sensitive blocks. The
witness `or3_blockSensitivity` executes the difference: for OR on three
coordinates at the zero vertex, all seven nonempty blocks are sensitive
(`or3_sensitive_blocks_card`), yet the block sensitivity is **3** — the three
singletons — and never exceeds the dimension (`blockSensitivity_le`).

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

/-- Local block sensitivity of `F` at `x` — **standard definition**
(Nisan–Szegedy): the **maximum number of pairwise disjoint sensitive blocks**,
that is, the maximal cardinal of a family of **nonempty** blocks whose
simultaneous flip changes the value of `F`, and whose two distinct members
always have empty intersection.

This is **not** the count of all sensitive blocks: at the zero vertex of `or3`,
all seven nonempty blocks are sensitive, yet the standard value is 3 — the
three singletons (`or3_blockSensitivity`). Disjointness bounds the quantity by
the dimension (`blockSensitivity_le`), where a raw count of sensitive blocks
would reach up to `2 ^ n - 1`. The empty family is admissible (with cardinal
zero), so the maximum always exists and is at least `0`. -/
def blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) : ℕ :=
  (Finset.univ.filter fun 𝓑 : Finset (Finset (Fin n)) =>
      (∀ B ∈ 𝓑, B.Nonempty ∧ F (flipBlock x B) ≠ F x) ∧
      (∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin n)) = ∅)).sup
    Finset.card

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

/-- **Block sensitivity is bounded by the dimension**: the blocks of an
admissible family are nonempty and pairwise disjoint, so the map "smallest
element of a block" is injective on the family, whose cardinal therefore cannot
exceed `n`. A raw count of sensitive blocks would reach up to `2 ^ n - 1`. -/
theorem blockSensitivity_le {n : ℕ} (F : Q n → Bool) (x : Q n) :
    blockSensitivity F x ≤ n := by
  classical
  refine Finset.sup_le ?_
  intro 𝓑 h𝓑
  have hmem : ∀ B ∈ 𝓑, B.Nonempty := fun B hB =>
    ((Finset.mem_filter.1 h𝓑).2.1 B hB).1
  have hdisj : ∀ B₁ ∈ 𝓑, ∀ B₂ ∈ 𝓑, B₁ ≠ B₂ → (B₁ ∩ B₂ : Finset (Fin n)) = ∅ :=
    fun B₁ hB₁ B₂ hB₂ hne => (Finset.mem_filter.1 h𝓑).2.2 B₁ hB₁ B₂ hB₂ hne
  have hinj : Set.InjOn (fun p : {B : Finset (Fin n) // B ∈ 𝓑} =>
      p.1.min' (hmem p.1 p.2)) (↑𝓑.attach : Set {B : Finset (Fin n) // B ∈ 𝓑}) := by
    intro p _ q _ hpq
    by_contra hpne
    have hBne : p.1 ≠ q.1 := fun h => hpne (Subtype.ext h)
    have hp : p.1.min' (hmem p.1 p.2) ∈ p.1 := Finset.min'_mem _ _
    have hq : q.1.min' (hmem q.1 q.2) ∈ q.1 := Finset.min'_mem _ _
    have hboth : p.1.min' (hmem p.1 p.2) ∈ q.1 := by
      rw [show p.1.min' (hmem p.1 p.2) = q.1.min' (hmem q.1 q.2) from hpq]
      exact hq
    have hinter : p.1.min' (hmem p.1 p.2) ∈ (p.1 ∩ q.1 : Finset (Fin n)) :=
      Finset.mem_inter.2 ⟨hp, hboth⟩
    rw [hdisj p.1 p.2 q.1 q.2 hBne] at hinter
    simp at hinter
  calc 𝓑.card = 𝓑.attach.card := Finset.card_attach.symm
    _ = (𝓑.attach.image
          fun p : {B : Finset (Fin n) // B ∈ 𝓑} => p.1.min' (hmem p.1 p.2)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

/-!
### The fundamental inequality: singletons form a disjoint family
-/

/-- `sensitivity ≤ blockSensitivity`: the singletons of the sensitive
coordinates form an admissible family — distinct singletons have empty
intersection — so their cardinal, which is that of the sensitive coordinates,
is a lower bound for the maximum. This is the trivial direction of the gap
between the two quantities; the sensitivity conjecture (solved by Huang)
concerns the reverse direction. -/
theorem sensitivity_le_blockSensitivity {n : ℕ} (F : Q n → Bool) (x : Q n) :
    sensitivity F x ≤ blockSensitivity F x := by
  classical
  have hfam : ∀ B ∈ (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n)), B.Nonempty ∧ F (flipBlock x B) ≠ F x := by
    intro B hB
    simp only [Finset.mem_image] at hB
    obtain ⟨i, hi, rfl⟩ := hB
    exact ⟨Finset.singleton_nonempty i, by
      rw [flipBlock_singleton]; exact (Finset.mem_filter.1 hi).2⟩
  have hpair : ∀ B₁ ∈ (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
      fun i => ({i} : Finset (Fin n)), ∀ B₂ ∈
      (Finset.univ.filter fun i => F (flip x i) ≠ F x).image
        fun i => ({i} : Finset (Fin n)), B₁ ≠ B₂ →
      (B₁ ∩ B₂ : Finset (Fin n)) = ∅ := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [Finset.mem_image] at hB₁ hB₂
    obtain ⟨i, -, rfl⟩ := hB₁
    obtain ⟨j, -, rfl⟩ := hB₂
    have hij : i ≠ j := fun h => hne (Finset.singleton_inj.2 h)
    ext a
    simp only [Finset.mem_inter, Finset.mem_singleton]
    constructor
    · intro h
      exact absurd (h.1.symm.trans h.2) hij
    · intro h
      simp at h
  have hinj : Set.InjOn (fun i => ({i} : Finset (Fin n)))
      (↑(Finset.univ.filter fun i => F (flip x i) ≠ F x) : Set (Fin n)) := by
    intro a _ b _ hab
    exact Finset.singleton_inj.1 hab
  calc sensitivity F x
      = ((Finset.univ.filter fun i => F (flip x i) ≠ F x).image
          fun i => ({i} : Finset (Fin n))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ blockSensitivity F x := by
        refine Finset.le_sup ?_
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩

/-!
### An explicit strict separation in dimension 4

The disjunction of two conjunctions `(x₀ ∧ x₁) ∨ (x₂ ∧ x₃)` has, at the zero
vertex, **zero** sensitivity (no single-coordinate flip turns it on) but
**nonzero** block sensitivity (flipping the block `{0, 1}` turns it on). Block
sensitivity can therefore strictly exceed sensitivity — as early as dimension
4, on an example computable end to end.
-/

/-- Explicit dimension-4 example: disjunction of two conjunctions. -/
def orOfAnds (x : Q 4) : Bool := (x 0 && x 1) || (x 2 && x 3)

/-- At the zero vertex, no single coordinate changes the value of `orOfAnds`:
the local sensitivity there is **zero**. -/
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

/-- Flipping the block `{0, 1}` at the zero vertex turns `orOfAnds` on: the
singleton family `{{0, 1}}` is admissible, so the local block sensitivity
there is **nonzero**. -/
theorem orOfAnds_blockSensitivity_pos :
    0 < blockSensitivity orOfAnds (fun _ => false) := by
  classical
  have hval : orOfAnds (flipBlock (fun _ => false) ({0, 1} : Finset (Fin 4))) = true := by
    simp [orOfAnds, flipBlock]
  have hfalse : orOfAnds (fun _ => false) = false := by simp [orOfAnds]
  have hfam : ∀ B ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))),
      B.Nonempty ∧ orOfAnds (flipBlock (fun _ => false) B) ≠ orOfAnds (fun _ => false) := by
    intro B hB
    simp only [Finset.mem_singleton] at hB
    subst hB
    exact ⟨⟨0, by simp⟩, by simp [hval, hfalse]⟩
  have hpair : ∀ B₁ ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))),
      ∀ B₂ ∈ ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))), B₁ ≠ B₂ →
      (B₁ ∩ B₂ : Finset (Fin 4)) = ∅ := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [Finset.mem_singleton] at hB₁ hB₂
    rw [hB₁, hB₂] at hne
    exact absurd rfl hne
  have hone : ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).card ≤
      blockSensitivity orOfAnds (fun _ => false) := by
    refine Finset.le_sup ?_
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩
  have h1 : ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).card = 1 := by simp
  rw [h1] at hone
  exact hone

/-- **Strict separation**: `sensitivity < blockSensitivity`, achieved by the
`orOfAnds` example in dimension 4. -/
theorem orOfAnds_strict_separation :
    sensitivity orOfAnds (fun _ => false) < blockSensitivity orOfAnds (fun _ => false) := by
  rw [orOfAnds_sensitivity_zero]
  exact orOfAnds_blockSensitivity_pos

/-!
### The OR₃ witness: three, not seven

At the zero vertex of OR₃, **all** nonempty blocks are sensitive — there are
seven of them. A definition that counted sensitive blocks would therefore read
7; the standard definition reads **3**, the maximal cardinal of a disjoint
family (the three singletons), bounded by the dimension. This is the witness
that distinguishes the two readings of the definition.
-/

/-- OR on the three coordinates of `Q 3`. -/
def or3 (x : Q 3) : Bool := x 0 || x 1 || x 2

/-- At the zero vertex, the **seven** nonempty blocks of `Fin 3` are all
sensitive for `or3`: this is the count a definition enumerating sensitive
blocks would read. -/
theorem or3_sensitive_blocks_card :
    (Finset.univ.filter fun S : Finset (Fin 3) =>
       S.Nonempty ∧ or3 (flipBlock (fun _ => false) S) ≠ or3 (fun _ => false)).card = 7 := by
  decide

/-- **Witness of the standard definition**: the block sensitivity of `or3` at
the zero vertex is **3**, not 7, although all seven nonempty blocks are
sensitive (`or3_sensitive_blocks_card`). The upper bound comes from the
dimension (`blockSensitivity_le`); the lower bound, from the admissible family
of the three singletons. -/
theorem or3_blockSensitivity :
    blockSensitivity or3 (fun _ => false) = 3 := by
  apply Nat.le_antisymm ?_ ?_
  · exact blockSensitivity_le or3 (fun _ => false)
  · have hzero : or3 (fun _ => false) = false := by simp [or3]
    have hsens : ∀ i : Fin 3, or3 (flip (fun _ => false) i) = true := by
      intro i
      fin_cases i <;> simp [or3, flip]
    have hfam : ∀ B ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)),
        B.Nonempty ∧ or3 (flipBlock (fun _ => false) B) ≠ or3 (fun _ => false) := by
      intro B hB
      simp only [Finset.mem_image] at hB
      obtain ⟨i, -, rfl⟩ := hB
      exact ⟨Finset.singleton_nonempty i, by simp [flipBlock_singleton, hsens i, hzero]⟩
    have hpair : ∀ B₁ ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)), ∀ B₂ ∈ (Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3)), B₁ ≠ B₂ →
        (B₁ ∩ B₂ : Finset (Fin 3)) = ∅ := by
      intro B₁ hB₁ B₂ hB₂ hne
      simp only [Finset.mem_image] at hB₁ hB₂
      obtain ⟨i, -, rfl⟩ := hB₁
      obtain ⟨j, -, rfl⟩ := hB₂
      have hij : i ≠ j := fun h => hne (Finset.singleton_inj.2 h)
      ext a
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · intro h
        exact absurd (h.1.symm.trans h.2) hij
      · intro h
        simp at h
    have hcard : ((Finset.univ : Finset (Fin 3)).image
        fun i => ({i} : Finset (Fin 3))).card = 3 := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro a _ b _ hab
        exact Finset.singleton_inj.1 hab
    calc 3 = ((Finset.univ : Finset (Fin 3)).image
          fun i => ({i} : Finset (Fin 3))).card := hcard.symm
      _ ≤ blockSensitivity or3 (fun _ => false) := by
          refine Finset.le_sup ?_
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hfam, hpair⟩⟩

end Sensitivity_en
