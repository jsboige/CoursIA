/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Canonical grid forms — the `sortDedup` specification (Conway's Game of Life)

English mirror of `GridCanonical.lean` (FR canonical). Convention EPIC #4980
(decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
files — no inline bilingual block in a single file (Option B rejected). The module
docstring and the theorem docstrings below differ from the FR version; the body
signatures, proofs and tactics remain byte-identical between the two files.

This file is the **canonical-grid-form** leaf of the `conway_lean` lake, sibling-paired
with `GridCanonical.lean` (FR canonical) per EPIC #4980 Option A. The module proves that
`sortDedup` outputs are **canonical** (lex-sorted and duplicate-free) and that canonical
lists are **rigid** — exactly the bridge that turns the list-equality goals of the
Hashlife correctness theorems (`HashlifeCorrectness.lean`, P4/P5) into pointwise
membership goals, where the actual combinatorics of the B3/S23 rule and the macrocell
recursion can be argued cell by cell. The level-2 namespace `Conway > Life` is mirrored
as `Conway_en > Life_en` (level-2 sibling pattern, see `LightCone_en.lean` c.421).
-/

import Conway.Life

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## The lexicographic comparator: order axioms -/

/-- `lexLt` in terms of linear integer arithmetic. -/
theorem lexLt_iff {a b : Int × Int} :
    lexLt a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold lexLt
  split_ifs <;> simp <;> omega

/-- `lexLe` in terms of linear integer arithmetic. -/
theorem lexLe_iff {a b : Int × Int} :
    lexLe a b = true ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2) := by
  simp only [lexLe, Bool.or_eq_true, lexLt_iff, beq_iff_eq, Prod.ext_iff]
  omega

/-- `lexLe` is total — the hypothesis `List.pairwise_insertionSort` needs. -/
theorem lexLe_total (a b : Int × Int) : (lexLe a b || lexLe b a) = true := by
  simp only [Bool.or_eq_true, lexLe_iff]
  omega

/-- `lexLe` is transitive. -/
theorem lexLe_trans (a b c : Int × Int)
    (hab : lexLe a b = true) (hbc : lexLe b c = true) : lexLe a c = true := by
  simp only [lexLe_iff] at *
  omega

/-- `lexLe` is antisymmetric — what makes sorted Nodup lists rigid. -/
theorem lexLe_antisymm (a b : Int × Int)
    (hab : lexLe a b = true) (hba : lexLe b a = true) : a = b := by
  simp only [lexLe_iff] at hab hba
  rw [Prod.ext_iff]
  omega

/-- Typeclass instances for `lexLe`, so that `List.pairwise_insertionSort`
    (which requires `[Std.Total r] [IsTrans α r]`) synthesizes automatically. -/
instance lexLe.isTrans : IsTrans (Int × Int) fun a b => lexLe a b = true :=
  ⟨fun _ _ _ hab hbc => lexLe_trans _ _ _ hab hbc⟩

instance lexLe.isTotal : Std.Total fun a b : Int × Int => lexLe a b = true :=
  ⟨fun a b => by
    have h : (lexLe a b || lexLe b a) = true := lexLe_total a b
    rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at h
    exact h⟩

/-! ## Canonical grids -/

/-- A grid in canonical form: lexicographically sorted and duplicate-free.
    Invariant of every `sortDedup` image, preserved by `filter`. -/
def Canonical (g : Grid) : Prop :=
  g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup

/-- `sortDedup` always produces a canonical grid: sortedness comes from
    `pairwise_insertionSort` (using totality and transitivity of `lexLe`) and
    survives `dedup` because `dedup` yields a sublist; freedom from
    duplicates is `nodup_dedup`.

    `insertionSort` (not `mergeSort`) is used in `sortDedup` because the
    kernel reducer can evaluate `List.insertionSort` under `decide` whereas
    `List.mergeSort` stays stuck (measured po-2026 c.786). The Mathlib lemma
    `List.pairwise_insertionSort` is typeclass-based (`[Std.Total r]`
    `[IsTrans α r]`); we discharge those instances locally from
    `lexLe_total` and `lexLe_trans`. -/
theorem canonical_sortDedup (l : List (Int × Int)) : Canonical (sortDedup l) := by
  unfold sortDedup
  have hsort : List.Pairwise (fun a b => lexLe a b = true)
      (List.insertionSort (fun a b => lexLe a b = true) l) :=
    List.pairwise_insertionSort _ l
  exact ⟨hsort.sublist (List.dedup_sublist _), List.nodup_dedup _⟩

/-- Filtering preserves canonical form (`filter` yields a sublist). -/
theorem Canonical.filter {g : Grid} (h : Canonical g) (q : (Int × Int) → Bool) :
    Canonical (g.filter q) :=
  ⟨List.Pairwise.sublist List.filter_sublist h.1,
   List.Nodup.sublist List.filter_sublist h.2⟩

/-- **Rigidity of canonical grids**: two canonical grids with the same
    members are equal as lists. Same-membership gives a permutation
    (`perm_ext_iff_of_nodup`), and a permutation between two lex-sorted
    lists is the identity by antisymmetry (`Perm.eq_of_pairwise`). -/
theorem Canonical.ext {g₁ g₂ : Grid} (h₁ : Canonical g₁) (h₂ : Canonical g₂)
    (h : ∀ p, p ∈ g₁ ↔ p ∈ g₂) : g₁ = g₂ :=
  List.Perm.eq_of_pairwise (fun a b _ _ hab hba => lexLe_antisymm a b hab hba)
    h₁.1 h₂.1 ((List.perm_ext_iff_of_nodup h₁.2 h₂.2).mpr h)

/-- The workhorse corollary: two `sortDedup` images are equal **iff** their
    input lists have the same members. List equality of canonical grids is
    exactly set equality. -/
theorem sortDedup_eq_sortDedup_iff {l₁ l₂ : List (Int × Int)} :
    sortDedup l₁ = sortDedup l₂ ↔ ∀ p, p ∈ l₁ ↔ p ∈ l₂ := by
  constructor
  · intro h p
    rw [← mem_sortDedup (l := l₁), h, mem_sortDedup]
  · intro h
    exact Canonical.ext (canonical_sortDedup _) (canonical_sortDedup _)
      (fun p => by rw [mem_sortDedup, mem_sortDedup]; exact h p)

/-! ## Canonicity of the Life-engine grids -/

/-- `step` produces canonical grids. -/
theorem canonical_step (g : Grid) : Canonical (step g) :=
  canonical_sortDedup _

/-- `evolve n` produces canonical grids for `n ≥ 1` (for `n = 0` the
    output is the input, which need not be canonical). -/
theorem canonical_evolve_of_pos {n : Nat} (hn : 0 < n) (g : Grid) :
    Canonical (evolve n g) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [evolve_succ]
  exact canonical_step _

/-- `shift` produces canonical grids. -/
theorem canonical_shift (v : Int × Int) (g : Grid) : Canonical (shift v g) :=
  canonical_sortDedup _

/-! ## Translation-invariance of the local rule (B3/S23)

These lemmas establish that Conway's rule (birth `B3` / survival `S23`) is
translation-invariant: shifting the grid by vector `v` amounts to shifting the
query point by `-v`. First sorry-free link of the translation-invariance chain
(`isAlive_shift` → ... → `evolve_shift`) needed by path (A) of #6724: reduce the
`p4_nw_g3_bridge` to a named overlap wall by aligning points `p ↔ p'` before
applying `evolve_cone_agree` (which concludes only at a common point). -/

/-- Cell liveness is translation-invariant:
    `isAlive (shift v g) p = isAlive g (p.1 - v.1, p.2 - v.2)`. -/
theorem isAlive_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    isAlive (shift v g) p = isAlive g (p.1 - v.1, p.2 - v.2) := by
  simp [shift, isAlive, List.mem_map, mem_sortDedup]
  constructor
  · rintro ⟨a, b, hg, hp⟩
    have hp' : a + v.1 = p.1 ∧ b + v.2 = p.2 := Prod.ext_iff.mp hp
    have heq : (a, b) = (p.1 - v.1, p.2 - v.2) := by rw [Prod.ext_iff]; omega
    rw [← heq]; exact hg
  · intro h
    refine ⟨p.1 - v.1, p.2 - v.2, h, ?_⟩
    rw [Prod.ext_iff]; omega

/-- Live-neighbour count is translation-invariant. -/
theorem liveNeighborCount_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    liveNeighborCount (shift v g) p = liveNeighborCount g (p.1 - v.1, p.2 - v.2) := by
  simp only [liveNeighborCount]
  have hL : mooreNeighbors (p.1 - v.1, p.2 - v.2) =
            (mooreNeighbors p).map (fun q => (q.1 - v.1, q.2 - v.2)) := by
    simp [mooreNeighbors, Prod.ext_iff]; omega
  rw [hL, List.countP_map]
  congr 1
  ext q
  exact isAlive_shift v g q

/-- The local transition rule `aliveNext` is translation-invariant. -/
theorem aliveNext_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    aliveNext (shift v g) p = aliveNext g (p.1 - v.1, p.2 - v.2) := by
  simp [aliveNext, isAlive_shift, liveNeighborCount_shift]

/-- Membership in a `step` image, unfolded to the rule: `p` is in `step g`
    iff it is a candidate and `aliveNext` accepts it. -/
theorem mem_step_iff {g : Grid} {p : Int × Int} :
    p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true := by
  unfold step
  rw [mem_sortDedup, List.mem_filter]

/-! ## Commutation of `step` / `evolve` with translation

Conclusion of the translation-invariance chain: the local layer
(`isAlive_shift`, `liveNeighborCount_shift`, `aliveNext_shift` above) establishes
that the B3/S23 **rule** is invariant; this layer establishes that the global
**step** and its iteration **evolve** **commute** with grid translation:
`shift v (evolve n g) = evolve n (shift v g)`. This is the point-alignment
machinery `p ↔ p'` required by path (A) of #6724 before applying
`evolve_cone_agree` (which concludes only at a common point). -/

/-- Membership in a shifted grid: `p ∈ shift v g ↔ (p.1-v.1, p.2-v.2) ∈ g`. -/
theorem mem_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    p ∈ shift v g ↔ (p.1 - v.1, p.2 - v.2) ∈ g := by
  simp [shift, List.mem_map, mem_sortDedup]
  constructor
  · rintro ⟨a, b, hg, hp⟩
    have hp' : a + v.1 = p.1 ∧ b + v.2 = p.2 := Prod.ext_iff.mp hp
    have heq : (a, b) = (p.1 - v.1, p.2 - v.2) := by rw [Prod.ext_iff]; omega
    rw [← heq]; exact hg
  · intro h
    refine ⟨p.1 - v.1, p.2 - v.2, h, ?_⟩
    rw [Prod.ext_iff]; omega

/-- Moore neighbours are relative: `p ∈ mooreNeighbors a` is equivalent to
    `(p - v) ∈ mooreNeighbors (a - v)` (the translated neighbourhood coincides). -/
theorem mooreNeighbors_shift_mem (v a p : Int × Int) :
    p ∈ mooreNeighbors a ↔ (p.1 - v.1, p.2 - v.2) ∈ mooreNeighbors (a.1 - v.1, a.2 - v.2) := by
  simp [mooreNeighbors, Prod.ext_iff, Prod.eta]
  omega

/-- The candidate set is translation-invariant. -/
theorem candidates_shift (v : Int × Int) (g : Grid) (p : Int × Int) :
    p ∈ candidates (shift v g) ↔ (p.1 - v.1, p.2 - v.2) ∈ candidates g := by
  simp [candidates, mem_shift, mooreNeighbors_shift_mem, Prod.ext_iff]
  constructor
  · rintro (h | ⟨a, b, hg, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a - v.1, b - v.2, hg, (mooreNeighbors_shift_mem v (a, b) p).mp hm⟩
  · rintro (h | ⟨a, b, hg, hm⟩)
    · exact Or.inl h
    · refine Or.inr ⟨a + v.1, b + v.2, ?_, ?_⟩
      · have heq : (a + v.1 - v.1, b + v.2 - v.2) = (a, b) := by rw [Prod.ext_iff]; omega
        rw [heq]; exact hg
      · have heq : ((a + v.1) - v.1, (b + v.2) - v.2) = (a, b) := by rw [Prod.ext_iff]; omega
        have hm' : (p.1 - v.1, p.2 - v.2) ∈ mooreNeighbors ((a + v.1) - v.1, (b + v.2) - v.2) := by
          rw [heq]; exact hm
        exact (mooreNeighbors_shift_mem v (a + v.1, b + v.2) p).mpr hm'

/-- `step` commutes with translation: `shift v (step g) = step (shift v g)`. -/
theorem step_shift (v : Int × Int) (g : Grid) : shift v (step g) = step (shift v g) := by
  apply Canonical.ext
  · exact canonical_shift v (step g)
  · exact canonical_step (shift v g)
  · intro p
    rw [mem_shift, mem_step_iff, mem_step_iff, aliveNext_shift]
    constructor
    · rintro ⟨hc, ha⟩; exact ⟨(candidates_shift v g p).mpr hc, ha⟩
    · rintro ⟨hc, ha⟩; exact ⟨(candidates_shift v g p).mp hc, ha⟩

/-- `evolve` commutes with translation:
    `shift v (evolve n g) = evolve n (shift v g)` (by induction on `n`). -/
theorem evolve_shift (v : Int × Int) (n : Nat) (g : Grid) :
    shift v (evolve n g) = evolve n (shift v g) := by
  induction n with
  | zero => simp [evolve]
  | succ k ih => rw [evolve_succ, step_shift, ih, ← evolve_succ]

end Life_en
end Conway_en
