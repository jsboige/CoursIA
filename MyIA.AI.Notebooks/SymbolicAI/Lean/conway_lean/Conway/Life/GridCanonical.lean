/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Canonical grid forms — the `sortDedup` specification

Every grid manipulated by the Life engine is a `sortDedup` image:
`step`, `evolve (n+1)`, `shift` and `MacroCell.toGrid` all post-compose
with `sortDedup`, and `restrictGridTo` is a `filter` of such an image.
This module proves that `sortDedup` outputs are **canonical** — lex-sorted
and duplicate-free — and that canonical lists are **rigid**: determined by
their membership predicate alone (`Canonical.ext`).

This is the bridge that turns the list-equality goals of the Hashlife
correctness theorems (P4/P5, `HashlifeCorrectness.lean`) into pointwise
membership goals, where the actual combinatorics of the B3/S23 rule and
the macrocell recursion can be argued cell by cell.

The order theory is elementary: `lexLe` (reflexive closure of `lexLt`)
is total, transitive and antisymmetric on `Int × Int`, all by `omega`
after unfolding to linear integer arithmetic.

This module is fully proven (no `sorry`).
-/

import Conway.Life

namespace Conway
namespace Life

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

/-- `lexLe` is total — the hypothesis `List.pairwise_mergeSort` needs. -/
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

/-! ## Canonical grids -/

/-- A grid in canonical form: lexicographically sorted and duplicate-free.
    Invariant of every `sortDedup` image, preserved by `filter`. -/
def Canonical (g : Grid) : Prop :=
  g.Pairwise (fun a b => lexLe a b = true) ∧ g.Nodup

/-- `sortDedup` always produces a canonical grid: sortedness comes from
    `pairwise_mergeSort` (using totality and transitivity of `lexLe`) and
    survives `dedup` because `dedup` yields a sublist; freedom from
    duplicates is `nodup_dedup`. -/
theorem canonical_sortDedup (l : List (Int × Int)) : Canonical (sortDedup l) := by
  unfold sortDedup
  exact ⟨List.Pairwise.sublist (List.dedup_sublist _)
          (List.pairwise_mergeSort lexLe_trans lexLe_total l),
        List.nodup_dedup _⟩

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

/-- Membership in a `step` image, unfolded to the rule: `p` is in `step g`
    iff it is a candidate and `aliveNext` accepts it. -/
theorem mem_step_iff {g : Grid} {p : Int × Int} :
    p ∈ step g ↔ p ∈ candidates g ∧ aliveNext g p = true := by
  unfold step
  rw [mem_sortDedup, List.mem_filter]

end Life
end Conway
