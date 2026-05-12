/-
  Sorted List Counting Lemmas
  ===========================

  Helper lemma stubs for counting elements in sorted lists relative to a pivot
  (typically the median element at position `length / 2`).

  These lemmas factor out the structural counting argument required by
  `Voting.lean median_voter_theorem_strict` (sorries at L355 and L385).

  PROOF STRATEGY (factored from Voting.lean L338-L354):
  1. Let `l` be a sorted list with pivot at position `k = l.length / 2`.
  2. Decompose `l = take k ++ drop k`.
  3. By sortedness, all elements in `drop k` are ≥ `l[k]`.
  4. Therefore `l.countP (· < l[k]) ≤ (take k).length = k`.
  5. Symmetrically, `l.countP (l[k] ≤ ·) ≥ (drop k).length = l.length - k`.

  Once these helpers are proven, Voting.lean L355 and L385 reduce to a
  bridging argument:
    A := Finset.filter (peaks i < median) Finset.univ
    A.card = (univ.toList.filter (peaks · < median)).length
           = (univ.toList.map peaks).countP (· < median)
           = (sortedPeaksList.countP (· < median))   [by Perm.countP_eq]
           ≤ k                                        [by countP_lt_kth_le_half]

  KEY MATHLIB LEMMAS (target API):
  - `List.Pairwise (· ≤ ·)` (sortedness primitive in current Mathlib)
  - `List.sorted_mergeSort` / `List.mergeSort_perm`
  - `List.Perm.countP_eq`, `List.countP_append`, `List.countP_eq_zero`
  - `List.length_take`, `List.length_drop`, `List.take_append_drop`

  STATUS: stub file with lemma signatures (sorries).
  Cycle 25 Wave 3 ai-01 backup for po-2026 Track 2.
  Reference: dispatched in msg-20260511T233949-r0i1xs (2026-05-11).
-/

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Count
import Mathlib.Tactic

namespace SocialChoice.SortedListCounting

variable {α : Type*}

/-! ## Counting elements relative to a sorted-list pivot -/

/-- For a list `l` sorted with `(· ≤ ·)` and pivot `l[k]`, the number of
    elements strictly less than `l[k]` is at most `k`.

    PROOF SKETCH (TODO po-2026 Track 2):
    - Decompose `l = l.take k ++ l.drop k` via `List.take_append_drop`.
    - `(l.take k).length = k` by `List.length_take` (using `hk : k < l.length`).
    - `(l.drop k).head = l[k]` by indexing.
    - By `Pairwise.drop` and head-of-drop reasoning, all elements of `l.drop k`
      are `≥ l[k]`.
    - Hence `(l.drop k).countP (· < l[k]) = 0` by `List.countP_eq_zero`.
    - Combining via `List.countP_append` and `List.countP_le_length`:
        `l.countP (· < l[k]) = (l.take k).countP (· < l[k]) + 0 ≤ k`. -/
theorem countP_lt_kth_le_half [LinearOrder α]
    {l : List α} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) :
    l.countP (fun x => decide (x < l[k])) ≤ k := by
  set p : α := l[k] with hp
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_lhs => rw [hsplit]
  rw [List.countP_append]
  have h1 : (l.take k).countP (fun x => decide (x < p)) ≤ k := by
    calc (l.take k).countP (fun x => decide (x < p))
        ≤ (l.take k).length := List.countP_le_length
      _ = min k l.length := List.length_take
      _ ≤ k := min_le_left _ _
  have h2 : (l.drop k).countP (fun x => decide (x < p)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro x hx
    simp only [decide_eq_true_eq, not_lt, hp]
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    rw [List.getElem_drop]
    have hki_lt : k + i < l.length := by
      have hi' := hi
      rw [List.length_drop] at hi'
      omega
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have hlt : k < k + i := by omega
      exact List.pairwise_iff_getElem.mp hsort k (k + i) hk hki_lt hlt
  omega

/-- For a list `l` sorted with `(· ≤ ·)` and pivot `l[k]`, the number of
    elements `≥ l[k]` is at least `l.length - k`.

    Dual of `countP_lt_kth_le_half`, giving a lower bound on the
    "right side" of the pivot.

    PROOF SKETCH (TODO po-2026 Track 2):
    - Decompose `l = l.take k ++ l.drop k`.
    - `(l.drop k).length = l.length - k` by `List.length_drop`.
    - All elements of `l.drop k` are `≥ l[k]` (head + sortedness).
    - So `(l.drop k).countP (l[k] ≤ ·) = (l.drop k).length`.
    - Adding `(l.take k).countP (l[k] ≤ ·) ≥ 0` gives the bound. -/
theorem countP_ge_kth_ge_half_succ [LinearOrder α]
    {l : List α} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ} (hk : k < l.length) :
    l.length - k ≤ l.countP (fun x => decide (l[k] ≤ x)) := by
  set p : α := l[k] with hp
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit]
  rw [List.countP_append]
  have hdrop_all : (l.drop k).countP (fun x => decide (p ≤ x)) = (l.drop k).length := by
    rw [List.countP_eq_length]
    intro x hx
    simp only [decide_eq_true_eq, hp]
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    rw [List.getElem_drop]
    have hki_lt : k + i < l.length := by
      have hi' := hi
      rw [List.length_drop] at hi'
      omega
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have hlt : k < k + i := by omega
      exact List.pairwise_iff_getElem.mp hsort k (k + i) hk hki_lt hlt
  have hdrop_len : (l.drop k).length = l.length - k := List.length_drop
  rw [hdrop_all, hdrop_len]
  omega

/-! ## Application to median voter (planned)

    Once `countP_lt_kth_le_half` and `countP_ge_kth_ge_half_succ` are proven,
    the following corollary closes Voting.lean L355 (and L385 by symmetry):

    For an odd `n`, sorted list `l` of length `n`, pivot `m := l[n/2]`,
    and predicates `P_lt := (· < m)`, `P_ge := (m ≤ ·)` :
        l.countP P_lt < l.countP P_ge

    Proof: by `countP_lt_kth_le_half`, `l.countP P_lt ≤ n/2`.
    By `countP_ge_kth_ge_half_succ`, `l.countP P_ge ≥ n - n/2 = (n+1)/2`.
    For odd `n = 2k+1`, `n/2 = k` and `(n+1)/2 = k+1`, hence `<`.

    The bridge from `Finset.filter ... Finset.univ` to `List.countP` uses
    `Finset.length_toList`, `List.countP_map`, `List.length_filter_eq_countP`,
    and `List.Perm.countP_eq` (for mergeSort). -/

end SocialChoice.SortedListCounting
