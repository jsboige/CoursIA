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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic

import SocialChoice.Basic
import SocialChoice.SortedListCounting

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

/-! ## Single-Peaked Preferences

Reference: Black (1948), "On the Rationale of Group Decision-making"

A preference ordering over a linearly ordered set is single-peaked if there
exists a unique most-preferred alternative (the peak) and preferences decline
monotonically away from the peak in both directions.
-/

section SinglePeaked

variable [LinearOrder σ]

/-- The peak of a preference relation: the unique strictly most-preferred element -/
def is_peak (R : σ → σ → Prop) (p : σ) : Prop :=
  ∀ x, x ≠ p → P R p x

/-- R is single-peaked with peak p on a linearly ordered set.
    1. p is the peak (strictly preferred to everything else)
    2. Left of peak: closer to peak is weakly preferred (a ≤ b ≤ p → R b a)
    3. Right of peak: closer to peak is weakly preferred (p ≤ a ≤ b → R a b) -/
def single_peaked (R : σ → σ → Prop) (p : σ) : Prop :=
  is_peak R p ∧
  (∀ a b, a ≤ b → b ≤ p → R b a) ∧
  (∀ a b, p ≤ a → a ≤ b → R a b)

/-- The peak is unique -/
theorem single_peaked_peak_unique {R : σ → σ → Prop} {p q : σ}
    (hsp : single_peaked R p) (hsq : single_peaked R q) (hne : p ≠ q) : False := by
  have hPpq : P R p q := hsp.1 q hne.symm
  have hPqp : P R q p := hsq.1 p hne
  exact hPpq.2 hPqp.1

/-- Single-peaked implies the peak is the best element (under Reflexive R) -/
theorem single_peaked_peak_best {R : σ → σ → Prop} {p : σ} {S : Finset σ}
    (hrefl : Reflexive R) (hsp : single_peaked R p) (hpS : p ∈ S) :
    is_best_element p S R := by
  intro y hy
  by_cases heq : y = p
  · subst heq; exact hrefl y
  · exact (hsp.1 y heq).1

/-- A profile is single-peaked if every voter has single-peaked preferences -/
def single_peaked_profile (prof : ι → PrefOrder σ) (peaks : ι → σ) : Prop :=
  ∀ i : ι, single_peaked (prof i).rel (peaks i)

/-- R is **strictly** single-peaked with peak p on a linearly ordered set.
    Strengthens `single_peaked` with strict monotonicity on each side of the peak,
    eliminating indifference between distinct alternatives on the same side.

    This is the hypothesis needed to obtain a *strict* Condorcet winner via
    `margin_pos` (positive margin), as opposed to the weak `margin ≥ 0`
    guarantee from `single_peaked` alone.

    Concretely:
    - `a < b ≤ p` implies `P R b a` (strictly prefer b to a, left of peak)
    - `p ≤ a < b` implies `P R a b` (strictly prefer a to b, right of peak) -/
def strictly_single_peaked (R : σ → σ → Prop) (p : σ) : Prop :=
  single_peaked R p ∧
  (∀ a b, a < b → b ≤ p → P R b a) ∧
  (∀ a b, p ≤ a → a < b → P R a b)

/-- A profile is strictly single-peaked if every voter has strictly single-peaked
    preferences. This is the standard hypothesis under which the median voter
    theorem yields a *Condorcet winner* (positive margin) rather than just a
    weak Condorcet winner (non-negative margin). -/
def strictly_single_peaked_profile (prof : ι → PrefOrder σ) (peaks : ι → σ) : Prop :=
  ∀ i : ι, strictly_single_peaked (prof i).rel (peaks i)

set_option linter.unusedSectionVars false in
/-- A strictly single-peaked profile is in particular single-peaked. -/
theorem strictly_single_peaked_profile.to_single_peaked
    {prof : ι → PrefOrder σ} {peaks : ι → σ}
    (h : strictly_single_peaked_profile prof peaks) :
    single_peaked_profile prof peaks :=
  fun i => (h i).1

/-! ## Median Voter Theorem (Black 1948)

For an odd number of voters with single-peaked preferences over a linearly
ordered set, the median peak (the middle element of sorted peaks) is a
Condorcet winner under majority rule.

Proof sketch:
- For any y < median: strictly more than n/2 voters have peak >= median,
  and by single-peakedness they prefer median to y
- For any y > median: strictly more than n/2 voters have peak <= median,
  and by single-peakedness they prefer median to y
-/

/-- Sorted list of peaks (with duplicates preserved) -/
noncomputable def sorted_peaks_list (peaks : ι → σ) : List σ :=
  (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)

/-- The median peak: the middle element of sorted peaks.
    For odd n, this is the unique middle element. -/
noncomputable def median_peak [Inhabited σ] (peaks : ι → σ) : σ :=
  let s := sorted_peaks_list peaks
  s.getD (s.length / 2) default

/-- **Median Voter Theorem — Strict-hypotheses version (Black 1948)**:
    For an odd number of voters with single-peaked preferences AND explicit
    strict monotonicity on each side of the peak, the median peak is a
    Condorcet winner.

    This is the workhorse lemma; `median_voter_theorem` below packages the
    strict-monotonicity hypotheses into the `strictly_single_peaked_profile`
    predicate. Both theorems are equivalent after unfolding. -/
theorem median_voter_theorem_strict [Inhabited σ] (prof : ι → PrefOrder σ) (peaks : ι → σ)
    (hsp : single_peaked_profile prof peaks)
    (hstrict_left : ∀ i a b, a < b → b ≤ peaks i → P (prof i).rel b a)
    (hstrict_right : ∀ i a b, peaks i ≤ a → a < b → P (prof i).rel a b)
    (hodd : Odd (Fintype.card ι)) :
    ∃ m, condorcet_winner prof (Finset.univ.image peaks) m := by
  classical
  have hcard_pos : 0 < Fintype.card ι := by
    have := hodd; rw [Nat.odd_iff] at this; omega
  have hne : Nonempty ι := Fintype.card_pos_iff.mp hcard_pos
  use median_peak peaks
  constructor
  · -- median ∈ image of peaks
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    unfold median_peak sorted_peaks_list
    let l := (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)
    have hl : l.length = Fintype.card ι := by unfold l; simp [List.length_mergeSort, List.length_map, Finset.length_toList]
    have hn : l.length / 2 < l.length := by omega
    have hin : l.getD (l.length / 2) default ∈ l := by simp [List.getD, List.getElem?_eq_getElem, hn]
    have hperm : l ≈ Finset.univ.toList.map peaks := List.mergeSort_perm _ _
    rw [List.Perm.mem_iff hperm] at hin
    simp at hin
    exact hin
  · -- margin_pos for any y ≠ median
    intro y hy hny
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy
    obtain ⟨j, hyj⟩ := hy; subst hyj
    unfold margin_pos margin
    by_cases hlt : peaks j < median_peak peaks
    · -- Case: peaks_j < median. Voters with peak >= median prefer median over j.
      -- Count: |{i | median ≤ peaks i}| > |{i | peaks i < median}| for odd n.
      have hgt_peaks : ∀ i, median_peak peaks ≤ peaks i → P (prof i).rel (median_peak peaks) (peaks j) := by
        intro i hi
        exact hstrict_left i (peaks j) (median_peak peaks) hlt hi
      -- Voters preferring median: at least the set {i | median ≤ peaks i}
      have hfor_card : (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card ≤
          (Finset.filter (fun i => P (prof i).rel (median_peak peaks) (peaks j)) Finset.univ).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hgt_peaks i hi
      -- Voters preferring j: at most the set {i | peaks i < median}
      have hag_card : (Finset.filter (fun i => P (prof i).rel (peaks j) (median_peak peaks)) Finset.univ).card ≤
          (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra hnot
        have hle : median_peak peaks ≤ peaks i := le_of_not_gt hnot
        exact (hgt_peaks i hle).2 hi.1
      -- Key counting: |{peaks < median}| < |{median ≤ peaks}|
      -- Follows from median being at position n/2 in sorted peaks list.
      -- For odd n = 2k+1: at most k peaks are strictly less, at least k+1 are ≥ median.
      have hcount : (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card <
          (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card := by
        -- Step 1: complementarity gives A.card + B.card = n
        have hcomp : (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card +
            (Finset.filter (fun i => median_peak peaks ≤ peaks i) Finset.univ).card =
            Fintype.card ι := by
          have hflip : (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ) =
              (Finset.filter (fun i => ¬ median_peak peaks ≤ peaks i) Finset.univ) := by
            apply Finset.filter_congr
            intro i _
            exact (not_le).symm
          rw [hflip, add_comm,
              Finset.card_filter_add_card_filter_not
                (s := Finset.univ) (p := fun i => median_peak peaks ≤ peaks i),
              Finset.card_univ]
        -- Step 1: Setup sorted list of peaks
        set l := (Finset.univ.toList.map peaks).mergeSort (· ≤ ·) with hl_def
        have hl_len : l.length = Fintype.card ι := by
          simp [l, List.length_mergeSort, List.length_map, Finset.length_toList]
        have hl_pos : 0 < l.length := by rw [hl_len]; exact hcard_pos
        have hn : l.length / 2 < l.length := Nat.div_lt_self hl_pos (by omega)
        have hperm : l ≈ Finset.univ.toList.map peaks := List.mergeSort_perm _ _
        have hsorted : l.Pairwise (· ≤ ·) :=
          List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map peaks)
        -- Step 2: median_peak peaks = l[l.length / 2]
        have hmedian_eq : median_peak peaks = l[l.length / 2] := by
          unfold median_peak sorted_peaks_list
          show l.getD (l.length / 2) default = l[l.length / 2]
          simp [List.getD, hn]
        -- Step 3: Bridge A.card to l.countP via SortedListCounting helper
        have hA_bridge :
            (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card =
              l.countP (fun x => decide (x < median_peak peaks)) := by
          rw [show (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ) =
              (Finset.filter (fun i => decide (peaks i < median_peak peaks) = true) Finset.univ)
              from by simp,
              SortedListCounting.finset_filter_lt_card_eq_toList_map_countP peaks
                (fun x => decide (x < median_peak peaks))]
          exact (hperm.countP_eq _).symm
        -- Step 4: Apply countP_lt_kth_le_half to bound A.card by l.length / 2
        have hA_bound :
            (Finset.filter (fun i => peaks i < median_peak peaks) Finset.univ).card ≤
              l.length / 2 := by
          rw [hA_bridge, hmedian_eq]
          exact SortedListCounting.countP_lt_kth_le_half hsorted hn
        -- Step 5: Combine with hcomp + hodd: for odd n = 2k+1, A.card ≤ k < k+1 ≤ B.card
        have hodd_n : Odd l.length := by rw [hl_len]; exact hodd
        obtain ⟨k, hk⟩ := hodd_n
        omega
      omega
    · -- Case: peaks_j > median. Voters with peak <= median prefer median over j.
      have hgt : median_peak peaks < peaks j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hny)
      have hlt_peaks : ∀ i, peaks i ≤ median_peak peaks → P (prof i).rel (median_peak peaks) (peaks j) := by
        intro i hi
        exact hstrict_right i (median_peak peaks) (peaks j) hi hgt
      have hfor_card : (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card ≤
          (Finset.filter (fun i => P (prof i).rel (median_peak peaks) (peaks j)) Finset.univ).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hlt_peaks i hi
      have hag_card : (Finset.filter (fun i => P (prof i).rel (peaks j) (median_peak peaks)) Finset.univ).card ≤
          (Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra hnot
        have hle : peaks i ≤ median_peak peaks := le_of_not_gt hnot
        exact (hlt_peaks i hle).2 hi.1
      have hcount : (Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ).card <
          (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card := by
        -- Step 1: Setup sorted list of peaks (mirror of LT case)
        set l := (Finset.univ.toList.map peaks).mergeSort (· ≤ ·) with hl_def
        have hl_len : l.length = Fintype.card ι := by
          simp [l, List.length_mergeSort, List.length_map, Finset.length_toList]
        have hl_pos : 0 < l.length := by rw [hl_len]; exact hcard_pos
        have hn : l.length / 2 < l.length := Nat.div_lt_self hl_pos (by omega)
        have hperm : l ≈ Finset.univ.toList.map peaks := List.mergeSort_perm _ _
        have hsorted : l.Pairwise (· ≤ ·) :=
          List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map peaks)
        -- Step 2: median_peak peaks = l[l.length / 2]
        have hmedian_eq : median_peak peaks = l[l.length / 2] := by
          unfold median_peak sorted_peaks_list
          show l.getD (l.length / 2) default = l[l.length / 2]
          simp [List.getD, hn]
        -- Step 3: Complementarity A.card + B.card = n
        have hcomp_dual :
            (Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ).card +
              (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card =
                Fintype.card ι := by
          have hflip :
              (Finset.filter (fun i => median_peak peaks < peaks i) Finset.univ) =
                (Finset.filter (fun i => ¬ peaks i ≤ median_peak peaks) Finset.univ) := by
            apply Finset.filter_congr
            intro i _
            exact (not_le).symm
          rw [hflip, add_comm,
              Finset.card_filter_add_card_filter_not
                (s := Finset.univ) (p := fun i => peaks i ≤ median_peak peaks),
              Finset.card_univ]
        -- Step 4: Bridge B.card to l.countP (· ≤ median) via SortedListCounting helper
        have hB_bridge :
            (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card =
              l.countP (fun x => decide (x ≤ median_peak peaks)) := by
          rw [show (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ) =
              (Finset.filter (fun i => decide (peaks i ≤ median_peak peaks) = true) Finset.univ)
              from by simp,
              SortedListCounting.finset_filter_lt_card_eq_toList_map_countP peaks
                (fun x => decide (x ≤ median_peak peaks))]
          exact (hperm.countP_eq _).symm
        -- Step 5: Apply countP_le_kth_ge_half_succ to lower-bound B.card by l.length / 2 + 1
        have hB_bound : l.length / 2 + 1 ≤
            (Finset.filter (fun i => peaks i ≤ median_peak peaks) Finset.univ).card := by
          rw [hB_bridge, hmedian_eq]
          exact SortedListCounting.countP_le_kth_ge_half_succ hsorted hn
        -- Step 6: Combine with hcomp_dual + hodd: for odd n = 2k+1, B.card ≥ k+1, A.card ≤ k
        have hodd_n : Odd l.length := by rw [hl_len]; exact hodd
        obtain ⟨k, hk⟩ := hodd_n
        omega
      omega

/-- **Median Voter Theorem (Black 1948)**: For an odd number of voters with
    **strictly** single-peaked preferences, the median peak is a Condorcet winner.

    Note (Issue #973): the hypothesis was strengthened from `single_peaked_profile`
    to `strictly_single_peaked_profile`. The weaker `single_peaked` allows
    indifference between distinct alternatives on the same side of the peak,
    which is incompatible with the *strict* Condorcet winner conclusion via
    `margin_pos`. Under `strictly_single_peaked_profile`, voters can no longer
    be indifferent between distinct alternatives on the same side of their peak,
    yielding positive margins as required. This delegates to
    `median_voter_theorem_strict` after extracting the strict monotonicity
    components. -/
theorem median_voter_theorem (prof : ι → PrefOrder σ) (peaks : ι → σ)
    (hsp : strictly_single_peaked_profile prof peaks)
    (hodd : Odd (Fintype.card ι)) :
    ∃ m, condorcet_winner prof (Finset.univ.image peaks) m := by
  classical
  have hcard_pos : 0 < Fintype.card ι := by
    have := hodd; rw [Nat.odd_iff] at this; omega
  have hne : Nonempty ι := Fintype.card_pos_iff.mp hcard_pos
  haveI : Inhabited σ := Classical.inhabited_of_nonempty (hne.map peaks)
  exact median_voter_theorem_strict prof peaks
    (strictly_single_peaked_profile.to_single_peaked hsp)
    (fun i a b hab hbp => (hsp i).2.1 a b hab hbp)
    (fun i a b hpa hab => (hsp i).2.2 a b hpa hab)
    hodd

/-! ## Strategy-Proofness under Single-Peaked Preferences -/

/-- A voting rule f is strategy-proof on a set S if no voter can change the
    outcome to one they strictly prefer by misreporting their preferences.
    Here stated without Function.update to avoid DecidableEq ι:
    for any truthful profile prof and deviating profile prof' that agrees
    with prof everywhere except possibly at i, the deviant outcome is not
    strictly preferred (under the true preferences) to the truthful outcome. -/
def strategy_proof_scc (f : SCC ι σ) (S : Finset σ) : Prop :=
  ∀ prof prof' i,
    (∀ j, j ≠ i → prof' j = prof j) →
    ¬ ∃ x y, x ∈ f prof' S ∧ y ∈ f prof S ∧ P (prof i).rel x y

/-- Under strictly single-peaked preferences, no voter can strictly prefer
    the median peak to their own peak. This is the core insight behind
    strategy-proofness of the median rule: the peak is the unique top
    element of the preference ordering, so nothing (including the median)
    can be strictly preferred to it.

    This lemma does NOT require an odd number of voters — it is purely
    about the preference structure. -/
theorem peak_not_strictly_preferred_to_median [Inhabited σ]
    (prof : ι → PrefOrder σ)
    (peaks : ι → σ)
    (hsp : strictly_single_peaked_profile prof peaks)
    (i : ι)
    (hne : peaks i ≠ median_peak peaks) :
    ¬ P (prof i).rel (median_peak peaks) (peaks i) := by
  intro h
  -- is_peak gives: ∀ x ≠ p, P R p x (peak strictly preferred to everything else)
  -- So P (prof i).rel (peaks i) (median_peak peaks) with component .2 = ¬ R (median_peak) (peaks_i)
  -- But h.1 gives R (median_peak) (peaks_i), contradiction.
  exact (hsp i).1.1 (median_peak peaks) hne.symm |>.2 h.1

end SinglePeaked

section SplitCycle

/-- A cycle in a relation R over a list: the last element relates to the first,
    forming a chain. -/
def cycle {X : Type*} (R : X → X → Prop) (c : List X) : Prop :=
  ∃ h : c ≠ [], List.IsChain R (c.getLast h :: c)

/-- A relation is acyclic if no cycles exist. -/
def acyclic {X : Type*} (R : X → X → Prop) : Prop :=
  ∀ c : List X, ¬ cycle R c

/-- Split Cycle defeat: x defeats y if
    1. x beats y by strict majority (positive margin), AND
    2. There is no cycle through x and y where every margin is >= margin(x,y).
    This resolves Condorcet cycles by only accepting defeats that aren't
    "locked out" by a stronger cycle. -/
noncomputable def split_cycle_defeats (prof : ι → PrefOrder σ) (x y : σ) : Prop :=
  margin_pos prof x y ∧
    ¬ ∃ c : List σ, x ∈ c ∧ y ∈ c ∧
      cycle (fun a b => (margin prof x y : Int) ≤ margin prof a b) c

/-- Split Cycle rule: select all alternatives that are not defeated by any other.
    Equivalently, x wins iff no y split-cycle defeats x. -/
noncomputable def split_cycle_scc : SCC ι σ := fun prof S => by
  classical
  exact S.filter (fun x => ∀ y ∈ S, ¬ split_cycle_defeats prof y x)

/-- Split Cycle is Condorcet-consistent:
    if x is a Condorcet winner, x is not split-cycle defeated by anyone. -/
theorem split_cycle_condorcet (prof : ι → PrefOrder σ) {S : Finset σ} {x : σ}
    (hw : condorcet_winner prof S x) : x ∈ split_cycle_scc prof S := by
  classical
  obtain ⟨hxs, hbeat⟩ := hw
  simp only [split_cycle_scc, Finset.mem_filter]
  exact ⟨hxs, fun y hyS ⟨hpos, _⟩ => by
    have hne : y ≠ x := fun h => by
      subst h; unfold margin_pos at hpos; rw [margin_self] at hpos; linarith
    have hmx := hbeat y hyS hne
    unfold margin_pos at hpos hmx
    rw [margin_antisymm prof y x] at hpos
    linarith⟩

/-- Cycle length is positive. -/
theorem cycle_length_pos {X : Type*} {R : X → X → Prop} {c : List X} (hc : cycle R c) :
    0 < c.length := by
  rcases hc with ⟨h, _⟩
  exact List.length_pos_of_ne_nil h

/-- Appending an element to a chain: if the chain's last element relates to x,
    we can extend the chain with x. Uses structural recursion via match. -/
private theorem isChain_append_last {α : Type*} {R : α → α → Prop}
    {l : List α} (hne : l ≠ []) {x : α}
    (hchain : List.IsChain R l)
    (hR : R (l.getLast hne) x) :
    List.IsChain R (l ++ [x]) :=
  match l, hne, hchain with
  | [], h, _ => absurd rfl h
  | [_], _, _ => List.IsChain.cons_cons hR (List.IsChain.singleton x)
  | _ :: b :: l'', _, .cons_cons hab hrest =>
    List.IsChain.cons_cons hab (isChain_append_last (List.cons_ne_nil b l'') hrest hR)

/-- Rotating a cycle preserves the cycle property.
    For `a :: l`, the cycle `IsChain R (getLast (a::l) :: a :: l)` rotates to
    `IsChain R (a :: l ++ [a])`. -/
theorem rotate_cycle {X : Type*} {R : X → X → Prop} {a : X} {l : List X}
    (hc : cycle R (a :: l)) : cycle R (l ++ [a]) := by
  rcases hc with ⟨hne, hchain⟩
  refine ⟨List.append_ne_nil_of_right_ne_nil l (List.cons_ne_nil a []), ?_⟩
  -- getLast (l ++ [a]) = a, so need IsChain R (a :: l ++ [a])
  simp only [List.getLast_append, List.getLast_singleton]
  cases l with
  | nil => exact hchain
  | cons b l' =>
    simp only [List.cons_append]
    match hchain with
    | .cons_cons hRza (.cons_cons hRab hchain_bl) =>
      -- hRza : R (getLast(b::l')) a, hRab : R a b, hchain_bl : IsChain R (b :: l')
      -- Build IsChain R (b :: l' ++ [a]) from hchain_bl + hRza
      -- Then IsChain R (a :: b :: l' ++ [a]) from hRab + above
      have h := isChain_append_last (List.cons_ne_nil b l') hchain_bl hRza
      exact List.IsChain.cons_cons hRab h

/-- From a chain `IsChain R (l.head :: l)`, the head relates to every member of l.
    Uses pairwise: `Pairwise R (l.head :: l)` means head relates to all of l. -/
private theorem chain_head_rel_mem {α : Type*} {R : α → α → Prop} [Trans R R R]
    {a : α} {l : List α} (hchain : List.IsChain R (a :: l))
    {x : α} (hmem : x ∈ l) : R a x := by
  have hp := hchain.pairwise
  rw [List.pairwise_cons] at hp
  exact hp.1 x hmem

set_option linter.unusedSectionVars false in
/-- Cycles are impossible on strict linear orders.
    A cycle `getLast c :: c` under `<` means the last element relates to itself
    via the chain, contradicting irreflexivity of `<`. -/
theorem lt_acyclic [LinearOrder σ] : acyclic (fun (x y : σ) => x < y) := by
  intro c hc
  rcases hc with ⟨hne, hchain⟩
  have hmem : c.getLast hne ∈ c := List.getLast_mem hne
  have hlt : c.getLast hne < c.getLast hne :=
    chain_head_rel_mem hchain hmem
  exact lt_irrefl _ hlt

end SplitCycle

/-! ## Clone Sets and Independence

A set of candidates X forms a clone set if every voter ranks all members of X
in an adjacent block (either all above or all below any candidate outside X).
This is relevant for clone-independent voting rules (e.g., Schulze, Split Cycle).

Reference: DominikPeters/SocialChoiceLean `SocialChoice.Axioms.Clones`
-/

section Clones

variable [DecidableEq σ] [Fintype σ]

/-- A clone set X in profile prof: every voter ranks X as a contiguous block. -/
def clone_set (prof : ι → PrefOrder σ) (X : Finset σ) : Prop :=
  X.Nonempty ∧ ∀ (v : ι) (c : σ), c ∉ X →
    (∀ x ∈ X, P (prof v).rel x c) ∨ (∀ x ∈ X, P (prof v).rel c x)

/-- Clone independence: replacing all clones by a single representative
    does not change the relative ranking of non-clone candidates. -/
def clone_independence (f : SCC ι σ) : Prop :=
  ∀ prof X x, clone_set prof X → x ∈ X →
    f prof (Finset.univ \ (X.erase x)) =
      ((f prof Finset.univ).image (fun y => if y ∈ X then x else y)).filter
        (fun y => y ∈ Finset.univ \ (X.erase x))

/-- An SCC is clone-independent if it satisfies clone independence for all profiles. -/
theorem clone_set_nonempty {prof : ι → PrefOrder σ} {X : Finset σ}
    (hc : clone_set prof X) : X.Nonempty := hc.1

end Clones

/-! ## Banks Set

The Banks set (Banks 1985) is a tournament solution concept. Given a majority
tournament (derived from pairwise margins), a Banks winner is an alternative that
tops some maximal transitive subtournament (i.e., some maximal chain).

Reference: Banks, "Sophisticated Voting Outcomes and Agenda Control" (1985)
-/

section BanksSet

/-- A profile induces a tournament on S: every distinct pair has a strict majority winner.
    This means for all x ≠ y in S, exactly one of margin(x,y) > 0 or margin(y,x) > 0 holds. -/
def is_tournament (prof : ι → PrefOrder σ) (S : Finset σ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → margin_pos prof x y ∨ margin_pos prof y x

/-- A Banks chain: a subset of S that is totally ordered by the majority relation,
    and is maximal (adding any element from S breaks transitivity). -/
def banks_chain (prof : ι → PrefOrder σ) (S : Finset σ) (C : Finset σ) : Prop :=
  C ⊆ S ∧ C.Nonempty ∧
  (∀ x ∈ C, ∀ y ∈ C, x ≠ y → margin_pos prof x y ∨ margin_pos prof y x) ∧
  -- Transitivity of the chain's tournament relation
  (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C,
    margin_pos prof x y → margin_pos prof y z → margin_pos prof x z) ∧
  -- Maximality: no element from S\C can be added while preserving the above
  (∀ x ∈ S, x ∉ C → ¬(
    (∀ y ∈ C, margin_pos prof x y ∨ margin_pos prof y x) ∧
    (∀ y ∈ C, ∀ z ∈ C,
      margin_pos prof y z → (margin_pos prof x y → margin_pos prof x z) ∧
      (margin_pos prof z x → margin_pos prof y x))))

/-- x is a Banks winner: it is the maximal element of some Banks chain.
    Being maximal means no element of the chain has a positive margin over x. -/
def banks_winner (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ ∃ C : Finset σ, banks_chain prof S C ∧ x ∈ C ∧
    ∀ y ∈ C, y ≠ x → margin_pos prof x y

/-- The Banks set: all Banks winners in S -/
noncomputable def banks_set (prof : ι → PrefOrder σ) (S : Finset σ) : Finset σ := by
  classical
  exact S.filter (fun x => banks_winner prof S x)

/-- The Banks set is a subset of S -/
theorem banks_set_subset (prof : ι → PrefOrder σ) (S : Finset σ) :
    banks_set prof S ⊆ S := by
  classical
  unfold banks_set
  exact Finset.filter_subset _ _

/-- A Condorcet winner is always in the Banks set -/
theorem banks_set_condorcet (prof : ι → PrefOrder σ) {S : Finset σ} {x : σ}
    (hw : condorcet_winner prof S x) :
    x ∈ banks_set prof S := by
  classical
  unfold banks_set banks_winner
  simp only [Finset.mem_filter, hw.1, true_and]
  let isTC (C : Finset σ) : Prop :=
    C ⊆ S ∧ C.Nonempty ∧
    (∀ a ∈ C, ∀ b ∈ C, a ≠ b → margin_pos prof a b ∨ margin_pos prof b a) ∧
    (∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C,
      margin_pos prof a b → margin_pos prof b c → margin_pos prof a c) ∧
    x ∈ C
  have h_single : isTC {x} := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.singleton_subset_iff.mpr hw.1
    · exact ⟨x, Finset.mem_singleton_self x⟩
    · intro a ha b hb hab
      simp only [Finset.mem_singleton] at ha hb
      subst ha; subst hb; contradiction
    · intro a ha b hb c hc hab hbc
      simp only [Finset.mem_singleton] at ha hb hc
      subst ha; subst hb; subst hc; exact hab
    · exact Finset.mem_singleton_self x
  have hTC_nonempty : (Finset.filter isTC (Finset.powerset S)).Nonempty :=
    ⟨{x}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.singleton_subset_iff.mpr hw.1), h_single⟩⟩
  obtain ⟨C, hC_filter, hC_max⟩ := Finset.exists_mem_eq_sup' hTC_nonempty (fun C => C.card)
  have hC_mem : C ∈ Finset.filter isTC (Finset.powerset S) := hC_filter
  obtain ⟨hC_sub, hC_ne, hC_tourn, hC_trans, hC_x⟩ := Finset.mem_filter.mp hC_mem |>.2
  have hC_x_beats : ∀ y ∈ C, y ≠ x → margin_pos prof x y := by
    intro y hy hne
    have ht := hC_tourn x hC_x y hy hne.symm
    by_cases h : margin_pos prof x y
    · exact h
    · exfalso
      have hxy := hw.2 y (hC_sub hy) hne
      have := margin_antisymm prof x y
      unfold margin_pos at *; omega
  have hC_chain : banks_chain prof S C := by
    refine ⟨hC_sub, hC_ne, hC_tourn, hC_trans, ?_⟩
    intro y hyS hyC
    by_contra h_ext
    obtain ⟨h_ext_tourn, h_ext_trans⟩ := h_ext
    have hxy : margin_pos prof x y :=
      hw.2 y hyS (by intro h; subst h; exact hyC hC_x)
    have h_no_self : ¬margin_pos prof y y := by
      intro h; unfold margin_pos at h; have := margin_self prof y; omega
    have h_insert_sub : ({y} ∪ C) ⊆ S :=
      Finset.union_subset (Finset.singleton_subset_iff.mpr hyS) hC_sub
    have h_insert_ne : ({y} ∪ C).Nonempty :=
      ⟨y, Finset.mem_union.mpr (.inl (Finset.mem_singleton_self y))⟩
    have h_insert_x : x ∈ {y} ∪ C := Finset.mem_union.mpr (.inr hC_x)
    have h_insert_tourn :
        ∀ a ∈ {y} ∪ C, ∀ b ∈ {y} ∪ C, a ≠ b →
          margin_pos prof a b ∨ margin_pos prof b a := by
      intro a ha b hb hab
      simp only [Finset.mem_union, Finset.mem_singleton] at ha hb
      rcases ha with rfl | ha_mem <;> rcases hb with rfl | hb_mem
      · contradiction
      · exact h_ext_tourn b hb_mem
      · exact (h_ext_tourn a ha_mem).symm
      · exact hC_tourn a ha_mem b hb_mem hab
    have h_insert_trans :
        ∀ a ∈ {y} ∪ C, ∀ b ∈ {y} ∪ C, ∀ c ∈ {y} ∪ C,
          margin_pos prof a b → margin_pos prof b c → margin_pos prof a c := by
      intro a ha b hb c hc hab hbc
      simp only [Finset.mem_union, Finset.mem_singleton] at ha hb hc
      rcases ha with (ha_eq | ha_mem) <;> rcases hb with (hb_eq | hb_mem) <;>
        rcases hc with (hc_eq | hc_mem)
      · -- (y,y,y)
        exfalso; rw [ha_eq, hb_eq] at hab; exact h_no_self hab
      · -- (y,y,C)
        exfalso; rw [ha_eq, hb_eq] at hab; exact h_no_self hab
      · -- (y,C,y): mp y b ∧ mp b y → antisymm contradiction
        exfalso; rw [ha_eq] at hab; rw [hc_eq] at hbc
        unfold margin_pos at *; have := margin_antisymm prof y b; omega
      · -- (y,C,C): forward via h_ext_trans .1
        rw [ha_eq]; rw [ha_eq] at hab
        exact (h_ext_trans b hb_mem c hc_mem hbc).1 hab
      · -- (C,y,y)
        exfalso; rw [hb_eq, hc_eq] at hbc; exact h_no_self hbc
      · -- (C,y,C): mp a y ∧ mp y c → by_cases
        rw [hb_eq] at hab; rw [hb_eq] at hbc
        by_cases hac : margin_pos prof a c
        · exact hac
        · exfalso
          have hne : c ≠ a := by
            intro h; rw [h] at hbc
            unfold margin_pos at *; have := margin_antisymm prof a y; omega
          have hca : margin_pos prof c a :=
            (hC_tourn c hc_mem a ha_mem hne).resolve_right hac
          have h_ya : margin_pos prof y a :=
            (h_ext_trans c hc_mem a ha_mem hca).1 hbc
          unfold margin_pos at *; have := margin_antisymm prof a y; omega
      · -- (C,C,y): backward via h_ext_trans .2
        rw [hc_eq]; rw [hc_eq] at hbc
        exact (h_ext_trans a ha_mem b hb_mem hab).2 hbc
      · -- (C,C,C)
        exact hC_trans a ha_mem b hb_mem c hc_mem hab hbc
    have h_insert_isTC : isTC ({y} ∪ C) :=
      ⟨h_insert_sub, h_insert_ne, h_insert_tourn, h_insert_trans, h_insert_x⟩
    have h_insert_filter : ({y} ∪ C) ∈ Finset.filter isTC (Finset.powerset S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h_insert_sub, h_insert_isTC⟩
    have h_disj : Disjoint {y} C := Finset.disjoint_singleton_left.mpr hyC
    have h_card : ({y} ∪ C).card = Finset.card {y} + C.card :=
      Finset.card_union_eq_card_add_card.mpr h_disj
    have h_le := Finset.le_sup' (fun C' => C'.card) h_insert_filter
    rw [hC_max] at h_le
    rw [h_card, Finset.card_singleton] at h_le
    omega
  exact ⟨C, hC_chain, hC_x, hC_x_beats⟩


end BanksSet

/-! ## Single Transferable Vote (STV)

STV is a preferential voting system where voters rank candidates, and candidates
are elected by reaching a quota. Surplus votes transfer to next preferences, and
the candidate with fewest votes is eliminated if no one reaches quota.

Key properties:
- Satisfies proportionality
- Fails monotonicity (Doron 1979)
- Fails clone independence in general
-/

section STV

variable [DecidableEq σ] [Fintype σ]

/-- Droop quota: minimum votes needed to guarantee election.
    For n voters and k seats: floor(n / (k+1)) + 1 -/
def droop_quota (n_voters : ℕ) (n_seats : ℕ) : ℕ :=
  n_voters / (n_seats + 1) + 1

/-- Count first-preference votes for x among remaining candidates.
    A voter's first preference is their top-ranked alternative in the remaining set. -/
noncomputable def first_preferences (prof : ι → PrefOrder σ) (remaining : Finset σ) (x : σ) : ℕ :=
  haveI : DecidablePred (fun i : ι => is_best_element x remaining (prof i).rel) := Classical.decPred _
  (Finset.filter (fun i => is_best_element x remaining (prof i).rel) Finset.univ).card

/-- Result of one STV round -/
inductive stv_round_result (σ : Type*) where
  | elected (x : σ) : stv_round_result σ
  | eliminated (x : σ) : stv_round_result σ
  | complete : stv_round_result σ

/-- One step of STV: elect a candidate reaching quota, or eliminate the weakest.
    Returns the action to take for this round.
    Uses classical choice for tie-breaking. -/
noncomputable def stv_step (prof : ι → PrefOrder σ) (remaining : Finset σ)
    (already_elected : Finset σ) (quota : ℕ) (n_seats : ℕ) : stv_round_result σ := by
  classical
  if hcard : already_elected.card ≥ n_seats then exact .complete
  else if hrem : remaining = ∅ then exact .complete
  else
    have hne : remaining.Nonempty := Finset.nonempty_iff_ne_empty.mpr hrem
    let over_quota := remaining.filter (fun x => quota ≤ first_preferences prof remaining x)
    if hov : over_quota.Nonempty then
      exact .elected (Classical.choose hov)
    else
      exact .eliminated (Classical.choose hne)

/-- STV as a Social Choice Correspondence with n_seats winners.
    Iteratively applies stv_step until n_seats candidates are elected. -/
noncomputable def stv_scc (n_seats : ℕ) : SCC ι σ := fun prof S =>
  let quota := droop_quota (Fintype.card ι) n_seats
  let rec loop (remaining : Finset σ) (elected : Finset σ) (fuel : ℕ) : Finset σ :=
    match fuel with
    | 0 => elected
    | fuel' + 1 =>
      match stv_step prof remaining elected quota n_seats with
      | .elected x =>
        if elected.card < n_seats then
          loop (remaining.erase x) (insert x elected) fuel'
        else
          elected
      | .eliminated x => loop (remaining.erase x) elected fuel'
      | .complete => elected
  loop S ∅ (2 * S.card + 1)

end STV

end SocialChoice

