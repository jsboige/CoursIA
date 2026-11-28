/-
  Gibbard-Satterthwaite: hypothesis witnesses (T5, #26945)
  =====================================================

  English mirror of `SocialChoice/GibbardSatterthwaite.lean` (FR-first
  canonical). Only docstrings and comments differ; statements and proofs
  are byte-identical (i18n convention #4980).

  The Gibbard-Satterthwaite theorem (1973): any resolute social choice
  rule, on a domain of at least three outcomes, that is **onto** and
  **strategy-proof**, is **dictatorial**. The criticized text (#26945,
  l.109) invokes this theorem against a "judge that decides in a
  repeatable and mechanical way" without stating its hypotheses. Each
  one is indispensable:

  * **surjectivity** (every outcome is reached by some profile);
  * **universal domain** (every ordinal preference is an admissible
    ballot).

  This module does NOT re-prove the theorem (it is cited): it proves its
  **witnesses** — as the T5 tranche of #26945 requests, as theorems:

  1. `constantSCF`: the constant rule is strategy-proof, NOT onto, and
     non-dictatorial. It kills the surjectivity hypothesis.
  2. `medianReportRule`: the median of peak-ballots is strategy-proof
     (Moulin's theorem) and non-dictatorial, but its domain is NOT
     universal — strategy-proofness is only proved for TRUE single-peaked
     preferences. It kills the universal-domain hypothesis.

  Each witness exhibits the hypothesis the theorem needs. The final
  reading (prose section) draws the conclusion for the "judge" of the
  text.

  Proof strategy: the countings reuse the organs of
  `SocialChoice_en.SortedListCounting` (bounds `countP_lt_kth_le_half`,
  `countP_le_kth_ge_half_succ`, `countP_ge_kth_ge_half_succ`) and the
  filter ↔ sorted-list bridge `finset_filter_lt_card_eq_toList_map_countP`,
  already consumed by `Voting_en.median_voter_theorem_strict`. The median
  is characterized by its countings (`sorted_get_of_counts`), then the
  monotonicity of the median in each ballot (`median_peak_le_of_le`,
  `median_peak_ge_of_ge`) yields Moulin's theorem by trichotomy.
-/

import SocialChoice.Basic_en
import SocialChoice.Voting_en
import SocialChoice.SortedListCounting_en

/-! ## The framework: resolute social choice rule (SCF) -/

namespace SocialChoice_en

section Framework

variable {ι σ : Type*}

/-- Resolute social choice function: a complete profile of ordinal
preferences determines a unique outcome. This is the object of the
Gibbard-Satterthwaite theorem. -/
def SCF := (ι → PrefOrder σ) → σ

/-- `f` is **onto**: every outcome is the result of some profile. This is
the "onto" hypothesis of Gibbard-Satterthwaite (which also requires at
least three outcomes — that is a condition on `σ`, not on `f`). -/
def scf_onto (f : @SCF ι σ) : Prop :=
  ∀ a : σ, ∃ prof : ι → PrefOrder σ, f prof = a

/-- `f` is **strategy-proof** (non-manipulable): no voter can, by changing
their own ballot alone, obtain a strictly preferred outcome — strictly
preferred according to their TRUE preferences, those of the starting
profile, not those of the reported ballot. -/
def scf_strategy_proof (f : @SCF ι σ) : Prop :=
  ∀ (prof prof' : ι → PrefOrder σ) (i : ι), (∀ j, j ≠ i → prof' j = prof j) →
    ¬ P (prof i).rel (f prof') (f prof)

variable [LinearOrder σ]

/-- `d` is a **dictator** for `f`: the outcome is always the peak of
`d`'s preferences. -/
def scf_dictator (f : @SCF ι σ) (d : ι) : Prop :=
  ∀ prof : ι → PrefOrder σ, is_peak (prof d).rel (f prof)

/-- `f` is **dictatorial**: a dictator exists. This is the (undesired)
conclusion of Gibbard-Satterthwaite. -/
def scf_dictatorial (f : @SCF ι σ) : Prop :=
  ∃ d : ι, scf_dictator f d

end Framework

/-! ## Witness A — the constant rule (kills surjectivity)

  The constant rule `constantSCF a` always returns `a`. It is trivially
  strategy-proof (the outcome depends on no ballot) and non-dictatorial
  (no ballot influences the outcome) — but it is not onto as soon as an
  outcome other than `a` exists. Gibbard-Satterthwaite does not apply:
  the onto hypothesis is essential. -/

section ConstantWitness

variable {ι σ : Type*}

/-- Totally indifferent order: every pair of outcomes is related. Serves
as the witness profile for non-dictatorship of the constant rule: nobody
has a strict preference, so nobody can be a peak. -/
def indifferentOrder : PrefOrder σ where
  rel _ _ := True
  refl _ := True.intro
  total _ _ := Or.inl True.intro
  trans _ _ _ _ _ := True.intro

/-- **Witness A (T5 #26945)**: the constant rule that always returns `a`. -/
def constantSCF (a : σ) : @SCF ι σ := fun _prof => a

/-- **Witness A (T5 #26945)**: the constant rule is strategy-proof — the
outcome does not depend on ballots, so no lie changes it; and a strict
preference for the outcome against itself is impossible (`P` is
irreflexive as soon as the relation is reflexive). -/
theorem constantSCF_strategy_proof (a : σ) :
    scf_strategy_proof (ι := ι) (constantSCF a) := by
  intro prof prof' i _hsame h
  exact h.2 ((prof i).refl a)

/-- **Witness A (T5 #26945)**: the constant rule is NOT onto as soon as a
second outcome exists. This is the hypothesis this witness isolates:
without surjectivity, strategy-proofness and non-dictatorship are
trivial. -/
theorem constantSCF_not_onto (a b : σ) (h : a ≠ b) :
    ¬ scf_onto (ι := ι) (constantSCF a) := by
  intro honto
  obtain ⟨prof, hprof⟩ := honto b
  exact h hprof

variable [LinearOrder σ] [Nontrivial σ]

/-- **Witness A (T5 #26945)**: the constant rule is NOT dictatorial. On
the uniformly indifferent profile, no outcome is anybody's peak: a
dictator would have to have `a` as their peak, yet `a` is nobody's strict
peak in the indifferent order. -/
theorem constantSCF_not_dictator (a : σ) :
    ¬ scf_dictatorial (ι := ι) (constantSCF a) := by
  rintro ⟨d, hd⟩
  have hispeak := hd (fun _ => indifferentOrder)
  obtain ⟨b, c, hbc⟩ := exists_pair_ne (α := σ)
  have hba : b ≠ a ∨ c ≠ a := by
    by_contra hcon
    have hb : b = a := not_not.mp (fun h => hcon (Or.inl h))
    have hc : c = a := not_not.mp (fun h => hcon (Or.inr h))
    exact hbc (hb.trans hc.symm)
  rcases hba with hne | hne
  · exact (hispeak b hne).2 True.intro
  · exact (hispeak c hne).2 True.intro

end ConstantWitness

/-! ## Identification: the median by its countings

  Counting lemmas specific to this module: characterization of the
  element at index `k` of a sorted list by its counting bounds (the
  converse of the `SortedListCounting` organs), then specialization to
  the median. -/

section MedianCounting

variable {σ : Type*} [LinearOrder σ]

/-- **Identification (converse of the bounds)**: in a sorted list, if at
most `k` elements are strictly below `x` and at least `k + 1` are less
than or equal, then the element at index `k` IS `x`. This is the
converse of `countP_lt_kth_le_half` + `countP_le_kth_ge_half_succ`. -/
theorem sorted_get_of_counts {l : List σ} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < l.length) {x : σ}
    (hlt : l.countP (fun z => decide (z < x)) ≤ k)
    (hle : k + 1 ≤ l.countP (fun z => decide (z ≤ x))) :
    l[k] = x := by
  rcases lt_trichotomy (l[k]) x with h | h | h
  · -- case l[k] < x: the first k + 1 elements are < x, contradicting hlt
    exfalso
    have hprefix : (l.take (k + 1)).countP (fun z => decide (z < x)) = k + 1 := by
      have hall : ∀ y ∈ l.take (k + 1), decide (y < x) = true := by
        intro y hy
        rcases List.mem_iff_getElem.mp hy with ⟨j, hj, rfl⟩
        have hj_l : j < l.length := by
          have hj' := hj
          rw [List.length_take] at hj'
          omega
        have hyj : (l.take (k + 1))[j] = l[j] := List.getElem_take (h := hj)
        have hgoal : decide (l[j] < x) = true := by
          rw [decide_eq_true]
          by_cases hj_eq : j = k
          · subst hj_eq; exact h
          · rw [List.length_take] at hj
            exact lt_of_le_of_lt
              (List.pairwise_iff_getElem.mp hsort j k hj_l hk (by omega)) h
        exact (congrArg (fun v => decide (v < x)) hyj).trans hgoal
      rw [List.countP_eq_length.mpr hall, List.length_take, Nat.min_eq_left (by omega)]
    have hmono : (l.take (k + 1)).countP (fun z => decide (z < x)) ≤
        l.countP (fun z => decide (z < x)) := by
      conv_rhs => rw [← List.take_append_drop (k + 1) l]
      rw [List.countP_append]
      omega
    omega
  · exact h
  · -- case x < l[k]: no element at index ≥ k is ≤ x, contradicting hle
    exfalso
    have hdrop : (l.drop k).countP (fun z => decide (z ≤ x)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro y hy
      rcases List.mem_iff_getElem.mp hy with ⟨j, hj, rfl⟩
      rw [List.getElem_drop]
      have hj_kj : k + j < l.length := by
        have hj' := hj
        rw [List.length_drop] at hj'
        omega
      have hge : l[k] ≤ l[k + j] := by
        by_cases hj0 : j = 0
        · subst hj0; simp
        · exact List.pairwise_iff_getElem.mp hsort k (k + j) hk hj_kj (by omega)
      intro hle_j
      have hxl : l[k + j] ≤ x := of_decide_eq_true hle_j
      exact lt_irrefl x (lt_of_lt_of_le h (le_trans hge hxl))
    have htake : (l.take k).countP (fun z => decide (z ≤ x)) ≤ k := by
      calc (l.take k).countP (fun z => decide (z ≤ x)) ≤ (l.take k).length :=
          List.countP_le_length
        _ = min k l.length := List.length_take
        _ ≤ k := min_le_left _ _
    have hsplit : l.countP (fun z => decide (z ≤ x)) =
        (l.take k).countP (fun z => decide (z ≤ x)) +
          (l.drop k).countP (fun z => decide (z ≤ x)) := by
      conv_lhs => rw [← List.take_append_drop k l]
      rw [List.countP_append]
    omega

end MedianCounting

/-! ## Witness B — the median of peak-ballots (kills universal domain)

  Each voter announces an outcome (their peak-ballot); the result is the
  median of the ballots. Moulin's theorem (1980): on the single-peaked
  domain, this rule is strategy-proof. And it is not dictatorial. But
  strategy-proofness REQUIRES the domain: outside single-peakedness, it
  fails (a polarized voter can pull the median toward their camp). -/

section MedianRule

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder σ]

/-- Bridge: the cardinal "ballots strictly below `x`" reads as a `countP`
on the ballot list (before sorting, hence without `mergeSort`). -/
private theorem filter_lt_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => p j < x) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (z < x)) := by
  rw [show (Finset.filter (fun j => p j < x) Finset.univ) =
      (Finset.filter (fun j => decide (p j < x) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (z < x))]

/-- Twin bridge for "ballots less than or equal to `x`". -/
private theorem filter_le_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => p j ≤ x) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (z ≤ x)) := by
  rw [show (Finset.filter (fun j => p j ≤ x) Finset.univ) =
      (Finset.filter (fun j => decide (p j ≤ x) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (z ≤ x))]

/-- Bridge "ballots strictly below `x`" ↔ `countP` on the sorted list
(sorting preserves countings: `List.Perm.countP_eq`). -/
private theorem countP_sorted_lt (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (z < x)) =
      (Finset.filter (fun j => p j < x) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (z < x))]
  exact (filter_lt_card p x).symm

/-- Twin bridge "≤ x" on the sorted list. -/
private theorem countP_sorted_le (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (z ≤ x)) =
      (Finset.filter (fun j => p j ≤ x) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (z ≤ x))]
  exact (filter_le_card p x).symm

/-- Bridge "ballots greater than or equal to `x`" (dual form, for the
downward monotonicity). -/
private theorem filter_ge_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => x ≤ p j) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (x ≤ z)) := by
  rw [show (Finset.filter (fun j => x ≤ p j) Finset.univ) =
      (Finset.filter (fun j => decide (x ≤ p j) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (x ≤ z))]

/-- Twin bridge "x ≤ z" on the sorted list. -/
private theorem countP_sorted_ge (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (x ≤ z)) =
      (Finset.filter (fun j => x ≤ p j) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (x ≤ z))]
  exact (filter_ge_card p x).symm

variable [Inhabited σ]

/-- Countings determine the median: if at most `n / 2` ballots are
strictly below `x` and at least `n / 2 + 1` are less than or equal to it,
then the median equals `x` (identification + bridges + counting organs). -/
private theorem median_eq_of_filter_bounds (p : ι → σ) {x : σ}
    (hlt : (Finset.filter (fun j => p j < x) Finset.univ).card ≤ Fintype.card ι / 2)
    (hle : Fintype.card ι / 2 + 1 ≤ (Finset.filter (fun j => p j ≤ x) Finset.univ).card) :
    median_peak p = x := by
  set l := sorted_peaks_list p with hl_def
  have hl_len : l.length = Fintype.card ι := by
    simp [l, sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hl_pos : 0 < l.length := by
    have hpos_filter : 0 < (Finset.filter (fun j => p j ≤ x) Finset.univ).card := by omega
    calc 0 < (Finset.filter (fun j => p j ≤ x) Finset.univ).card := hpos_filter
      _ ≤ Fintype.card ι := Finset.card_le_card (Finset.filter_subset _ _)
      _ = l.length := hl_len.symm
  have hn : l.length / 2 < l.length := Nat.div_lt_self hl_pos (by omega)
  have hsorted : l.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map p)
  have hmid : median_peak p = l[l.length / 2] := by
    unfold median_peak sorted_peaks_list
    show l.getD (l.length / 2) default = l[l.length / 2]
    simp [List.getD, hn]
  have hltP : l.countP (fun z => decide (z < x)) ≤ l.length / 2 := by
    rw [show l.countP (fun z => decide (z < x)) =
        (Finset.filter (fun j => p j < x) Finset.univ).card from countP_sorted_lt p x, hl_len]
    exact hlt
  have hleP : l.length / 2 + 1 ≤ l.countP (fun z => decide (z ≤ x)) := by
    rw [show l.countP (fun z => decide (z ≤ x)) =
        (Finset.filter (fun j => p j ≤ x) Finset.univ).card from countP_sorted_le p x, hl_len]
    exact hle
  rw [hmid]
  exact sorted_get_of_counts hsorted hn hltP hleP

/-- Organic "left half" bound: at most `n / 2` ballots strictly below the
median. -/
private theorem median_filter_bounds_lt (p : ι → σ) (hnp : Nonempty ι) :
    (Finset.filter (fun j => p j < median_peak p) Finset.univ).card ≤
      Fintype.card ι / 2 := by
  set l := sorted_peaks_list p with hl_def
  have hl_len : l.length = Fintype.card ι := by
    simp [l, sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hn : l.length / 2 < l.length :=
    Nat.div_lt_self (by rw [hl_len]; exact Fintype.card_pos_iff.mpr hnp) (by omega)
  have hsorted : l.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map p)
  have hmid : median_peak p = l[l.length / 2] := by
    unfold median_peak sorted_peaks_list
    show l.getD (l.length / 2) default = l[l.length / 2]
    simp [List.getD, hn]
  rw [← countP_sorted_lt p (median_peak p), hmid, ← hl_def, ← hl_len]
  exact SortedListCounting.countP_lt_kth_le_half hsorted hn

/-- Organic "enlarged left half" bound: at least `n / 2 + 1` ballots less
than or equal to the median. -/
private theorem median_filter_bounds_le (p : ι → σ) (hnp : Nonempty ι) :
    Fintype.card ι / 2 + 1 ≤
      (Finset.filter (fun j => p j ≤ median_peak p) Finset.univ).card := by
  set l := sorted_peaks_list p with hl_def
  have hl_len : l.length = Fintype.card ι := by
    simp [l, sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hn : l.length / 2 < l.length :=
    Nat.div_lt_self (by rw [hl_len]; exact Fintype.card_pos_iff.mpr hnp) (by omega)
  have hsorted : l.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map p)
  have hmid : median_peak p = l[l.length / 2] := by
    unfold median_peak sorted_peaks_list
    show l.getD (l.length / 2) default = l[l.length / 2]
    simp [List.getD, hn]
  rw [← countP_sorted_le p (median_peak p), hmid, ← hl_def, ← hl_len]
  exact SortedListCounting.countP_le_kth_ge_half_succ hsorted hn

/-- **Upward monotonicity of the median**: if voter `i` replaces their
ballot `peaks i` by a larger `v` (others unchanged), the median does not
decrease.

Proof by counting: if it decreased (`m' < m`), the `k + 1` ballots
`≤ m'` would be `< m`; yet the ballots `< m` can only increase when
replacing `peaks i` by `v ≥ peaks i` (the new ballot is `< m` only if
the old one was), and there were at most `k` of them. Contradiction. -/
theorem median_peak_le_of_le {peaks : ι → σ} {i : ι} {v : σ}
    (hle : peaks i ≤ v) :
    median_peak peaks ≤ median_peak (Function.update peaks i v) := by
  by_contra hcon
  have hlt : median_peak (Function.update peaks i v) < median_peak peaks :=
    lt_of_not_ge hcon
  set l := sorted_peaks_list peaks with hl_def
  set l' := sorted_peaks_list (Function.update peaks i v) with hl'_def
  have hl_len : l.length = Fintype.card ι := by
    simp [l, sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hl'_len : l'.length = Fintype.card ι := by
    simp [l', sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hl_pos : 0 < l.length := by rw [hl_len]; exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hn : l.length / 2 < l.length := Nat.div_lt_self hl_pos (by omega)
  have hl'_pos : 0 < l'.length := by rw [hl'_len]; exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hn' : l'.length / 2 < l'.length := Nat.div_lt_self hl'_pos (by omega)
  have hsorted : l.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map peaks)
  have hsorted' : l'.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·))
      (Finset.univ.toList.map (Function.update peaks i v))
  have hm'_eq : median_peak (Function.update peaks i v) = l'[l'.length / 2] := by
    unfold median_peak sorted_peaks_list
    show l'.getD (l'.length / 2) default = l'[l'.length / 2]
    simp [l', List.getD, hn']
  -- new side: at least k + 1 ballots ≤ m'
  have hnew : l'.length / 2 + 1 ≤
      l'.countP (fun z => decide (z ≤ median_peak (Function.update peaks i v))) := by
    rw [hm'_eq]
    exact SortedListCounting.countP_le_kth_ge_half_succ hsorted' hn'
  have hnew_card : l'.countP (fun z => decide (z ≤ median_peak (Function.update peaks i v))) =
      (Finset.filter (fun j => Function.update peaks i v j ≤
        median_peak (Function.update peaks i v)) Finset.univ).card := by
    rw [hm'_eq]
    exact countP_sorted_le (Function.update peaks i v) _
  -- old side: at most k ballots < m
  have hold : (Finset.filter (fun j => peaks j < median_peak peaks) Finset.univ).card ≤
      l.length / 2 := by
    rw [← countP_sorted_lt peaks (median_peak peaks)]
    have hmid : median_peak peaks = l[l.length / 2] := by
      unfold median_peak sorted_peaks_list
      show l.getD (l.length / 2) default = l[l.length / 2]
      simp [List.getD, hn]
    rw [hmid]
    exact SortedListCounting.countP_lt_kth_le_half hsorted hn
  -- inclusion 1: ≤ m' implies < m (since m' < m)
  have hsub1 : (Finset.filter (fun j => Function.update peaks i v j ≤
        median_peak (Function.update peaks i v)) Finset.univ).card ≤
      (Finset.filter (fun j => Function.update peaks i v j < median_peak peaks)
        Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_le_of_lt hj hlt
  -- inclusion 2: a deviated ballot < m was there only if the old one was (v ≥ peaks i)
  have hsub2 : (Finset.filter (fun j => Function.update peaks i v j < median_peak peaks)
        Finset.univ).card ≤
      (Finset.filter (fun j => peaks j < median_peak peaks) Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      exact lt_of_le_of_lt hle hj
    · rw [Function.update_of_ne hji] at hj
      exact hj
  rw [hl'_len] at hnew
  omega

/-- **Downward monotonicity of the median**: if voter `i` replaces their
ballot `peaks i` by a smaller `v` (others unchanged), the median does not
increase. Proof by counting, mirror of `median_peak_le_of_le`: if it
increased (`m < m'`), the `n - k` ballots `≥ m'` would be `> m`; yet the
ballots `> m` can only increase when replacing `peaks i` by `v ≤ peaks i`,
and there were at most `n - k - 1` of them (complement of the bound
`k + 1 ≤ #{≤ m}`). Contradiction. -/
theorem median_peak_ge_of_ge {peaks : ι → σ} {i : ι} {v : σ}
    (hge : v ≤ peaks i) :
    median_peak (Function.update peaks i v) ≤ median_peak peaks := by
  by_contra hcon
  have hlt : median_peak peaks < median_peak (Function.update peaks i v) :=
    lt_of_not_ge hcon
  set l := sorted_peaks_list peaks with hl_def
  set l' := sorted_peaks_list (Function.update peaks i v) with hl'_def
  have hl_len : l.length = Fintype.card ι := by
    simp [l, sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hl'_len : l'.length = Fintype.card ι := by
    simp [l', sorted_peaks_list, List.length_mergeSort, List.length_map, Finset.length_toList]
  have hl_pos : 0 < l.length := by rw [hl_len]; exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hn : l.length / 2 < l.length := Nat.div_lt_self hl_pos (by omega)
  have hl'_pos : 0 < l'.length := by rw [hl'_len]; exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hn' : l'.length / 2 < l'.length := Nat.div_lt_self hl'_pos (by omega)
  have hsorted : l.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·)) (Finset.univ.toList.map peaks)
  have hsorted' : l'.Pairwise (· ≤ ·) :=
    List.pairwise_mergeSort' (r := (· ≤ ·))
      (Finset.univ.toList.map (Function.update peaks i v))
  have hm'_eq : median_peak (Function.update peaks i v) = l'[l'.length / 2] := by
    unfold median_peak sorted_peaks_list
    show l'.getD (l'.length / 2) default = l'[l'.length / 2]
    simp [l', List.getD, hn']
  -- new side: at least n - k ballots ≥ m'
  have hnew : l'.length - l'.length / 2 ≤
      l'.countP (fun z => decide (median_peak (Function.update peaks i v) ≤ z)) := by
    rw [hm'_eq]
    exact SortedListCounting.countP_ge_kth_ge_half_succ hsorted' hn'
  have hnew_card : l'.countP (fun z => decide (median_peak (Function.update peaks i v) ≤ z)) =
      (Finset.filter (fun j => median_peak (Function.update peaks i v) ≤
        Function.update peaks i v j) Finset.univ).card :=
    countP_sorted_ge (Function.update peaks i v) (median_peak (Function.update peaks i v))
  -- complementarity: {> m} and {≤ m} partition the electorate
  have hcomp : (Finset.filter (fun j => median_peak peaks < peaks j) Finset.univ).card +
      (Finset.filter (fun j => peaks j ≤ median_peak peaks) Finset.univ).card =
      Fintype.card ι := by
    have hflip : (Finset.filter (fun j => median_peak peaks < peaks j) Finset.univ) =
        (Finset.filter (fun j => ¬ (peaks j ≤ median_peak peaks)) Finset.univ) := by
      apply Finset.filter_congr
      intro j _
      exact (not_le).symm
    rw [hflip, add_comm,
        Finset.card_filter_add_card_filter_not
          (s := Finset.univ) (p := fun j => peaks j ≤ median_peak peaks),
        Finset.card_univ]
  -- old side: at least k + 1 ballots ≤ m
  have hold : l.length / 2 + 1 ≤
      (Finset.filter (fun j => peaks j ≤ median_peak peaks) Finset.univ).card := by
    rw [← countP_sorted_le peaks (median_peak peaks)]
    have hmid : median_peak peaks = l[l.length / 2] := by
      unfold median_peak sorted_peaks_list
      show l.getD (l.length / 2) default = l[l.length / 2]
      simp [List.getD, hn]
    rw [hmid]
    exact SortedListCounting.countP_le_kth_ge_half_succ hsorted hn
  -- inclusion 1: ≥ m' implies > m (since m < m')
  have hsub1 : (Finset.filter (fun j => median_peak (Function.update peaks i v) ≤
        Function.update peaks i v j) Finset.univ).card ≤
      (Finset.filter (fun j => median_peak peaks <
        Function.update peaks i v j) Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_lt_of_le hlt hj
  -- inclusion 2: a deviated ballot > m was there only if the old one was (v ≤ peaks i)
  have hsub2 : (Finset.filter (fun j => median_peak peaks <
        Function.update peaks i v j) Finset.univ).card ≤
      (Finset.filter (fun j => median_peak peaks < peaks j) Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hji : j = i
    · subst hji
      rw [Function.update_self] at hj
      exact lt_of_lt_of_le hj hge
    · rw [Function.update_of_ne hji] at hj
      exact hj
  rw [hl'_len] at hnew
  omega

/-- **Witness B (T5 #26945): the median-of-peak-ballots rule**
(Black's rule restricted to ballots, Moulin's theorem). Each voter
announces an outcome; the result is the median (position `n / 2` of the
sorted list, lower median).

WARNING — the domain is NOT universal: strategy-proofness is guaranteed
only when the TRUE preferences are single-peaked. This is the domain
hypothesis that Gibbard-Satterthwaite forbids omitting. -/
noncomputable def medianReportRule (reports : ι → σ) : σ :=
  median_peak reports

/-- **Witness B (T5 #26945) — Moulin's theorem (1980)**: the median rule
is strategy-proof on the single-peaked domain. A voter whose true
preferences are single-peaked with peak `reports i` (their sincere
ballot) can never obtain strictly better by changing their own ballot
alone.

Sketch: the median is monotone in each ballot (`median_peak_le_of_le`,
`median_peak_ge_of_ge`). If the voter deviates downward (`v ≤ reports
i`), the outcome does not increase; if it strictly decreases then the
peak was above the median and left-of-peak monotonicity gives
`R m m'` — which rules out the strict preference `P m' m`. Symmetric
case upward. Unchanged outcome: a strict preference of self against self
is impossible (`P` irreflexive). -/
theorem medianReport_strategy_proof
    (reports : ι → σ) (i : ι) (v : σ) (prof : ι → PrefOrder σ)
    (hsp : single_peaked (prof i).rel (reports i)) :
    ¬ P (prof i).rel (medianReportRule (Function.update reports i v))
        (medianReportRule reports) := by
  classical
  by_cases hle : v ≤ reports i
  · -- lower (or equal) lie: the median does not increase
    have hbr : medianReportRule (Function.update reports i v) ≤ medianReportRule reports :=
      median_peak_ge_of_ge hle
    rcases lt_or_eq_of_le hbr with hlt' | heq'
    · -- m' < m: then the peak was ≥ m (otherwise the median would be unchanged),
      -- and left-of-peak monotonicity gives R m m', which kills P m' m
      have hpim : medianReportRule reports ≤ reports i := by
        by_contra hcon
        have hpilt : reports i < medianReportRule reports := lt_of_not_ge hcon
        have hlt_eq : (Finset.filter (fun j =>
              Function.update reports i v j < medianReportRule reports) Finset.univ).card =
            (Finset.filter (fun j => reports j < medianReportRule reports)
              Finset.univ).card := by
          have hfe : (Finset.filter (fun j =>
                Function.update reports i v j < medianReportRule reports) Finset.univ) =
              (Finset.filter (fun j => reports j < medianReportRule reports)
                Finset.univ) := by
            apply Finset.filter_congr
            intro j _
            rw [Function.update_apply]
            by_cases hji : j = i
            · subst hji
              have hv : v < medianReportRule reports :=
                lt_of_le_of_lt hle hpilt
              simp [hpilt, hv]
            · simp [hji]
          rw [hfe]
        have hle_sub : (Finset.filter (fun j => reports j ≤ medianReportRule reports)
              Finset.univ).card ≤
            (Finset.filter (fun j => Function.update reports i v j ≤
              medianReportRule reports) Finset.univ).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
            exact le_of_lt (lt_of_le_of_lt hle hpilt)
          · rw [Function.update_of_ne hji]
            exact hj
        have hb := median_filter_bounds_lt reports ⟨i⟩
        have hle_b := median_filter_bounds_le reports ⟨i⟩
        have hmid' : medianReportRule (Function.update reports i v) =
            medianReportRule reports :=
          median_eq_of_filter_bounds (Function.update reports i v)
            (x := medianReportRule reports)
            (by rw [hlt_eq]; exact hb)
            (le_trans hle_b hle_sub)
        rw [hmid'] at hlt'
        exact lt_irrefl _ hlt'
      intro h
      exact h.2 (hsp.2.1 _ _ hbr hpim)
    · -- unchanged outcome: P of self against self impossible
      rw [heq']
      intro h
      exact h.2 ((prof i).refl _)
  · -- higher lie: the median does not decrease
    have hlt : reports i < v := lt_of_not_ge hle
    have hbr : medianReportRule reports ≤ medianReportRule (Function.update reports i v) :=
      median_peak_le_of_le (le_of_lt hlt)
    rcases lt_or_eq_of_le hbr with hlt' | heq'
    · -- m < m': then the peak was ≤ m (otherwise the median would be unchanged),
      -- and right-of-peak monotonicity gives R m m', which kills P m' m
      have hpim : reports i ≤ medianReportRule reports := by
        by_contra hcon
        have hpigt : medianReportRule reports < reports i := lt_of_not_ge hcon
        have hlt_eq : (Finset.filter (fun j =>
              Function.update reports i v j < medianReportRule reports) Finset.univ).card =
            (Finset.filter (fun j => reports j < medianReportRule reports)
              Finset.univ).card := by
          have hfe : (Finset.filter (fun j =>
                Function.update reports i v j < medianReportRule reports) Finset.univ) =
              (Finset.filter (fun j => reports j < medianReportRule reports)
                Finset.univ) := by
            apply Finset.filter_congr
            intro j _
            rw [Function.update_apply]
            by_cases hji : j = i
            · subst hji
              have hv : ¬ (v < medianReportRule reports) := fun hc =>
                lt_irrefl _ (lt_trans (lt_trans hpigt hlt) hc)
              have hri : ¬ (reports j < medianReportRule reports) := fun hc =>
                lt_irrefl _ (lt_trans hpigt hc)
              simp [hv, hri]
            · simp [hji]
          rw [hfe]
        have hle_eq : (Finset.filter (fun j =>
              Function.update reports i v j ≤ medianReportRule reports) Finset.univ).card =
            (Finset.filter (fun j => reports j ≤ medianReportRule reports)
              Finset.univ).card := by
          have hfe : (Finset.filter (fun j =>
                Function.update reports i v j ≤ medianReportRule reports) Finset.univ) =
              (Finset.filter (fun j => reports j ≤ medianReportRule reports)
                Finset.univ) := by
            apply Finset.filter_congr
            intro j _
            rw [Function.update_apply]
            by_cases hji : j = i
            · subst hji
              have hv : ¬ (v ≤ medianReportRule reports) := fun hc =>
                lt_irrefl _ (lt_of_le_of_lt hc (lt_trans hpigt hlt))
              have hri : ¬ (reports j ≤ medianReportRule reports) := fun hc =>
                lt_irrefl _ (lt_of_lt_of_le hpigt hc)
              simp [hv, hri]
            · simp [hji]
          rw [hfe]
        have hb := median_filter_bounds_lt reports ⟨i⟩
        have hle_b := median_filter_bounds_le reports ⟨i⟩
        have hmid' : medianReportRule (Function.update reports i v) =
            medianReportRule reports :=
          median_eq_of_filter_bounds (Function.update reports i v)
            (x := medianReportRule reports)
            (by rw [hlt_eq]; exact hb)
            (by rw [hle_eq]; exact hle_b)
        rw [hmid'] at hlt'
        exact lt_irrefl _ hlt'
      intro h
      exact h.2 (hsp.2.2 _ _ hpim hbr)
    · -- unchanged outcome: P of self against self impossible
      rw [← heq']
      intro h
      exact h.2 ((prof i).refl _)

/-- **Witness B (T5 #26945, continued): the median rule is not
dictatorial.** No voter systematically obtains their own ballot as the
outcome: with at least two voters and two outcomes, the profile "all
`a₁` except `d` reporting `a₀`" (with `a₀ ≠ a₁`) has median `a₁`, not
`a₀`. -/
theorem medianReport_not_dictator [Nontrivial σ]
    (hcard : 2 ≤ Fintype.card ι) :
    ¬ ∃ d : ι, ∀ reports : ι → σ, medianReportRule reports = reports d := by
  rintro ⟨d, hd⟩
  obtain ⟨a₀, a₁, hne⟩ := exists_pair_ne (α := σ)
  rcases lt_or_gt_of_ne hne with hlt01 | hgt01
  · -- case a₀ < a₁: all at a₁ except d at a₀; the median is a₁
    have hlt_card : (Finset.filter (fun j => (if j = d then a₀ else a₁) < a₁)
        Finset.univ).card = 1 := by
      have hfe : (Finset.filter (fun j => (if j = d then a₀ else a₁) < a₁)
          Finset.univ) = {d} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
        by_cases hjd : j = d
        · rw [hjd, if_pos rfl]
          exact ⟨fun _ => rfl, fun _ => hlt01⟩
        · rw [if_neg hjd]
          exact ⟨fun h => absurd h (lt_irrefl a₁), fun h => absurd h hjd⟩
      rw [hfe, Finset.card_singleton]
    have hle_card : Fintype.card ι / 2 + 1 ≤
        (Finset.filter (fun j => (if j = d then a₀ else a₁) ≤ a₁)
          Finset.univ).card := by
      have hfe : (Finset.filter (fun j => (if j = d then a₀ else a₁) ≤ a₁)
          Finset.univ) = Finset.univ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hjd : j = d
        · rw [hjd, if_pos rfl]
          exact iff_of_true (le_of_lt hlt01) trivial
        · rw [if_neg hjd]
          exact iff_of_true (le_refl _) trivial
      rw [hfe, Finset.card_univ]
      omega
    have hmid := median_eq_of_filter_bounds (fun j => if j = d then a₀ else a₁)
      (x := a₁) (by rw [hlt_card]; omega) hle_card
    have hres' : (fun j => if j = d then a₀ else a₁) d = a₀ := if_pos rfl
    have hres : median_peak (fun j => if j = d then a₀ else a₁) =
        (fun j => if j = d then a₀ else a₁) d := hd _
    rw [hmid, hres'] at hres
    exact (ne_of_lt hlt01) hres.symm
  · -- case a₁ < a₀: all at a₀ except d at a₁; the median is a₀
    have hlt_card : (Finset.filter (fun j => (if j = d then a₁ else a₀) < a₀)
        Finset.univ).card = 1 := by
      have hfe : (Finset.filter (fun j => (if j = d then a₁ else a₀) < a₀)
          Finset.univ) = {d} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
        by_cases hjd : j = d
        · rw [hjd, if_pos rfl]
          exact ⟨fun _ => rfl, fun _ => hgt01⟩
        · rw [if_neg hjd]
          exact ⟨fun h => absurd h (lt_irrefl a₀), fun h => absurd h hjd⟩
      rw [hfe, Finset.card_singleton]
    have hle_card : Fintype.card ι / 2 + 1 ≤
        (Finset.filter (fun j => (if j = d then a₁ else a₀) ≤ a₀)
          Finset.univ).card := by
      have hfe : (Finset.filter (fun j => (if j = d then a₁ else a₀) ≤ a₀)
          Finset.univ) = Finset.univ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hjd : j = d
        · rw [hjd, if_pos rfl]
          exact iff_of_true (le_of_lt hgt01) trivial
        · rw [if_neg hjd]
          exact iff_of_true (le_refl _) trivial
      rw [hfe, Finset.card_univ]
      omega
    have hmid := median_eq_of_filter_bounds (fun j => if j = d then a₁ else a₀)
      (x := a₀) (by rw [hlt_card]; omega) hle_card
    have hres' : (fun j => if j = d then a₁ else a₀) d = a₁ := if_pos rfl
    have hres : median_peak (fun j => if j = d then a₁ else a₀) =
        (fun j => if j = d then a₁ else a₀) d := hd _
    rw [hmid, hres'] at hres
    exact (ne_of_lt hgt01) hres.symm

end MedianRule

/-! ## Reading — what remains for the "repeatable and mechanical judge"?

  The criticized text (l.109) concludes from the Gibbard-Satterthwaite
  theorem that a "judge that decides in a repeatable and mechanical way"
  would be manipulable or dictatorial. The two witnesses above show what
  the theorem REQUIRES to say this, and what such a judge satisfies:

  * **Surjectivity**: a mechanical judge issuing verdicts over a
    vocabulary of at least three outcomes CAN be onto — nothing
    mechanically forbids it. But the constant rule (`constantSCF`) shows
    that a perfectly repeatable, strategy-proof and non-dictatorial judge
    exists as soon as one abandons surjectivity: a judge that always
    returns the same verdict is trivial to specify and to audit. The
    onto hypothesis is not free: it says the judge is *sensitive to the
    case*.

  * **Universal domain**: this is the hypothesis the text omits most
    gravely. The median (`medianReportRule`, Moulin's theorem) is
    strategy-proof and non-dictatorial ON A SINGLE-PEAKED DOMAIN: when
    the judge's "preferences" over cases are structurally constrained
    (single-peakedness: one ideal outcome, regular degradation on either
    side), the manipulation argument collapses. Yet a mechanical judge
    handles precisely a RESTRICTED and structured domain: cases subject
    to a format, a grid, a procedure. Claiming the domain "universal" to
    apply Gibbard-Satterthwaite is assuming exactly what is false of a
    real judge.

  * **Non-dictatorship**: both witnesses are NON-dictatorial
    (`constantSCF_not_dictator`, `medianReport_not_dictator`) — the
    dreaded conclusion is not an inevitable residue, it is the price of
    the TWO hypotheses taken together.

  Conclusion of the tranche: the text's argument does not fall "because
  Gibbard-Satterthwaite" — it falls because neither hypothesis of the
  theorem is established for the described judge, and each is
  contradicted by a concrete strategy-proof and non-dictatorial
  witness. -/
