/-
  Théorie du choix social — Définitions de vote
  ==============================================

  Port de chasenorman/Formalized-Voting vers Lean 4
  Original : https://github.com/chasenorman/Formalized-Voting

  Adapté au cadre SocialChoice/Basic.lean :
  - Utilise PrefOrder de Basic.lean au lieu de relations brutes
  - Utilise P (préférence stricte) et I (indifférence) de Basic.lean
  - Compatible avec Profile ι σ d'Arrow.lean

  Concepts clés :
  - Fonction de marge pour le comptage des votes par paire
  - Gagnant/perdant de Condorcet et leurs critères
  - Efficacité au sens de Pareto et monotonicité pour les correspondances
    de choix social

  Convention i18n (Option A ratifiée par ai-01, Epic #4980) :
  en-têtes de section, docstrings de définition/théorème, commentaires de
  lemme sont **français d'abord** ; le code Lean tactique (noms de tactiques,
  lemmes Mathlib, identifiants) reste en anglais, langue canonique de Lean.
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

/-! ## Fonction de marge -/

/-- Marge de x sur y dans un profil :
    |{votants préférant strictement x à y}| - |{votants préférant strictement y à x}|
    Une marge positive signifie que x bat y en comparaison par paire. -/
noncomputable def margin (prof : ι → PrefOrder σ) (x y : σ) : ℤ :=
  haveI : (i : ι) → Decidable (P (prof i).rel x y) := fun _ => Classical.dec _
  haveI : (i : ι) → Decidable (P (prof i).rel y x) := fun _ => Classical.dec _
  ((Finset.filter (fun i => P (prof i).rel x y) Finset.univ).card : ℤ) -
    ((Finset.filter (fun i => P (prof i).rel y x) Finset.univ).card : ℤ)

/-- Marge positive : x bat y en comparaison par paire -/
def margin_pos (prof : ι → PrefOrder σ) (x y : σ) : Prop :=
  0 < margin prof x y

/-! ## Concepts de Condorcet -/

/-- Gagnant de Condorcet : bat strictement toute autre alternative en
    comparaison par paire -/
def condorcet_winner (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, y ≠ x → margin_pos prof x y

/-- Perdant de Condorcet : perd strictement contre toute autre alternative -/
def condorcet_loser (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ S.card ≥ 2 ∧ ∀ y ∈ S, y ≠ x → margin_pos prof y x

/-! ## Correspondance de choix social -/

/-- Correspondance de choix social : associe à un profil et un ensemble
    d'alternatives les alternatives choisies -/
def SCC (ι σ : Type*) [Fintype ι] [DecidableEq σ] :=
  (ι → PrefOrder σ) → Finset σ → Finset σ

/-! ## Critères de vote -/

/-- Critère de Condorcet : tout gagnant de Condorcet est sélectionné -/
def condorcet_criterion (f : SCC ι σ) : Prop :=
  ∀ prof S x, condorcet_winner prof S x → x ∈ f prof S

/-- Critère du perdant de Condorcet : aucun perdant de Condorcet n'est sélectionné -/
def condorcet_loser_criterion (f : SCC ι σ) : Prop :=
  ∀ prof S x, condorcet_loser prof S x → x ∉ f prof S

/-- Efficacité au sens de Pareto : si tous les votants préfèrent x à y,
    alors y n'est pas sélectionné -/
def pareto_scc (f : SCC ι σ) : Prop :=
  ∀ prof S x y, x ∈ S → y ∈ S →
    (∀ i : ι, P (prof i).rel x y) → y ∉ f prof S

/-- Monotonie : améliorer la position de x préserve la sélection de x -/
def monotonicity (f : SCC ι σ) : Prop :=
  ∀ prof prof' S x,
    x ∈ f prof S → x ∈ S →
    (∀ i : ι, ∀ y ∈ S, P (prof i).rel x y → P (prof' i).rel x y) →
    (∀ i : ι, ∀ y ∈ S, ¬P (prof i).rel y x → ¬P (prof' i).rel y x) →
    x ∈ f prof' S

/-! ## Propriétés de la marge -/

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

/-! ## Propriétés de Condorcet -/

/-- Le gagnant de Condorcet est unique (lorsqu'il existe) -/
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

/-- Un gagnant de Condorcet ne peut pas être un perdant de Condorcet -/
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

/-! ## Unanimité et marge -/

/-- Si tous les votants préfèrent strictement x à y, la marge est positive -/
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

/-! ## Préférences à pic unique

Référence : Black (1948), "On the Rationale of Group Decision-making"

Un classement de préférences sur un ensemble linéairement ordonné est à pic
unique s'il existe une alternative préférée de manière unique (le pic) et
les préférences décroissent monotoniquement en s'éloignant du pic dans les
deux directions.
-/

section SinglePeaked

variable [LinearOrder σ]

/-- Le pic d'une relation de préférence : l'unique élément strictement préféré -/
def is_peak (R : σ → σ → Prop) (p : σ) : Prop :=
  ∀ x, x ≠ p → P R p x

/-- R est à pic unique de pic p sur un ensemble linéairement ordonné.
    1. p est le pic (strictement préféré à tout le reste)
    2. À gauche du pic : plus proche du pic est faiblement préféré (a ≤ b ≤ p → R b a)
    3. À droite du pic : plus proche du pic est faiblement préféré (p ≤ a ≤ b → R a b) -/
def single_peaked (R : σ → σ → Prop) (p : σ) : Prop :=
  is_peak R p ∧
  (∀ a b, a ≤ b → b ≤ p → R b a) ∧
  (∀ a b, p ≤ a → a ≤ b → R a b)

/-- Le pic est unique -/
theorem single_peaked_peak_unique {R : σ → σ → Prop} {p q : σ}
    (hsp : single_peaked R p) (hsq : single_peaked R q) (hne : p ≠ q) : False := by
  have hPpq : P R p q := hsp.1 q hne.symm
  have hPqp : P R q p := hsq.1 p hne
  exact hPpq.2 hPqp.1

/-- À pic unique implique que le pic est le meilleur élément (sous Reflexive R) -/
theorem single_peaked_peak_best {R : σ → σ → Prop} {p : σ} {S : Finset σ}
    (hrefl : Reflexive R) (hsp : single_peaked R p) (hpS : p ∈ S) :
    is_best_element p S R := by
  intro y hy
  by_cases heq : y = p
  · subst heq; exact hrefl y
  · exact (hsp.1 y heq).1

/-- Un profil est à pic unique si chaque votant a des préférences à pic unique -/
def single_peaked_profile (prof : ι → PrefOrder σ) (peaks : ι → σ) : Prop :=
  ∀ i : ι, single_peaked (prof i).rel (peaks i)

/-- R est **strictement** à pic unique de pic p sur un ensemble
    linéairement ordonné. Renforce `single_peaked` avec monotonie stricte
    de chaque côté du pic, éliminant l'indifférence entre alternatives
    distinctes du même côté.

    C'est l'hypothèse nécessaire pour obtenir un gagnant de Condorcet
    *strict* via `margin_pos` (marge positive), par opposition à la
    garantie faible `margin ≥ 0` de `single_peaked` seul.

    Concretely:
    - `a < b ≤ p` implies `P R b a` (strictly prefer b to a, left of peak)
    - `p ≤ a < b` implies `P R a b` (strictly prefer a to b, right of peak) -/
def strictly_single_peaked (R : σ → σ → Prop) (p : σ) : Prop :=
  single_peaked R p ∧
  (∀ a b, a < b → b ≤ p → P R b a) ∧
  (∀ a b, p ≤ a → a < b → P R a b)

/-- Un profil est strictement à pic unique si chaque votant a des
    préférences strictement à pic unique. C'est l'hypothèse standard sous
    laquelle le théorème du votant médian donne un *gagnant de Condorcet*
    (marge positive) plutôt qu'un simple gagnant faible de Condorcet
    (marge non négative). -/
def strictly_single_peaked_profile (prof : ι → PrefOrder σ) (peaks : ι → σ) : Prop :=
  ∀ i : ι, strictly_single_peaked (prof i).rel (peaks i)

set_option linter.unusedSectionVars false in
/-- Un profil strictement à pic unique est en particulier à pic unique. -/
theorem strictly_single_peaked_profile.to_single_peaked
    {prof : ι → PrefOrder σ} {peaks : ι → σ}
    (h : strictly_single_peaked_profile prof peaks) :
    single_peaked_profile prof peaks :=
  fun i => (h i).1

/-! ## Théorème du votant médian (Black 1948)

Pour un nombre impair de votants avec des préférences à pic unique sur un
ensemble linéairement ordonné, le pic médian (l'élément du milieu des pics
triés) est un gagnant de Condorcet sous règle majoritaire.

Esquisse de preuve :
- Pour tout y < médiane : strictement plus de n/2 votants ont un pic ≥ médiane,
  et par pic-unique ils préfèrent la médiane à y
- Pour tout y > médiane : strictement plus de n/2 votants ont un pic ≤ médiane,
  et par pic-unique ils préfèrent la médiane à y
-/

/-- Liste triée des pics (avec doublons préservés) -/
noncomputable def sorted_peaks_list (peaks : ι → σ) : List σ :=
  (Finset.univ.toList.map peaks).mergeSort (· ≤ ·)

/-- Le pic médian : l'élément du milieu des pics triés.
    Pour n impair, c'est l'unique élément du milieu. -/
noncomputable def median_peak [Inhabited σ] (peaks : ι → σ) : σ :=
  let s := sorted_peaks_list peaks
  s.getD (s.length / 2) default

/-- **Théorème du votant médian — version hypothèses strictes (Black 1948)** :
    Pour un nombre impair de votants avec préférences à pic unique ET
    monotonie stricte explicite de chaque côté du pic, le pic médian est
    un gagnant de Condorcet.

    C'est le lemme de travail ; `median_voter_theorem` ci-dessous emballe
    les hypothèses de monotonie stricte dans le prédicat
    `strictly_single_peaked_profile`. Les deux théorèmes sont équivalents
    après dépliage. -/
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

/-- **Théorème du votant médian (Black 1948)** : pour un nombre impair de votants avec
    des préférences à pic unique **strictes**, le pic médian est un gagnant de Condorcet.

    Note (Issue #973) : l'hypothèse a été renforcée de `single_peaked_profile`
    à `strictly_single_peaked_profile`. Le `single_peaked` plus faible autorise
    l'indifférence entre alternatives distinctes du même côté du pic,
    ce qui est incompatible avec la conclusion de gagnant de Condorcet *strict*
    via `margin_pos`. Sous `strictly_single_peaked_profile`, les votants ne peuvent plus
    être indifférents entre alternatives distinctes du même côté de leur pic,
    produisant des marges positives comme requis. Cela délègue à
    `median_voter_theorem_strict` après extraction des composantes de monotonicité stricte. -/
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

/-! ## Robustesse stratégique sous préférences à pic unique -/

/-- Une règle de vote f est robuste aux manipulations sur un ensemble S si aucun votant
    ne peut changer le résultat en un qu'il préfère strictement en déclarant mensongèrement ses préférences.
    Énoncé ici sans Function.update pour éviter DecidableEq ι :
    pour tout profil sincère prof et profil déviant prof' qui coïncide
    avec prof partout sauf peut-être en i, le résultat déviant n'est pas
    strictement préféré (sous les préférences vraies) au résultat sincère. -/
def strategy_proof_scc (f : SCC ι σ) (S : Finset σ) : Prop :=
  ∀ prof prof' i,
    (∀ j, j ≠ i → prof' j = prof j) →
    ¬ ∃ x y, x ∈ f prof' S ∧ y ∈ f prof S ∧ P (prof i).rel x y

/-- Sous préférences strictement à pic unique, aucun votant ne peut strictement préférer
    le pic médian à son propre pic. C'est l'intuition centrale derrière
    la robustesse stratégique de la règle du médian : le pic est l'unique élément
    maximal de l'ordre de préférence, donc rien (y compris la médiane)
    ne peut lui être strictement préféré.

    Ce lemme n'exige PAS un nombre impair de votants — il porte purement
    sur la structure des préférences. -/
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

/-- Un cycle dans une relation R sur une liste : le dernier élément est lié au premier,
    formant une chaîne. -/
def cycle {X : Type*} (R : X → X → Prop) (c : List X) : Prop :=
  ∃ h : c ≠ [], List.IsChain R (c.getLast h :: c)

/-- Une relation est acyclique si aucun cycle n'existe. -/
def acyclic {X : Type*} (R : X → X → Prop) : Prop :=
  ∀ c : List X, ¬ cycle R c

/-- Défaite en Split Cycle : x vainc y si
    1. x bat y à majorité stricte (marge positive), ET
    2. Il n'existe aucun cycle passant par x et y où chaque marge est ≥ marge(x,y).
    Cela résout les cycles de Condorcet en n'acceptant que les défaites qui ne sont pas
    « verrouillées » par un cycle plus fort. -/
noncomputable def split_cycle_defeats (prof : ι → PrefOrder σ) (x y : σ) : Prop :=
  margin_pos prof x y ∧
    ¬ ∃ c : List σ, x ∈ c ∧ y ∈ c ∧
      cycle (fun a b => (margin prof x y : Int) ≤ margin prof a b) c

/-- Règle Split Cycle : sélectionner toutes les alternatives qui ne sont vaincues par aucune autre.
    Équivalent : x gagne ssi aucun y ne vainc x via split-cycle. -/
noncomputable def split_cycle_scc : SCC ι σ := fun prof S => by
  classical
  exact S.filter (fun x => ∀ y ∈ S, ¬ split_cycle_defeats prof y x)

/-- Split Cycle est cohérent avec Condorcet :
    si x est un gagnant de Condorcet, x n'est vaincu par aucun cycle de split. -/
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

/-- Longueur de cycle positive. -/
theorem cycle_length_pos {X : Type*} {R : X → X → Prop} {c : List X} (hc : cycle R c) :
    0 < c.length := by
  rcases hc with ⟨h, _⟩
  exact List.length_pos_of_ne_nil h

/-- Ajout d'un élément à une chaîne : si le dernier élément de la chaîne est lié à x,
    on peut étendre la chaîne avec x. Utilise la récursion structurelle via match. -/
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

/-- La rotation d'un cycle préserve la propriété de cycle.
    Pour `a :: l`, le cycle `IsChain R (getLast (a::l) :: a :: l)` est tourné en
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

/-- À partir d'une chaîne `IsChain R (a :: l)`, la tête est liée à tout membre de l.
    Utilise pairwise : `Pairwise R (a :: l)` signifie que la tête est liée à tout l. -/
private theorem chain_head_rel_mem {α : Type*} {R : α → α → Prop} [Trans R R R]
    {a : α} {l : List α} (hchain : List.IsChain R (a :: l))
    {x : α} (hmem : x ∈ l) : R a x := by
  have hp := hchain.pairwise
  rw [List.pairwise_cons] at hp
  exact hp.1 x hmem

set_option linter.unusedSectionVars false in
/-- Les cycles sont impossibles sur les ordres stricts linéaires.
    Un cycle `getLast c :: c` sous `<` signifie que le dernier élément est lié à lui-même
    via la chaîne, contredisant l'irréflexivité de `<`. -/
theorem lt_acyclic [LinearOrder σ] : acyclic (fun (x y : σ) => x < y) := by
  intro c hc
  rcases hc with ⟨hne, hchain⟩
  have hmem : c.getLast hne ∈ c := List.getLast_mem hne
  have hlt : c.getLast hne < c.getLast hne :=
    chain_head_rel_mem hchain hmem
  exact lt_irrefl _ hlt

end SplitCycle

/-! ## Ensembles clones et indépendance

Un ensemble de candidats X forme un ensemble clone si chaque votant classe tous les membres de X
dans un bloc contigu (soit tous au-dessus, soit tous en dessous de tout candidat hors de X).
Ceci est pertinent pour les règles de vote clone-indépendantes (p. ex. Schulze, Split Cycle).

Référence : DominikPeters/SocialChoiceLean `SocialChoice.Axioms.Clones`
-/

section Clones

variable [DecidableEq σ] [Fintype σ]

/-- Un ensemble clone X dans le profil prof : chaque votant classe X en bloc contigu. -/
def clone_set (prof : ι → PrefOrder σ) (X : Finset σ) : Prop :=
  X.Nonempty ∧ ∀ (v : ι) (c : σ), c ∉ X →
    (∀ x ∈ X, P (prof v).rel x c) ∨ (∀ x ∈ X, P (prof v).rel c x)

/-- Indépendance aux clones : remplacer tous les clones par un seul représentant
    ne change pas le classement relatif des candidats non clones. -/
def clone_independence (f : SCC ι σ) : Prop :=
  ∀ prof X x, clone_set prof X → x ∈ X →
    f prof (Finset.univ \ (X.erase x)) =
      ((f prof Finset.univ).image (fun y => if y ∈ X then x else y)).filter
        (fun y => y ∈ Finset.univ \ (X.erase x))

/-- Une SCC est clone-indépendante si elle satisfait l'indépendance aux clones pour tous les profils. -/
theorem clone_set_nonempty {prof : ι → PrefOrder σ} {X : Finset σ}
    (hc : clone_set prof X) : X.Nonempty := hc.1

end Clones

/-! ## Ensemble de Banks

L'ensemble de Banks (Banks 1985) est un concept de solution par tournoi. Étant donné un
tournoi majoritaire (issu des marges par paires), un gagnant de Banks est une alternative qui
domine un sous-tournoi transitif maximal (c.-à-d. une chaîne maximale).

Référence : Banks, "Sophisticated Voting Outcomes and Agenda Control" (1985)
-/

section BanksSet

/-- Un profil induit un tournoi sur S : toute paire distincte a un gagnant majoritaire strict.
    Cela signifie pour tous x ≠ y dans S, exactement l'un de margin(x,y) > 0 ou margin(y,x) > 0 tient. -/
def is_tournament (prof : ι → PrefOrder σ) (S : Finset σ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → margin_pos prof x y ∨ margin_pos prof y x

/-- Une chaîne de Banks : un sous-ensemble de S totalement ordonné par la relation majoritaire,
    et maximal (ajouter tout élément de S brise la transitivité). -/
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

/-- x est un gagnant de Banks : c'est l'élément maximal d'une certaine chaîne de Banks.
    Être maximal signifie qu'aucun élément de la chaîne n'a une marge positive sur x. -/
def banks_winner (prof : ι → PrefOrder σ) (S : Finset σ) (x : σ) : Prop :=
  x ∈ S ∧ ∃ C : Finset σ, banks_chain prof S C ∧ x ∈ C ∧
    ∀ y ∈ C, y ≠ x → margin_pos prof x y

/-- L'ensemble de Banks : tous les gagnants de Banks dans S -/
noncomputable def banks_set (prof : ι → PrefOrder σ) (S : Finset σ) : Finset σ := by
  classical
  exact S.filter (fun x => banks_winner prof S x)

/-- L'ensemble de Banks est un sous-ensemble de S -/
theorem banks_set_subset (prof : ι → PrefOrder σ) (S : Finset σ) :
    banks_set prof S ⊆ S := by
  classical
  unfold banks_set
  exact Finset.filter_subset _ _

/-- Un gagnant de Condorcet est toujours dans l'ensemble de Banks -/
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

/-! ## Vote unique transférable (STV)

Le STV est un système de vote préférentiel où les votants classent les candidats, et les candidats
sont élus en atteignant un quota. Les votes excédentaires sont transférés aux préférences suivantes, et
le candidat ayant le moins de voix est éliminé si personne n'atteint le quota.

Propriétés clés :
- Satisfait la proportionnalité
- Échoue à la monotonicité (Doron 1979)
- Échoue à l'indépendance aux clones en général
-/

section STV

variable [DecidableEq σ] [Fintype σ]

/-- Quota de Droop : nombre minimal de voix pour garantir l'élection.
    Pour n votants et k sièges : floor(n / (k+1)) + 1 -/
def droop_quota (n_voters : ℕ) (n_seats : ℕ) : ℕ :=
  n_voters / (n_seats + 1) + 1

/-- Compte les votes de première préférence pour x parmi les candidats restants.
    La première préférence d'un votant est son alternative la mieux classée dans l'ensemble restant. -/
noncomputable def first_preferences (prof : ι → PrefOrder σ) (remaining : Finset σ) (x : σ) : ℕ :=
  haveI : DecidablePred (fun i : ι => is_best_element x remaining (prof i).rel) := Classical.decPred _
  (Finset.filter (fun i => is_best_element x remaining (prof i).rel) Finset.univ).card

/-- Résultat d'un tour STV -/
inductive stv_round_result (σ : Type*) where
  | elected (x : σ) : stv_round_result σ
  | eliminated (x : σ) : stv_round_result σ
  | complete : stv_round_result σ

/-- Une étape du STV : élire un candidat atteignant le quota, ou éliminer le plus faible.
    Renvoie l'action à effectuer pour ce tour.
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

/-- STV en tant que correspondance de choix social avec n_seats gagnants.
    Applique itérativement stv_step jusqu'à ce que n_seats candidats soient élus. -/
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

