/-
  Gibbard-Satterthwaite : témoins d'hypothèses (T5, #26945)
  =======================================================

  Le théorème de Gibbard-Satterthwaite (1973) : toute règle de choix social
  résolue, sur un domaine d'au moins trois issues, qui est **surjective** et
  **non manipulable**, est **dictatoriale**. Le texte critiqué (#26945, l.109)
  invoque ce théorème contre un « juge qui choisit de façon répétable et
  mécanique » sans énoncer ses hypothèses. Chacune est indispensable :

  * la **surjectivité** (toute issue est atteinte par un certain profil) ;
  * le **domaine universel** (toute préférence ordinale est un bulletin admis).

  Ce module ne re-prove PAS le théorème (il est cité) : il en prouve les
  **témoins** — que la tranche T5 de #26945 demande comme théorèmes :

  1. `constantSCF` : la règle constante est non manipulable, NON surjective,
     non dictatoriale. Elle tue l'hypothèse de surjectivité.
  2. `medianReportRule` : la médiane des bulletins-pic est non manipulable
     (théorème de Moulin) et non dictatoriale, mais son domaine n'est PAS
     universel — la non-manipulabilité n'est prouvée que pour des préférences
     VRAIES unimodales. Elle tue l'hypothèse de domaine universel.

  Chaque témoin montre l'hypothèse dont le théorème a besoin. La lecture
  finale (section prose) en tire la conclusion pour le « juge » du texte.

  Stratégie de preuve : les comptages réutilisent les organes de
  `SocialChoice.SortedListCounting` (bornes `countP_lt_kth_le_half`,
  `countP_le_kth_ge_half_succ`, `countP_ge_kth_ge_half_succ`) et le pont
  filtre ↔ liste triée `finset_filter_lt_card_eq_toList_map_countP`,
  déjà consommés par `Voting.median_voter_theorem_strict`. La médiane est
  caractérisée par ses comptages (`sorted_get_of_counts`), puis la
  monotonie de la médiane en chaque bulletin (`median_peak_le_of_le`,
  `median_peak_ge_of_ge`) donne le théorème de Moulin par trichotomie.
-/

import SocialChoice.Basic
import SocialChoice.Voting
import SocialChoice.SortedListCounting

/-! ## Le cadre : règle de choix social résolue (SCF) -/

namespace SocialChoice

section Framework

variable {ι σ : Type*}

/-- Règle de choix social résolue (*social choice function*) : un profil
complet de préférences ordinales détermine une issue unique. C'est l'objet
du théorème de Gibbard-Satterthwaite. -/
def SCF := (ι → PrefOrder σ) → σ

/-- `f` est **surjective** : toute issue est le résultat d'un certain profil.
C'est l'hypothèse d'« onto » de Gibbard-Satterthwaite (qui exige aussi au
moins trois issues — c'est une condition sur `σ`, pas sur `f`). -/
def scf_onto (f : @SCF ι σ) : Prop :=
  ∀ a : σ, ∃ prof : ι → PrefOrder σ, f prof = a

/-- `f` est **non manipulable** (*strategy-proof*) : aucun électeur ne peut,
en changeant son seul bulletin, obtenir une issue strictement préférée —
strictement préférée selon ses VRAIES préférences, celles du profil de
départ, pas celles du bulletin déclaré. -/
def scf_strategy_proof (f : @SCF ι σ) : Prop :=
  ∀ (prof prof' : ι → PrefOrder σ) (i : ι), (∀ j, j ≠ i → prof' j = prof j) →
    ¬ P (prof i).rel (f prof') (f prof)

variable [LinearOrder σ]

/-- `d` est un **dictateur** pour `f` : le résultat est toujours le pic des
préférences de `d`. -/
def scf_dictator (f : @SCF ι σ) (d : ι) : Prop :=
  ∀ prof : ι → PrefOrder σ, is_peak (prof d).rel (f prof)

/-- `f` est **dictatoriale** : un dictateur existe. C'est la conclusion
(indésirable) de Gibbard-Satterthwaite. -/
def scf_dictatorial (f : @SCF ι σ) : Prop :=
  ∃ d : ι, scf_dictator f d

end Framework

/-! ## Témoin A — la règle constante (tue la surjectivité)

  La règle constante `constantSCF a` retourne toujours `a`. Elle est
  trivialement non manipulable (le résultat ne dépend d'aucun bulletin) et
  non dictatoriale (aucun bulletin n'influe le résultat) — mais elle n'est
  pas surjective dès qu'il existe une autre issue que `a`. Gibbard-
  Satterthwaite ne s'applique pas : l'hypothèse d'onto est essentielle. -/

section ConstantWitness

variable {ι σ : Type*}

/-- Ordre totalement indifférent : toute paire d'issues est en relation.
Sert de profil témoin pour la non-dictature de la règle constante :
personne n'a de préférence stricte, donc personne ne peut être pic. -/
def indifferentOrder : PrefOrder σ where
  rel _ _ := True
  refl _ := True.intro
  total _ _ := Or.inl True.intro
  trans _ _ _ _ _ := True.intro

/-- **Témoin A (T5 #26945)** : la règle constante qui retourne toujours `a`. -/
def constantSCF (a : σ) : @SCF ι σ := fun _prof => a

/-- **Témoin A (T5 #26945)** : la règle constante est non manipulable — le
résultat ne dépend pas des bulletins, donc aucun mensonge ne le change ;
et une préférence stricte pour le résultat contre lui-même est impossible
(`P` est irréflexive dès que la relation est réflexive). -/
theorem constantSCF_strategy_proof (a : σ) :
    scf_strategy_proof (ι := ι) (constantSCF a) := by
  intro prof prof' i _hsame h
  exact h.2 ((prof i).refl a)

/-- **Témoin A (T5 #26945)** : la règle constante n'est PAS surjective dès
qu'il existe une seconde issue. C'est l'hypothèse que ce témoin isole :
sans surjectivité, non-manipulabilité et non-dictature sont triviales. -/
theorem constantSCF_not_onto (a b : σ) (h : a ≠ b) :
    ¬ scf_onto (ι := ι) (constantSCF a) := by
  intro honto
  obtain ⟨prof, hprof⟩ := honto b
  exact h hprof

variable [LinearOrder σ] [Nontrivial σ]

/-- **Témoin A (T5 #26945)** : la règle constante n'est PAS dictatoriale.
Sur le profil uniformément indifférent, aucune issue n'est le pic de
qui que ce soit : un dictateur devrait avoir `a` pour pic, or `a` n'est
le pic strict de personne dans l'ordre indifférent. -/
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

/-! ## Identification : la médiane par ses comptages

  Lemmes de comptage propres à ce module : caractérisation de l'élément
  d'indice `k` d'une liste triée par ses bornes de comptage (la réciproque
  des organes de `SortedListCounting`), puis spécialisation à la médiane. -/

section MedianCounting

variable {σ : Type*} [LinearOrder σ]

/-- **Identification (réciproque des bornes)** : dans une liste triée, si
au plus `k` éléments sont strictement sous `x` et au moins `k + 1` sont
inférieurs ou égaux, alors l'élément d'indice `k` EST `x`. C'est la
réciproque de `countP_lt_kth_le_half` + `countP_le_kth_ge_half_succ`. -/
theorem sorted_get_of_counts {l : List σ} (hsort : l.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : k < l.length) {x : σ}
    (hlt : l.countP (fun z => decide (z < x)) ≤ k)
    (hle : k + 1 ≤ l.countP (fun z => decide (z ≤ x))) :
    l[k] = x := by
  rcases lt_trichotomy (l[k]) x with h | h | h
  · -- cas l[k] < x : les k + 1 premiers éléments sont < x, contredit hlt
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
  · -- cas x < l[k] : aucun élément d'indice ≥ k n'est ≤ x, contredit hle
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

/-! ## Témoin B — la médiane des bulletins-pic (tue le domaine universel)

  Chaque électeur annonce une issue (son bulletin-pic) ; le résultat est
  la médiane des bulletins. Le théorème de Moulin (1980) : sur le domaine
  unimodal, cette règle est non manipulable. Et elle n'est pas dictatoriale.
  Mais la non-manipulabilité EXIGE le domaine : hors unimodalité, elle
  tombe (un électeur bipolaire peut tirer la médiane vers son camp). -/

section MedianRule

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder σ]

/-- Pont : le cardinal « bulletins strictement sous `x` » se lit comme
`countP` sur la liste des bulletins (avant tri, donc sans `mergeSort`). -/
private theorem filter_lt_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => p j < x) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (z < x)) := by
  rw [show (Finset.filter (fun j => p j < x) Finset.univ) =
      (Finset.filter (fun j => decide (p j < x) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (z < x))]

/-- Pont jumeau pour « bulletins inférieurs ou égaux à `x` ». -/
private theorem filter_le_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => p j ≤ x) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (z ≤ x)) := by
  rw [show (Finset.filter (fun j => p j ≤ x) Finset.univ) =
      (Finset.filter (fun j => decide (p j ≤ x) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (z ≤ x))]

/-- Pont « bulletins strictement sous `x` » ↔ `countP` sur la liste triée
(le tri préserve les comptages : `List.Perm.countP_eq`). -/
private theorem countP_sorted_lt (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (z < x)) =
      (Finset.filter (fun j => p j < x) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (z < x))]
  exact (filter_lt_card p x).symm

/-- Pont jumeau « ≤ x » sur la liste triée. -/
private theorem countP_sorted_le (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (z ≤ x)) =
      (Finset.filter (fun j => p j ≤ x) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (z ≤ x))]
  exact (filter_le_card p x).symm

/-- Pont « bulletins supérieurs ou égaux à `x` » (forme duale, pour la
monotonie descendante). -/
private theorem filter_ge_card (p : ι → σ) (x : σ) :
    (Finset.filter (fun j => x ≤ p j) Finset.univ).card =
      (Finset.univ.toList.map p).countP (fun z => decide (x ≤ z)) := by
  rw [show (Finset.filter (fun j => x ≤ p j) Finset.univ) =
      (Finset.filter (fun j => decide (x ≤ p j) = true) Finset.univ) from by simp,
    SortedListCounting.finset_filter_lt_card_eq_toList_map_countP p
      (fun z => decide (x ≤ z))]

/-- Pont jumeau « x ≤ z » sur la liste triée. -/
private theorem countP_sorted_ge (p : ι → σ) (x : σ) :
    (sorted_peaks_list p).countP (fun z => decide (x ≤ z)) =
      (Finset.filter (fun j => x ≤ p j) Finset.univ).card := by
  unfold sorted_peaks_list
  rw [(List.mergeSort_perm (Finset.univ.toList.map p) (fun a b => decide (a ≤ b))).countP_eq
      (fun z => decide (x ≤ z))]
  exact (filter_ge_card p x).symm

variable [Inhabited σ]

/-- Les comptages déterminent la médiane : si au plus `n / 2` bulletins sont
strictement sous `x` et au moins `n / 2 + 1` lui sont inférieurs ou égaux,
alors la médiane vaut `x` (identification + ponts + organes de comptage). -/
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

/-- Borne organique « moitié gauche » : au plus `n / 2` bulletins
strictement sous la médiane. -/
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

/-- Borne organique « moitié gauche élargie » : au moins `n / 2 + 1`
bulletins inférieurs ou égaux à la médiane. -/
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

/-- **Monotonie montante de la médiane** : si l'électeur `i` remplace son
bulletin `peaks i` par `v` plus grand (les autres inchangés), la médiane
ne descend pas.

Preuve par comptage : si elle descendait (`m' < m`), les `k + 1` bulletins
`≤ m'` seraient `< m` ; or les bulletins `< m` ne peuvent qu'augmenter quand
on remplace `peaks i` par `v ≥ peaks i` (le nouveau bulletin n'est `< m`
que si l'ancien l'était), et ils étaient au plus `k`. Contradiction. -/
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
  -- côté neuf : au moins k + 1 bulletins ≤ m'
  have hnew : l'.length / 2 + 1 ≤
      l'.countP (fun z => decide (z ≤ median_peak (Function.update peaks i v))) := by
    rw [hm'_eq]
    exact SortedListCounting.countP_le_kth_ge_half_succ hsorted' hn'
  have hnew_card : l'.countP (fun z => decide (z ≤ median_peak (Function.update peaks i v))) =
      (Finset.filter (fun j => Function.update peaks i v j ≤
        median_peak (Function.update peaks i v)) Finset.univ).card := by
    rw [hm'_eq]
    exact countP_sorted_le (Function.update peaks i v) _
  -- côté ancien : au plus k bulletins < m
  have hold : (Finset.filter (fun j => peaks j < median_peak peaks) Finset.univ).card ≤
      l.length / 2 := by
    rw [← countP_sorted_lt peaks (median_peak peaks)]
    have hmid : median_peak peaks = l[l.length / 2] := by
      unfold median_peak sorted_peaks_list
      show l.getD (l.length / 2) default = l[l.length / 2]
      simp [List.getD, hn]
    rw [hmid]
    exact SortedListCounting.countP_lt_kth_le_half hsorted hn
  -- inclusion 1 : ≤ m' entraîne < m (car m' < m)
  have hsub1 : (Finset.filter (fun j => Function.update peaks i v j ≤
        median_peak (Function.update peaks i v)) Finset.univ).card ≤
      (Finset.filter (fun j => Function.update peaks i v j < median_peak peaks)
        Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_le_of_lt hj hlt
  -- inclusion 2 : un bulletin dévié < m n'y était que si l'ancien y était (v ≥ peaks i)
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

/-- **Monotonie descendante de la médiane** : si l'électeur `i` remplace son
bulletin `peaks i` par `v` plus petit (les autres inchangés), la médiane
ne monte pas. Preuve par comptage, miroir de `median_peak_le_of_le` :
si elle montait (`m < m'`), les `n - k` bulletins `≥ m'` seraient `> m` ;
or les bulletins `> m` ne peuvent qu'augmenter quand on remplace `peaks i`
par `v ≤ peaks i`, et ils étaient au plus `n - k - 1` (complément de la
borne `k + 1 ≤ #{≤ m}`). Contradiction. -/
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
  -- côté neuf : au moins n - k bulletins ≥ m'
  have hnew : l'.length - l'.length / 2 ≤
      l'.countP (fun z => decide (median_peak (Function.update peaks i v) ≤ z)) := by
    rw [hm'_eq]
    exact SortedListCounting.countP_ge_kth_ge_half_succ hsorted' hn'
  have hnew_card : l'.countP (fun z => decide (median_peak (Function.update peaks i v) ≤ z)) =
      (Finset.filter (fun j => median_peak (Function.update peaks i v) ≤
        Function.update peaks i v j) Finset.univ).card :=
    countP_sorted_ge (Function.update peaks i v) (median_peak (Function.update peaks i v))
  -- complémentarité : {> m} et {≤ m} partitionnent l'électorat
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
  -- côté ancien : au moins k + 1 bulletins ≤ m
  have hold : l.length / 2 + 1 ≤
      (Finset.filter (fun j => peaks j ≤ median_peak peaks) Finset.univ).card := by
    rw [← countP_sorted_le peaks (median_peak peaks)]
    have hmid : median_peak peaks = l[l.length / 2] := by
      unfold median_peak sorted_peaks_list
      show l.getD (l.length / 2) default = l[l.length / 2]
      simp [List.getD, hn]
    rw [hmid]
    exact SortedListCounting.countP_le_kth_ge_half_succ hsorted hn
  -- inclusion 1 : ≥ m' entraîne > m (car m < m')
  have hsub1 : (Finset.filter (fun j => median_peak (Function.update peaks i v) ≤
        Function.update peaks i v j) Finset.univ).card ≤
      (Finset.filter (fun j => median_peak peaks <
        Function.update peaks i v j) Finset.univ).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_lt_of_le hlt hj
  -- inclusion 2 : un bulletin dévié > m n'y était que si l'ancien y était (v ≤ peaks i)
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

/-- **Témoin B (T5 #26945) : la règle de la médiane des bulletins-pic**
(règle de Black restreinte aux bulletins, théorème de Moulin). Chaque
électeur annonce une issue ; le résultat est la médiane (position `n / 2`
de la liste triée, médiane basse).

ATTENTION — le domaine n'est PAS universel : la non-manipulabilité n'est
garantie que lorsque les préférences VRAIES sont unimodales. C'est
l'hypothèse de domaine que Gibbard-Satterthwaite interdit d'omettre. -/
noncomputable def medianReportRule (reports : ι → σ) : σ :=
  median_peak reports

/-- **Témoin B (T5 #26945) — théorème de Moulin (1980)** : la règle de la
médiane est non manipulable sur le domaine unimodal. Un électeur dont les
vraies préférences sont unimodales de pic `reports i` (son bulletin sincère)
ne peut jamais obtenir strictement mieux en changeant son seul bulletin.

Esquisse : la médiane est monotone en chaque bulletin
(`median_peak_le_of_le`, `median_peak_ge_of_ge`). Si l'électeur dévie vers
le bas (`v ≤ reports i`), le résultat ne monte pas ; s'il descend
strictement alors le pic était au-dessus de la médiane et la monotonie à
gauche du pic donne `R m m'` — qui exclut la préférence stricte `P m' m`.
Cas symétrique vers le haut. Résultat inchangé : une préférence stricte
de soi contre soi est impossible (`P` irréflexive). -/
theorem medianReport_strategy_proof
    (reports : ι → σ) (i : ι) (v : σ) (prof : ι → PrefOrder σ)
    (hsp : single_peaked (prof i).rel (reports i)) :
    ¬ P (prof i).rel (medianReportRule (Function.update reports i v))
        (medianReportRule reports) := by
  classical
  by_cases hle : v ≤ reports i
  · -- mensonge plus bas (ou égal) : la médiane ne monte pas
    have hbr : medianReportRule (Function.update reports i v) ≤ medianReportRule reports :=
      median_peak_ge_of_ge hle
    rcases lt_or_eq_of_le hbr with hlt' | heq'
    · -- m' < m : alors le pic était ≥ m (sinon la médiane serait inchangée),
      -- et la monotonie à gauche du pic donne R m m', qui tue P m' m
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
    · -- résultat inchangé : P de soi contre soi impossible
      rw [heq']
      intro h
      exact h.2 ((prof i).refl _)
  · -- mensonge plus haut : la médiane ne descend pas
    have hlt : reports i < v := lt_of_not_ge hle
    have hbr : medianReportRule reports ≤ medianReportRule (Function.update reports i v) :=
      median_peak_le_of_le (le_of_lt hlt)
    rcases lt_or_eq_of_le hbr with hlt' | heq'
    · -- m < m' : alors le pic était ≤ m (sinon la médiane serait inchangée),
      -- et la monotonie à droite du pic donne R m m', qui tue P m' m
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
    · -- résultat inchangé : P de soi contre soi impossible
      rw [← heq']
      intro h
      exact h.2 ((prof i).refl _)

/-- **Témoin B (T5 #26945, suite) : la règle de la médiane n'est pas
dictatoriale.** Aucun électeur n'obtient systématiquement son propre
bulletin comme résultat : sur au moins deux électeurs et deux issues, le
profil « tous `a₁` sauf `d` qui déclare `a₀` » (avec `a₀ ≠ a₁`) a pour
médiane `a₁`, pas `a₀`. -/
theorem medianReport_not_dictator [Nontrivial σ]
    (hcard : 2 ≤ Fintype.card ι) :
    ¬ ∃ d : ι, ∀ reports : ι → σ, medianReportRule reports = reports d := by
  rintro ⟨d, hd⟩
  obtain ⟨a₀, a₁, hne⟩ := exists_pair_ne (α := σ)
  rcases lt_or_gt_of_ne hne with hlt01 | hgt01
  · -- cas a₀ < a₁ : tous à a₁ sauf d à a₀ ; la médiane est a₁
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
  · -- cas a₁ < a₀ : tous à a₀ sauf d à a₁ ; la médiane est a₀
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

/-! ## Lecture — que reste-t-il pour le « juge répétable et mécanique » ?

  Le texte critiqué (l.109) conclut du théorème de Gibbard-Satterthwaite
  qu'un « juge qui choisit de façon répétable et mécanique » serait
  manipulable ou dictatoriale. Les deux témoins ci-dessus montrent ce que
  le théorème EXIGE pour dire cela, et ce qu'un tel juge en satisfait :

  * **Surjectivité** : un juge mécanique qui rend des verdicts sur un
    vocabulaire d'au moins trois issues PEUT être surjectif — rien ne
    l'interdit mécaniquement. Mais la règle constante (`constantSCF`)
    montre qu'un juge parfaitement répétable, non manipulable et non
    dictatoriale existe dès qu'on abandonne la surjectivité : un juge qui
    rend toujours le même verdict est trivial à spécifier et à auditer.
    L'hypothèse d'onto n'est pas gratuite : elle dit que le juge est
    *sensible au dossier*.

  * **Domaine universel** : c'est l'hypothèse que le texte omet le plus
    gravement. La médiane (`medianReportRule`, théorème de Moulin) est
    non manipulable et non dictatoriale SUR UN DOMAINE UNIMODAL : quand
    les « préférences » du juge sur les dossiers sont structurellement
    contraintes (unimodalité : une issue idéale, dégradation régulière de
    part et d'autre), l'argument de manipulation s'effondre. Or un juge
    mécanique traite précisément un domaine RESTREINT et structuré : des
    dossiers soumis à un format, une grille, une procédure. Prétendre le
    domaine « universel » pour lui appliquer Gibbard-Satterthwaite, c'est
    supposer exactement ce qui est faux d'un juge réel.

  * **Non-dictature** : les deux témoins sont NON dictatoriaux
    (`constantSCF_not_dictator`, `medianReport_not_dictator`) — la
    conclusion redoutée n'est pas un résidu inévitable, elle est le prix
    des DEUX hypothèses prises ensemble.

  Conclusion de la tranche : l'argument du texte ne tombe pas « parce que
  Gibbard-Satterthwaite » — il tombe parce qu'aucune des deux hypothèses
  du théorème n'est établie pour le juge décrit, et que chacune est
  contredite par un témoin concret non manipulable et non dictatoriale. -/
