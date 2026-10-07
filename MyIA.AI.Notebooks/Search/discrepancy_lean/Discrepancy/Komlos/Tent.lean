/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
Adapted to `discrepancy_lean` (issue #17845, distillation Karingula–Lovett
arXiv:2609.20979) : toolchain v4.33.0, convention i18n #4980.

Le source Dahia original vit dans le dépôt `gdahia/Komlos` (toolchain v4.34.0,
Mathlib v4.34.0). L'adaptation ci-dessous vise v4.33.0 / Mathlib `db584cd6` :

- les tactiques `grind` intensives sont remplacées par `simp`/`omega`/`ring`
  classiques, plus conservatives sur v4.33.0 ;
- les preuves qui dépendent de lemmes absents en v4.33.0 sont réécrites
  avec les équivalents stables.

**Portée de ce commit** (tranche k3 complète du fichier `Tent.lean` de
l'oracle — `lake build SUCCESS` requis pour passer la gate du module racine —
convention anti-régression D, 0 `sorry`) :

Briques closes : `tent`, `tent_nonneg`, `tent_neg`, `tent_zero`,
`tent_eq_zero`, `tent_of_abs_le`, `support_tent_subset`, `tent_add_one`,
`card_Icc_neg`, `Icc_neg_add_one`, `sum_Icc_comp_tent_add_one`, `sum_tent`,
`sum_tent_sq`, `abs_tent_sub_le`, `step`, `abs_step_le_one`, `step_eq_zero`,
`sum_step_sq_le`, `tent_sub_tent_eq_sum_step`, `sum_tent_sub_sq_le_nat`,
`sum_tent_sub_sq_le`.

Le fichier porte désormais **l'intégralité** du `Komlos/Tent.lean` de Dahia :
les 13 preuves reportées en c.885 sont livrées ici, chacune adaptée du
`grind` v4.34 vers des tactiques disponibles au pin v4.33.0 / `db584cd6`
(détail par preuve dans la note d'adaptation en fin de fichier).

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett, briques k1..k5 »).
-/

import Discrepancy.Basic

/-!
# La fonction « tente » discrète

`Discrepancy.Komlos.tent M j = max (M - |j|) 0` est la tente de demi-largeur
`M` sur `ℤ`. Son carré, après normalisation, donne les poids
unidimensionnels utilisés par la grille `Komlos.Grid` dans la distillation
Karingula–Lovett (arXiv:2609.20979, sœur de #15944, EPIC #12823).

Ce fichier calcule `∑ j, tent M j ^ 2` et prouve
`∑ j ∈ s, (tent M j - tent M (j - m)) ^ 2 ≤ 2 * M * m ^ 2` — la borne `L²`
discrète qui porte le Lemme 4.1 (l'estimation de densité-tente par
Cauchy–Schwarz). Cette dernière s'obtient en exprimant un décalage comme
somme de différences de pas puis en appliquant Cauchy–Schwarz.
-/

namespace Discrepancy.Komlos

open Finset

/-- Tente discrète de demi-largeur `M`. -/
noncomputable def tent (M : ℕ) (j : ℤ) : ℝ := max ((M : ℝ) - |(j : ℝ)|) 0

/-- La tente est partout positive ou nulle. -/
lemma tent_nonneg (M : ℕ) (j : ℤ) : 0 ≤ tent M j := le_max_right _ _

@[simp] lemma tent_neg (M : ℕ) (j : ℤ) : tent M (-j) = tent M j := by
  simp [tent, abs_neg]

@[simp] lemma tent_zero (M : ℕ) : tent M 0 = M := by simp [tent]

/-- La tente s'annule hors de `[-M, M]`. -/
lemma tent_eq_zero {M : ℕ} {j : ℤ} (h : (M : ℤ) ≤ |j|) : tent M j = 0 := by
  rw [tent, max_eq_right_iff, sub_nonpos]
  exact_mod_cast h

/-- Sur le support `[-M, M]`, la tente est en mode « linéaire ». -/
lemma tent_of_abs_le {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent M j = (M : ℝ) - |(j : ℝ)| := by
  rw [tent, max_eq_left_iff, sub_nonneg]
  exact_mod_cast h

/-- Le support de la tente est inclus dans `[-M, M]`. -/
lemma support_tent_subset (M : ℕ) :
    Function.support (tent M) ⊆ Set.Icc (-(M : ℤ)) (M : ℤ) := by
  intro j hj
  by_contra h
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with hj' | hj'
  · exact hj (tent_eq_zero
      ((by omega : (M : ℤ) ≤ -j).trans ((le_abs_self (-j : ℤ)).trans_eq (abs_neg j))))
  · exact hj (tent_eq_zero ((by omega : (M : ℤ) ≤ j).trans (le_abs_self j)))

/-- `tent_add_one` (lemme technique pour l'induction) : sur le support
`[-M, M]`, la tente de demi-largeur `M + 1` est la tente de demi-largeur `M`
plus `1`. -/
lemma tent_add_one {M : ℕ} {j : ℤ} (h : |j| ≤ (M : ℤ)) :
    tent (M + 1) j = tent M j + 1 := by
  rw [tent_of_abs_le h, tent_of_abs_le (by omega)]
  push_cast
  ring

/-- `Icc (-M) M` contient exactement `2·M + 1` éléments. -/
lemma card_Icc_neg (M : ℕ) : #(Icc (-(M : ℤ)) M) = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega

/-- `Icc (-(M+1)) (M+1)` est `Icc (-M) M` plus les deux extrémités. -/
lemma Icc_neg_add_one (M : ℕ) :
    Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ)
      = insert (-((M + 1 : ℕ) : ℤ)) (insert ((M + 1 : ℕ) : ℤ) (Icc (-(M : ℤ)) (M : ℤ))) := by
  ext j
  simp only [mem_Icc, mem_insert]
  omega

/-- Passer de la demi-largeur `M` à `M + 1` relève la tente de `1` sur
`[-M, M]` et ajoute deux points de valeur nulle. -/
lemma sum_Icc_comp_tent_add_one (M : ℕ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ j ∈ Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ), f (tent (M + 1) j)
      = ∑ j ∈ Icc (-(M : ℤ)) (M : ℤ), f (tent M j + 1) := by
  have h1 : (-((M + 1 : ℕ) : ℤ)) ∉ insert ((M + 1 : ℕ) : ℤ) (Icc (-(M : ℤ)) (M : ℤ)) := by
    intro h
    rcases mem_insert.1 h with h' | h'
    · omega
    · simp only [mem_Icc] at h'
      omega
  have h2 : ((M + 1 : ℕ) : ℤ) ∉ Icc (-(M : ℤ)) (M : ℤ) := by
    intro h
    simp only [mem_Icc] at h
    omega
  have e1 : tent (M + 1) (-((M + 1 : ℕ) : ℤ)) = 0 :=
    tent_eq_zero (by rw [abs_neg]; exact le_abs_self _)
  have e2 : tent (M + 1) ((M + 1 : ℕ) : ℤ) = 0 := tent_eq_zero (le_abs_self _)
  rw [Icc_neg_add_one, sum_insert h1, sum_insert h2, e1, e2, hf]
  simp only [zero_add]
  refine sum_congr rfl ?_
  intro j hj
  simp only [mem_Icc] at hj
  rw [tent_add_one (abs_le.2 ⟨hj.1, hj.2⟩)]

/-- Somme close : la tente sur son support somme à `M ^ 2`. -/
lemma sum_tent (M : ℕ) : ∑ j ∈ Icc (-(M : ℤ)) M, tent M j = (M : ℝ) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h := sum_Icc_comp_tent_add_one M id (rfl : (id : ℝ → ℝ) 0 = 0)
    simp only [id] at h
    rw [h]
    simp only [sum_add_distrib, ih, sum_const, card_Icc_neg, nsmul_eq_mul]
    push_cast
    ring

/-- Somme close : la somme des carrés de la tente vaut `M * (2 * M ^ 2 + 1) / 3`
(écrite ici multipliée par `3` pour rester sans division). -/
lemma sum_tent_sq (M : ℕ) :
    (∑ j ∈ Icc (-(M : ℤ)) M, tent M j ^ 2) * 3 = (M : ℝ) * (2 * (M : ℝ) ^ 2 + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [sum_Icc_comp_tent_add_one M (fun x => x ^ 2) (by norm_num)]
    simp only [add_sq, sum_add_distrib, ← sum_mul, ← mul_sum, sum_tent,
      sum_const, card_Icc_neg, nsmul_eq_mul]
    push_cast
    linarith [ih]

/-- La tente est `1`-Lipschitz. -/
lemma abs_tent_sub_le (M : ℕ) (j k : ℤ) :
    |tent M j - tent M k| ≤ |(j : ℝ) - (k : ℝ)| := by
  simp only [tent]
  refine (abs_max_sub_max_le_abs ((M : ℝ) - |(j : ℝ)|) ((M : ℝ) - |(k : ℝ)|) 0).trans ?_
  have e : ((M : ℝ) - |(j : ℝ)|) - ((M : ℝ) - |(k : ℝ)|) = |(k : ℝ)| - |(j : ℝ)| := by
    ring
  rw [e]
  exact (abs_abs_sub_abs_le_abs_sub (k : ℝ) (j : ℝ)).trans_eq (abs_sub_comm (k : ℝ) (j : ℝ))

/-- Différence de pas de la tente. -/
noncomputable def step (M : ℕ) (j : ℤ) : ℝ := tent M j - tent M (j - 1)

/-- Chaque pas de la tente est borné par `1` en valeur absolue. -/
lemma abs_step_le_one (M : ℕ) (j : ℤ) : |step M j| ≤ 1 := by
  have h := abs_tent_sub_le M j (j - 1)
  simp only [step] at h ⊢
  have e : ((j : ℝ) - ((j - 1 : ℤ) : ℝ)) = 1 := by
    push_cast
    ring
  rwa [e, abs_one] at h

/-- Le pas est nul hors de l'intervalle `[1 - M, M]`. -/
lemma step_eq_zero {M : ℕ} {j : ℤ} (h : j ∉ Icc (1 - (M : ℤ)) M) : step M j = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · have e1 : tent M j = 0 :=
      tent_eq_zero ((by omega : (M : ℤ) ≤ -j).trans ((le_abs_self (-j : ℤ)).trans_eq (abs_neg j)))
    have e2 : tent M (j - 1) = 0 :=
      tent_eq_zero ((by omega : (M : ℤ) ≤ -(j - 1)).trans
        ((le_abs_self (-(j - 1 : ℤ))).trans_eq (abs_neg (j - 1))))
    rw [step, e1, e2, sub_zero]
  · have e1 : tent M j = 0 :=
      tent_eq_zero ((by omega : (M : ℤ) ≤ j).trans (le_abs_self j))
    have e2 : tent M (j - 1) = 0 :=
      tent_eq_zero ((by omega : (M : ℤ) ≤ j - 1).trans (le_abs_self (j - 1)))
    rw [step, e1, e2, sub_zero]

/-- Les pas de la tente sont bornés par `1` et supportés sur `2·M` points. -/
lemma sum_step_sq_le (M : ℕ) (s : Finset ℤ) : ∑ j ∈ s, step M j ^ 2 ≤ 2 * M := by
  rw [← sum_subset (s₁ := s ∩ Icc (1 - (M : ℤ)) M) inter_subset_left ?_]
  · refine (sum_le_card_nsmul _ _ 1 ?_).trans ?_
    · intro j _
      exact (sq_le_one_iff_abs_le_one _).2 (abs_step_le_one M j)
    · rw [nsmul_eq_mul, mul_one, ← Nat.cast_two, ← Nat.cast_mul, Nat.cast_le]
      refine (card_le_card inter_subset_right).trans_eq ?_
      rw [Int.card_Icc]
      omega
  · intro j hj hj'
    rw [mem_inter, and_iff_right hj] at hj'
    rw [step_eq_zero hj', zero_pow two_ne_zero]

/-- Un décalage de `k` pas s'exprime comme la somme des pas intermédiaires. -/
lemma tent_sub_tent_eq_sum_step (M k : ℕ) (j : ℤ) :
    tent M j - tent M (j - k) = ∑ i ∈ range k, step M (j - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, sum_range_succ]
    have hs : step M (j - k) = tent M (j - k) - tent M (j - (↑k + 1)) := by
      have e2 : (j - ↑k : ℤ) - 1 = j - (↑k + 1) := by omega
      simp only [step, e2]
    rw [← ih, hs]
    ring

/-- La distance `L²` au carré entre la tente et sa translatée par `k : ℕ`
est au plus `2·M·k ^ 2`. -/
lemma sum_tent_sub_sq_le_nat (M k : ℕ) (s : Finset ℤ) :
    ∑ j ∈ s, (tent M j - tent M (j - k)) ^ 2 ≤ 2 * M * (k : ℝ) ^ 2 := by
  simp_rw [tent_sub_tent_eq_sum_step]
  calc ∑ j ∈ s, (∑ i ∈ range k, step M (j - i)) ^ 2
      ≤ ∑ j ∈ s, (k : ℝ) * ∑ i ∈ range k, step M (j - i) ^ 2 := by
        gcongr with j
        simpa using sq_sum_le_card_mul_sum_sq (s := range k) (f := fun i ↦ step M (j - i))
    _ = (k : ℝ) * ∑ i ∈ range k, ∑ j ∈ s, step M (j - i) ^ 2 := by rw [← mul_sum, sum_comm]
    _ ≤ (k : ℝ) * ∑ i ∈ range k, (2 * M : ℝ) := by
        gcongr with i
        simpa using sum_step_sq_le M (s.map (Equiv.subRight ((i : ℤ))).toEmbedding)
    _ = 2 * M * (k : ℝ) ^ 2 := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring

/-- La distance `L²` au carré entre la tente et sa translatée par `m : ℤ`
est au plus `2·M·m ^ 2`. -/
lemma sum_tent_sub_sq_le (M : ℕ) (m : ℤ) (s : Finset ℤ) :
    ∑ j ∈ s, (tent M j - tent M (j - m)) ^ 2 ≤ 2 * M * (m : ℝ) ^ 2 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · simpa using sum_tent_sub_sq_le_nat M k s
  · convert sum_tent_sub_sq_le_nat M k (s.map (Equiv.addRight ((k : ℤ))).toEmbedding) using 1
    · rw [sum_map]
      congr with j
      simp [sub_sq_comm (tent M j)]
    · push_cast
      ring

/-! ## Note d'adaptation (tranche k3 complète)

**Statut** : 21 briques closes — l'intégralité du `Komlos/Tent.lean` de
Dahia est portée (`lake build Discrepancy.Komlos.Tent` SUCCESS sur les deux
jumeaux, 0 `sorry` en code).

**Portage `grind` → v4.33.0, preuve par preuve** :

- `support_tent_subset` : l'énoncé force **`Set.Icc`** (le `Icc` nu sous
  `open Finset` s'élabore en coercion `↑(Finset.Icc)`, dont le `mem_Icc`
  ne s'applique pas — mesuré au probe) ; le `grind` de l'oracle devient
  `by_contra` + `Set.mem_Icc`/`not_and_or`/`not_le`, chaque borne
  `M ≤ |j|` passant par
  `(by omega : M ≤ -j).trans ((le_abs_self _).trans_eq (abs_neg _))` —
  `omega` **ne splitte pas** `|j|` sur `ℤ` (atome opaque, mesuré).
- `Icc_neg_add_one`, `sum_Icc_comp_tent_add_one` : les bornes en **cast
  entier global** `((M + 1 : ℕ) : ℤ)` — `(M + 1 : ℤ)` se distribue en
  `↑M + 1` et ne matche jamais le `↑(M + 1)` produit par l'induction ;
  les gardes `sum_insert (by grind)` deviennent des `mem_insert.1` +
  `omega` explicites (`h1`, `h2`).
- `sum_tent` : le `rw` direct avec `f := id` échoue (le pattern
  `id (tent …)` n'existe pas dans le but) — normalisation par
  `have h := …; simp only [id] at h` avant le `rw` ; le `grind` final
  devient `push_cast` + `ring`.
- `sum_tent_sq` : le `grind` final de l'induction devient `push_cast` +
  `linarith [ih]` (les carrés y sont des atomes linéaires).
- `abs_tent_sub_le` : le `grind` devient l'inégalité triangulaire inverse
  pour `max` via `abs_max_sub_max_le_abs`, puis `abs_abs_sub_abs_le_abs_sub`
  + `abs_sub_comm` (les noms `abs_add` / `neg_le_abs_self` de Mathlib
  récent sont **absents au pin** — sondé par `lake env lean`).
- `step_eq_zero` : chaque borne `M ≤ |j|`, `M ≤ |j - 1|` passe par le même
  composite `le_abs_self` + `abs_neg` (même raison qu'en
  `support_tent_subset`).
- `tent_sub_tent_eq_sum_step` : `sum_range_sub'` (absent au pin) est
  remplacé par une induction sur `k` (`Nat.cast_add`/`Nat.cast_one` +
  `sum_range_succ`, identité d'indice par `omega`, puis `ring`).
- `sum_step_sq_le`, `sum_tent_sub_sq_le_nat`, `sum_tent_sub_sq_le` :
  repris de l'oracle quasi tels quels (`sum_subset`, `sum_le_card_nsmul`,
  `gcongr`, Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`, `Equiv.subRight` /
  `addRight`) — tous ces noms existent au pin `db584cd6`.

L'état détaillé vit dans `FORMAL_STATUS.md` (« Distillation
Karingula–Lovett »).
-/

end Discrepancy.Komlos
